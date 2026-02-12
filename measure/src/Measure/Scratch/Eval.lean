/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Scratch Mode runtime: core evaluator (evalExpr / evalStmt).
Reuses Measure.Dim.Dim, Measure.Error.Interval + UncertaintyModel,
Measure.Constants for physics constants.
-/
import Measure.Scratch.Env
import Measure.Scratch.Format
import Measure.Scratch.Decl
import Measure.Scratch.ParseStmt
import Measure.Constants
import Measure.External.Engine
import Measure.External.Compute
import Measure.External.Adapter
import Measure.External.Verify

namespace Measure.Scratch

open Measure.Dim
open Measure.Error
open Measure.Quantity
open Measure.External

/-- Result type for evaluation. -/
abbrev EvalResult := Except String (Env × Value)

/-- Result type for expression evaluation (no env change). -/
abbrev ExprResult := Except String Value

/-- Helper: make a QExp from an integer. -/
private def qe (n : Int) : QExp := QExp.mk' n 1

/-- Resolve a UnitExpr to a Dim using Measure.Dim.Dim. -/
partial def unitToDim : UnitExpr → Dim
  | .base name =>
    match name with
    | "m"  => { L := QExp.one }
    | "kg" => { M := QExp.one }
    | "s"  => { T := QExp.one }
    | "A"  => { I := QExp.one }
    | "K"  => { Θ := QExp.one }
    | "mol" => { N := QExp.one }
    | "cd" => { J := QExp.one }
    | "N"  => Force
    | "J"  => Energy
    | "W"  => Power
    | "Pa" => Pressure
    | "Hz" => { T := qe (-1) }
    | "C"  => Charge
    | "V"  => Voltage
    | "Ω" | "ohm" => Resistance
    | _ => Dim.dimensionless
  | .mul a b => Dim.mul (unitToDim a) (unitToDim b)
  | .div a b => Dim.div (unitToDim a) (unitToDim b)
  | .pow u n => Dim.pow (unitToDim u) (qe n)

/-- Extract a plain Float from a Value. -/
private def valueToFloat (v : Value) : Except String Float :=
  match v with
  | .number f => .ok f
  | .withUnit f _ _ => .ok f
  | .withUncertainty f _ _ _ => .ok f
  | .quantity f _ _ => .ok f
  | _ => .error s!"expected numeric value, got {v.format}"

/-- Get or create an Interval from a Value. -/
private def valueToInterval (v : Value) : Interval :=
  match v.getInterval? with
  | some iv => iv
  | none =>
    let f := v.toFloat?.getD 0.0
    UncertaintyModel.fromExact (α := Interval) f

/-- Check if a Value carries uncertainty. -/
private def hasUncertainty (v : Value) : Bool :=
  v.getInterval?.isSome

/-- Preserve unit info from operands. -/
private def pickUnit (a b : Value) : Option UnitExpr :=
  match a with
  | .withUnit _ u _ => some u
  | .withUncertainty _ _ u _ => u
  | _ => match b with
    | .withUnit _ u _ => some u
    | .withUncertainty _ _ u _ => u
    | _ => none

/-- Build a result Value from computed float, interval, unit, and dim. -/
private def mkResult (val : Float) (iv : Interval) (unit : Option UnitExpr)
    (dim : Dim) (uncertain : Bool) : Value :=
  if uncertain then .withUncertainty val iv unit dim
  else if dim.isDimensionless then .number val
  else .withUnit val (unit.getD (.base "?")) dim

/-- Add two values: dimension check + UncertaintyModel.add. -/
private def addValues (a b : Value) : Except String Value :=
  if !a.dimCompatible b then
    .error s!"dimension mismatch in addition: {Format.formatDim a.getDim} vs {Format.formatDim b.getDim}"
  else
    let va := a.toFloat?.getD 0.0
    let vb := b.toFloat?.getD 0.0
    let result := va + vb
    let dim := a.getDim
    let unc := hasUncertainty a || hasUncertainty b
    let iv := UncertaintyModel.add (α := Interval) (valueToInterval a) (valueToInterval b)
    .ok (mkResult result iv (pickUnit a b) dim unc)

/-- Subtract two values: dimension check + UncertaintyModel.sub. -/
private def subValues (a b : Value) : Except String Value :=
  if !a.dimCompatible b then
    .error s!"dimension mismatch in subtraction: {Format.formatDim a.getDim} vs {Format.formatDim b.getDim}"
  else
    let va := a.toFloat?.getD 0.0
    let vb := b.toFloat?.getD 0.0
    let result := va - vb
    let dim := a.getDim
    let unc := hasUncertainty a || hasUncertainty b
    let iv := UncertaintyModel.sub (α := Interval) (valueToInterval a) (valueToInterval b)
    .ok (mkResult result iv (pickUnit a b) dim unc)

/-- Multiply two values: dims multiply + UncertaintyModel.mul. -/
private def mulValues (a b : Value) : Except String Value :=
  let va := a.toFloat?.getD 0.0
  let vb := b.toFloat?.getD 0.0
  let result := va * vb
  let dim := Dim.mul a.getDim b.getDim
  let unc := hasUncertainty a || hasUncertainty b
  let iv := UncertaintyModel.mul (α := Interval) (valueToInterval a) (valueToInterval b) va vb
  .ok (mkResult result iv none dim unc)

/-- Divide two values: dims divide + UncertaintyModel.div. -/
private def divValues (a b : Value) : Except String Value :=
  let vb := b.toFloat?.getD 0.0
  if vb == 0.0 then .error "division by zero"
  else
    let va := a.toFloat?.getD 0.0
    let result := va / vb
    let dim := Dim.div a.getDim b.getDim
    let unc := hasUncertainty a || hasUncertainty b
    let iv := UncertaintyModel.div (α := Interval) (valueToInterval a) (valueToInterval b) va vb
    .ok (mkResult result iv none dim unc)

/-- Negate a value: UncertaintyModel.neg. -/
private def negValue : Value → Value
  | .number v => .number (-v)
  | .withUnit v u d => .withUnit (-v) u d
  | .withUncertainty v err u d =>
    .withUncertainty (-v) (UncertaintyModel.neg (α := Interval) err) u d
  | .quantity v d err =>
    .quantity (-v) d (err.map (UncertaintyModel.neg (α := Interval)))
  | v => v

/-- Power of a value: UncertaintyModel.pow. -/
private def powValues (base exp : Value) : Except String Value := do
  let vb ← valueToFloat base
  let ve ← valueToFloat exp
  let result := Float.pow vb ve
  let dim := Dim.pow base.getDim (qe (Int.ofNat ve.toUInt32.toNat))
  let unc := hasUncertainty base
  let iv := UncertaintyModel.pow (α := Interval) (valueToInterval base) vb ve
  .ok (mkResult result iv none dim unc)

/-- Absolute value. -/
private def absValue : Value → Except String Value
  | .number v => .ok (.number (Float.abs v))
  | .withUnit v u d => .ok (.withUnit (Float.abs v) u d)
  | .withUncertainty v err u d => .ok (.withUncertainty (Float.abs v) err u d)
  | .quantity v d err => .ok (.quantity (Float.abs v) d err)
  | v => .error s!"abs not supported for {v.format}"

/-- Apply a unary math function via UncertaintyModel.applyFunc. -/
private def applyUnaryFunc (arg : Value) (f f' : Float → Float)
    (dim : Dim) : Except String Value := do
  let v ← valueToFloat arg
  let result := f v
  if hasUncertainty arg then
    let iv := UncertaintyModel.applyFunc (α := Interval) (valueToInterval arg) v f f'
    .ok (.withUncertainty result iv none dim)
  else
    .ok (.number result)

/-- Evaluate a built-in unary function call using UncertaintyModel. -/
private def evalBuiltinUnary (fn : String) (arg : Value) : Except String Value := do
  let v ← valueToFloat arg
  match fn with
  | "sin" => applyUnaryFunc arg Float.sin Float.cos Dim.dimensionless
  | "cos" => applyUnaryFunc arg Float.cos (fun x => -Float.sin x) Dim.dimensionless
  | "tan" =>
    let c := Float.cos v
    if Float.abs c < 1e-15 then .error "tan: undefined (cos = 0)"
    else applyUnaryFunc arg Float.tan (fun x => 1.0 / (Float.cos x * Float.cos x)) Dim.dimensionless
  | "exp" => applyUnaryFunc arg Float.exp Float.exp Dim.dimensionless
  | "log" | "ln" =>
    if v <= 0.0 then .error s!"{fn}: argument must be positive"
    else applyUnaryFunc arg Float.log (fun x => 1.0 / x) Dim.dimensionless
  | "sqrt" =>
    if v < 0.0 then .error "sqrt: argument must be non-negative"
    else applyUnaryFunc arg Float.sqrt (fun x => 0.5 / Float.sqrt x) (Dim.sqrt arg.getDim)
  | "abs" => absValue arg
  | "asin" =>
    if v < -1.0 || v > 1.0 then .error "asin: argument out of range [-1, 1]"
    else .ok (.number (Float.asin v))
  | "acos" =>
    if v < -1.0 || v > 1.0 then .error "acos: argument out of range [-1, 1]"
    else .ok (.number (Float.acos v))
  | "atan" => .ok (.number (Float.atan v))
  | _ => .error s!"unknown function: {fn}"

/-- Dot product of two vectors. -/
private def dotProduct (a b : Array Value) : Except String Value := do
  if a.size != b.size then
    .error s!"dot: vectors must have same length ({a.size} vs {b.size})"
  else
    let mut sum : Value := .number 0.0
    for i in [:a.size] do
      let prod ← mulValues a[i]! b[i]!
      sum ← addValues sum prod
    .ok sum

/-- Cross product of two 3D vectors. -/
private def crossProduct (a b : Array Value) : Except String Value := do
  if a.size != 3 || b.size != 3 then
    .error "cross: requires 3D vectors"
  else
    let a0 ← valueToFloat a[0]!; let a1 ← valueToFloat a[1]!; let a2 ← valueToFloat a[2]!
    let b0 ← valueToFloat b[0]!; let b1 ← valueToFloat b[1]!; let b2 ← valueToFloat b[2]!
    .ok (.vector #[
      .number (a1 * b2 - a2 * b1),
      .number (a2 * b0 - a0 * b2),
      .number (a0 * b1 - a1 * b0)])

/-- Euclidean norm of a vector. -/
private def vectorNorm (elems : Array Value) : Except String Value := do
  let mut sumSq : Float := 0.0
  for e in elems do
    let v ← valueToFloat e
    sumSq := sumSq + v * v
  .ok (.number (Float.sqrt sumSq))

/-- Evaluate a comparison operation. -/
private def evalCmp (op : CmpOp) (a b : Value) : Except String Value := do
  let va ← valueToFloat a
  let vb ← valueToFloat b
  let result := match op with
    | .eq => va == vb
    | .neq => va != vb
    | .lt => va < vb
    | .gt => va > vb
    | .leq => va <= vb
    | .geq => va >= vb
    | .approx => Float.abs (va - vb) < 1e-9 * max (Float.abs va) (Float.abs vb)
    | .muchLt => va * 100.0 < vb
    | .muchGt => va > vb * 100.0
  .ok (.bool result)

/-- Evaluate a multi-argument built-in function call. -/
private def evalBuiltinMulti (fn : String) (args : Array Value) : Except String Value :=
  match fn, args.size with
  | "dot", 2 =>
    match args[0]!, args[1]! with
    | .vector a, .vector b => dotProduct a b
    | _, _ => .error "dot: requires two vector arguments"
  | "cross", 2 =>
    match args[0]!, args[1]! with
    | .vector a, .vector b => crossProduct a b
    | _, _ => .error "cross: requires two vector arguments"
  | "norm", 1 =>
    match args[0]! with
    | .vector elems => vectorNorm elems
    | v => do let f ← valueToFloat v; .ok (.number (Float.abs f))
  | "atan2", 2 => do
    let y ← valueToFloat args[0]!
    let x ← valueToFloat args[1]!
    .ok (.number (Float.atan2 y x))
  | "max", 2 => do
    let a ← valueToFloat args[0]!
    let b ← valueToFloat args[1]!
    .ok (.number (max a b))
  | "min", 2 => do
    let a ← valueToFloat args[0]!
    let b ← valueToFloat args[1]!
    .ok (.number (min a b))
  | _, _ => .error s!"unknown function or wrong arity: {fn}({args.size} args)"

/-- Evaluate an expression in the given environment. -/
partial def evalExpr (env : Env) : Expr → Except String Value
  | .number val _ => .ok (.number val)
  | .ident name _ =>
    match env.lookup name with
    | some v => .ok v
    | none => .error s!"undefined variable: {name}"
  | .greekIdent name _ =>
    match env.lookup name with
    | some v => .ok v
    | none => .error s!"undefined variable: {name}"
  | .add lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; addValues a b
  | .sub lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; subValues a b
  | .mul lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; mulValues a b
  | .div lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; divValues a b
  | .neg e => do let v ← evalExpr env e; .ok (negValue v)
  | .pow base exp => do
    let b ← evalExpr env base; let e ← evalExpr env exp; powValues b e
  | .abs e => do let v ← evalExpr env e; absValue v
  | .grouped e => evalExpr env e
  | .juxtapose lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; mulValues a b
  | .call fn args => evalCall env fn args
  | .pmLiteral value sigma unit => do
    let v ← evalExpr env value
    let s ← evalExpr env sigma
    let vf ← valueToFloat v
    let sf ← valueToFloat s
    let dim := match unit with
      | some u => unitToDim u
      | none => v.getDim
    let iv := UncertaintyModel.fromIndependent (α := Interval) vf sf
    .ok (.withUncertainty vf iv unit dim)
  | .withUnit value unit => do
    let v ← evalExpr env value
    let vf ← valueToFloat v
    let dim := unitToDim unit
    .ok (.withUnit vf unit dim)
  | .vector elems => do
    let vals ← elems.mapM (evalExpr env)
    .ok (.vector vals.toArray)
  | .matrix rows => do
    let vals ← rows.mapM fun row => do
      let r ← row.mapM (evalExpr env)
      pure r.toArray
    .ok (.matrix vals.toArray)
  | .cmp op lhs rhs => do
    let a ← evalExpr env lhs; let b ← evalExpr env rhs; evalCmp op a b
  | .ifExpr cond then_ elifs else_ => evalIf env cond then_ elifs else_
  | .forExpr var start stop step body => evalFor env var start stop step body
  | .lambda params body => .ok (.closure params body (env.flatten.toList))
  | .letExpr _name _ rhs => evalExpr env rhs

where
  /-- Evaluate a function call. -/
  evalCall (env : Env) (fn : String) (args : List Expr) : Except String Value := do
    let vals ← args.mapM (evalExpr env)
    let arr := vals.toArray
    if arr.size == 1 then
      match evalBuiltinUnary fn arr[0]! with
      | .ok v => return v
      | .error _ => pure ()
    match evalBuiltinMulti fn arr with
    | .ok v => return v
    | .error _ => pure ()
    match env.lookup fn with
    | some (.closure params body snap) =>
      if params.length != arr.size then
        .error s!"{fn}: expected {params.length} arguments, got {arr.size}"
      else
        -- Restore the captured closure environment, then bind parameters
        let fnEnv := (Env.fromSnapshot (Std.HashMap.ofList snap)).pushScope
        let bindings := params.zip vals |>.map fun (p, v) => (p.name, v)
        evalExpr (fnEnv.bindAll bindings) body
    | some _ => .error s!"{fn} is not a function"
    | none => .error s!"unknown function: {fn}"

  /-- Evaluate a block of expressions, returning the last value. -/
  evalExprBlock (env : Env) : List Expr → Except String Value
    | [] => .ok .unit
    | [e] => evalExpr env e
    | e :: rest => do let _ ← evalExpr env e; evalExprBlock env rest

  /-- Try each elif branch in order. -/
  tryElifs (env : Env) : List (Expr × List Expr) → Except String (Option Value)
    | [] => .ok none
    | (c, body) :: rest => do
      match ← evalExpr env c with
      | .bool true => do let v ← evalExprBlock env body; .ok (some v)
      | .bool false => tryElifs env rest
      | _ => .error "elif condition must be a boolean"

  /-- Evaluate an if/elif/else expression. -/
  evalIf (env : Env) (cond : Expr) (then_ : List Expr)
      (elifs : List (Expr × List Expr)) (else_ : Option (List Expr))
      : Except String Value := do
    match ← evalExpr env cond with
    | .bool true => evalExprBlock env then_
    | .bool false =>
      match ← tryElifs env elifs with
      | some v => .ok v
      | none => match else_ with
        | some body => evalExprBlock env body
        | none => .ok .unit
    | _ => .error "if condition must be a boolean"

  /-- Evaluate a for loop expression. -/
  evalFor (env : Env) (var : String) (start stop : Expr)
      (step : Option Expr) (body : List Expr) : Except String Value := do
    let sf ← valueToFloat (← evalExpr env start)
    let ef ← valueToFloat (← evalExpr env stop)
    let stf ← match step with
      | some s => valueToFloat (← evalExpr env s)
      | none => .ok 1.0
    if stf == 0.0 then .error "for loop: step cannot be zero"
    else
      let mut lastVal : Value := .unit
      let mut i := sf
      let goUp := stf > 0.0
      let mut fuel : Nat := 1000000
      while (if goUp then i <= ef else i >= ef) && fuel > 0 do
        let loopEnv := env.pushScope.bind var (.number i)
        lastVal ← evalExprBlock loopEnv body
        i := i + stf
        fuel := fuel - 1
      if fuel == 0 then .error "for loop: exceeded iteration limit"
      else .ok lastVal

/-- Evaluate a top-level statement, returning updated environment and output lines. -/
partial def evalStmt (env : Env) : Stmt → IO (Env × List String)
  | .letDecl name _ rhs => do
    match evalExpr env rhs with
    | .ok v => return (env.bind name v, [])
    | .error e => return (env, [s!"error in let {name}: {e}"])
  | .defDecl name params _ body => do
    let snap := env.flatten.toList
    match body with
    | [.exprStmt bodyExpr] =>
      return (env.bind name (.closure params bodyExpr snap), [])
    | _ =>
      let dummyExpr := Expr.number 0.0 { line := 0, column := 0, offset := 0 }
      return (env.bind name (.closure params dummyExpr snap), [s!"(def {name}: multi-stmt body stored)"])
  | .exprStmt e => do
    match evalExpr env e with
    | .ok .unit => return (env, [])
    | .ok v => return (env, [v.format])
    | .error e => return (env, [s!"error: {e}"])
  | .importStmt path => do
    return (env.addImport path, [s!"(imported {String.intercalate "." path})"])
  | .fromImport path names => do
    return (env.addImport path, [s!"(from {String.intercalate "." path} imported {String.intercalate ", " names})"])
  | .assertStmt cond msg => do
    match evalExpr env cond with
    | .ok (.bool true) => return (env, [])
    | .ok (.bool false) =>
      let m := msg.getD "assertion failed"
      return (env, [s!"ASSERTION FAILED: {m}"])
    | .ok _ => return (env, ["error: assert condition must be boolean"])
    | .error e => return (env, [s!"error in assert: {e}"])
  | .emitStmt name value => do
    match evalExpr env value with
    | .ok v => return (env, [s!"emit {name}: {v.format}"])
    | .error e => return (env, [s!"error in emit {name}: {e}"])
  | .compute name engine body rawBody => do
    let exprStr := match rawBody with
      | some s => s
      | none => match evalExpr env body with
        | .ok v => v.format
        | .error _ => s!"{repr body}"
    let kind := EngineKind.fromString engine
    let registry : AdapterRegistry := {}
    IO.println s!"[compute {name} via {engine}]: dispatching to external engine..."
    let result ← ComputeEngine.computeViaEngine kind exprStr registry
    match result with
    | .ok output =>
      let val := Value.number output.value
      let newEnv := env.bind name val
      let msg := s!"compute {name} = {val.format} (via {output.engineUsed}, {output.computeMs}ms)"
      return (newEnv, [msg])
    | .error (.engineNotInstalled k) =>
      IO.eprintln s!"[compute {name}]: engine '{k.toString}' not installed, falling back to local eval"
      match evalExpr env body with
      | .ok v =>
        let newEnv := env.bind name v
        return (newEnv, [s!"compute {name} = {v.format} (local fallback)"])
      | .error e => return (env, [s!"error in compute {name}: engine unavailable, local eval failed: {e}"])
    | .error (.adapterNotFound k) =>
      IO.eprintln s!"[compute {name}]: no adapter for '{k.toString}', falling back to local eval"
      match evalExpr env body with
      | .ok v =>
        let newEnv := env.bind name v
        return (newEnv, [s!"compute {name} = {v.format} (local fallback)"])
      | .error e => return (env, [s!"error in compute {name}: no adapter, local eval failed: {e}"])
    | .error err =>
      return (env, [s!"error in compute {name}: {repr err}"])
  | .simulation sim => evalSimulation env sim
  | .verify name clauses => evalVerify env name clauses
  | .attributed _ inner => evalStmt env inner
where
  /-- Evaluate a simulation block. -/
  evalSimulation (env : Env) (sim : SimulationNode) : IO (Env × List String) := do
    let mut simEnv := env.pushScope
    let mut output : List String := [s!"[simulation {sim.name}]"]
    for (name, rhs) in sim.initStmts do
      match evalExpr simEnv rhs with
      | .ok v => simEnv := simEnv.bind name v
      | .error e => output := output ++ [s!"  init error ({name}): {e}"]
    -- Evaluate loop range
    let startV := match evalExpr simEnv sim.loopRange.start with
      | .ok v => v.toFloat?.getD 0.0 | .error _ => 0.0
    let stopV := match evalExpr simEnv sim.loopRange.stop with
      | .ok v => v.toFloat?.getD 1.0 | .error _ => 1.0
    let stepV := match sim.loopRange.step with
      | some s => match evalExpr simEnv s with
        | .ok v => v.toFloat?.getD 1.0 | .error _ => 1.0
      | none => 1.0
    if stepV == 0.0 then
      return (env, output ++ ["  error: step cannot be zero"])
    -- Run simulation loop
    let mut t := startV
    let goUp := stepV > 0.0
    let mut fuel : Nat := 1000000
    while (if goUp then t <= stopV else t >= stopV) && fuel > 0 do
      simEnv := simEnv.bind sim.loopVar (.number t)
      for step in sim.loopBody do
        match step with
        | .primedUpdate var rhs =>
          match evalExpr simEnv rhs with
          | .ok v => simEnv := simEnv.bind var v
          | .error e => output := output ++ [s!"  step error ({var}'): {e}"]
        | .letBinding var rhs =>
          match evalExpr simEnv rhs with
          | .ok v => simEnv := simEnv.bind var v
          | .error e => output := output ++ [s!"  step error (let {var}): {e}"]
        | .funcCall fn args =>
          -- If the function name starts with "compute_via_", dispatch to engine
          if fn.startsWith "compute_via_" then
            let engineName := (fn.drop 12).toString  -- strip "compute_via_"
            let kind := EngineKind.fromString engineName
            let argStrs := args.filterMap (fun a =>
              match evalExpr simEnv a with
              | .ok v => some v.format
              | .error _ => none)
            let exprStr := String.intercalate ", " argStrs
            let registry : AdapterRegistry := {}
            let result ← ComputeEngine.computeViaEngine kind exprStr registry
            match result with
            | .ok cOutput =>
              output := output ++ [s!"  {fn}: {cOutput.value} (via {cOutput.engineUsed})"]
            | .error (.engineNotInstalled _) | .error (.adapterNotFound _) =>
              let vals := args.filterMap (fun a => (evalExpr simEnv a).toOption)
              output := output ++ [s!"  {fn}({vals.length} args): engine unavailable, skipped"]
            | .error err =>
              output := output ++ [s!"  {fn}: engine error - {repr err}"]
          else
            let vals := args.filterMap (fun a => (evalExpr simEnv a).toOption)
            output := output ++ [s!"  call {fn}({vals.length} args)"]
        | .assertStep cond msg =>
          match evalExpr simEnv cond with
          | .ok (.bool true) => pure ()
          | .ok (.bool false) =>
            let m := msg.getD "simulation assertion failed"
            output := output ++ [s!"  ASSERT FAILED at {sim.loopVar}={t}: {m}"]
          | _ => output := output ++ [s!"  assert error at {sim.loopVar}={t}"]
        | .emitStep name value =>
          match evalExpr simEnv value with
          | .ok v => output := output ++ [s!"  emit {name} at {sim.loopVar}={t}: {v.format}"]
          | .error e => output := output ++ [s!"  emit error ({name}): {e}"]
      t := t + stepV
      fuel := fuel - 1
    if fuel == 0 then
      output := output ++ ["  warning: simulation hit iteration limit"]
    output := output ++ [s!"[end simulation {sim.name}]"]
    return (env, output)

  /-- Evaluate a verify block.
      First evaluates clauses locally; for non-boolean or failed clauses,
      attempts symbolic verification via external CAS engine. -/
  evalVerify (env : Env) (name : String) (clauses : List VerifyClause)
      : IO (Env × List String) := do
    let mut output : List String := [s!"[verify {name}]"]
    let mut allPassed := true
    let registry : AdapterRegistry := {}
    for clause in clauses do
      match clause.expr with
      | some e =>
        match evalExpr env e with
        | .ok (.bool true) => output := output ++ [s!"  {clause.name}: PASS"]
        | .ok (.bool false) =>
          -- Local eval says false; try symbolic verification as second opinion
          let symResult ← VerifyEngine.verifyViaEngine .mathematica
            s!"{repr e}" registry
          match symResult with
          | .verified =>
            output := output ++ [s!"  {clause.name}: PASS (symbolic override)"]
          | .refuted ce =>
            let detail := match ce with
              | some c => s!" (counterexample: {c})"
              | none => ""
            output := output ++ [s!"  {clause.name}: FAIL{detail}"]
            allPassed := false
          | _ =>
            output := output ++ [s!"  {clause.name}: FAIL"]
            allPassed := false
        | .ok v =>
          -- Non-boolean result; try symbolic verification
          let symResult ← VerifyEngine.verifyViaEngine .mathematica
            s!"{v.format} == 0" registry
          match symResult with
          | .verified =>
            output := output ++ [s!"  {clause.name}: PASS (symbolic, {v.format} == 0)"]
          | _ =>
            output := output ++ [s!"  {clause.name}: {v.format} (non-boolean, unverified)"]
        | .error e =>
          output := output ++ [s!"  {clause.name}: ERROR - {e}"]
          allPassed := false
      | none => output := output ++ [s!"  {clause.name}: (no expression)"]
    let status := if allPassed then "ALL PASSED" else "SOME FAILED"
    output := output ++ [s!"[end verify {name}: {status}]"]
    return (env, output)

/-- Parse a single expression from a string. -/
private def parseOneExpr (input : String) : Except String Expr :=
  let tokens := Lexer.tokenize input
  let arr := tokens.toArray
  if arr.isEmpty then .error "empty input"
  else
    match Parser.parseExpr { tokens := arr } 0 with
    | .ok (_, expr) => .ok expr
    | .error e => .error e

/-- Parse a complete program from a string. -/
private def parseOneProgram (input : String) : Except String Program :=
  let tokens := Lexer.tokenize input
  let arr := tokens.toArray
  if arr.isEmpty then .error "empty input"
  else
    match Parser.parseProgram { tokens := arr } with
    | .ok (_, prog) => .ok prog
    | .error e => .error e

/-- Evaluate a single expression from a string (for REPL). -/
def evalScratch (env : Env) (input : String) : IO (Env × String) := do
  match parseOneExpr input with
  | .error e => return (env, s!"parse error: {e}")
  | .ok expr =>
    match evalExpr env expr with
    | .ok v => return (env, v.format)
    | .error e => return (env, s!"error: {e}")

/-- Evaluate a complete program. -/
def evalScratchProgram (env : Env) (input : String) : IO (Env × List String) := do
  match parseOneProgram input with
  | .error e => return (env, [s!"parse error: {e}"])
  | .ok prog =>
    let mut curEnv := env
    let mut allOutput : List String := []
    for stmt in prog.stmts do
      let (newEnv, output) ← evalStmt curEnv stmt
      curEnv := newEnv
      for line in output do
        IO.println line
      allOutput := allOutput ++ output
    return (curEnv, allOutput)

/-- Create a default environment with physics constants from Measure.Constants. -/
def defaultEnv : Env :=
  Env.empty
    |>.bind "pi" (.number 3.141592653589793)
    |>.bind "π" (.number 3.141592653589793)
    |>.bind "e" (.number 2.718281828459045)
    |>.bind "c" (.quantity Constants.c.value Velocity none)
    |>.bind "G" (.quantity Constants.G.value
        { L := qe 3, M := qe (-1), T := qe (-2) } none)
    |>.bind "h" (.quantity Constants.h.value
        { L := qe 2, M := QExp.one, T := qe (-1) } none)
    |>.bind "k_B" (.quantity Constants.k_B.value
        { L := qe 2, M := QExp.one, T := qe (-2), Θ := qe (-1) } none)
    |>.bind "N_A" (.quantity Constants.N_A.value
        { N := qe (-1) } none)
    |>.bind "m_e" (.quantity Constants.m_e.value { M := QExp.one } none)
    |>.bind "m_p" (.quantity Constants.m_p.value { M := QExp.one } none)
    |>.bind "α" (.quantity Constants.α.value Dim.dimensionless none)
    |>.bind "true" (.bool true)
    |>.bind "false" (.bool false)

end Measure.Scratch
