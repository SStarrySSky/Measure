/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Dimension inference algorithm.
Walks expression ASTs and infers/checks dimension annotations.
See docs/type-system.md Section 1.5.
-/
import Std
import Measure.Dim.Basic
import Measure.Dim.Unify

namespace Measure.Dim

/-- Dimension inference context: maps variable names to their dimensions. -/
abbrev DimEnv := Std.HashMap Lean.Name Dim

/-- Result of dimension inference on an expression. -/
inductive InferResult where
  | ok (dim : Dim) (subst : DimSubst)
  | error (msg : String)
  deriving Repr, Nonempty

/-- Dimension signature for a function. -/
structure DimSignature where
  /-- Dimension of each parameter -/
  params : Array DimTerm
  /-- Dimension of the return type -/
  ret : DimTerm
  /-- Generic dimension variables -/
  dimVars : Array DimVar
  deriving Repr, Inhabited

/-- Registry of known function dimension signatures. -/
abbrev SigRegistry := Std.HashMap Lean.Name DimSignature

-- ============================================================
-- Expression AST for dimension inference
-- ============================================================

/-- Simple expression AST that the dimension inference walks over.
    This is the Measure-level expression representation, not Lean's Expr. -/
inductive MExpr where
  | lit (v : Float)
  | natLit (n : Nat)
  | var (name : Lean.Name)
  | add (lhs rhs : MExpr)
  | sub (lhs rhs : MExpr)
  | mul (lhs rhs : MExpr)
  | div (lhs rhs : MExpr)
  | pow (base : MExpr) (exp : QExp)
  | app (fn : Lean.Name) (args : Array MExpr)
  | letBind (name : Lean.Name) (val body : MExpr)
  | ann (expr : MExpr) (dim : Dim)
  deriving Repr, Inhabited

-- ============================================================
-- Inference context
-- ============================================================

/-- Full context for dimension inference. -/
structure InferCtx where
  env : DimEnv := ∅
  sigs : SigRegistry := ∅
  subst : DimSubst := ∅
  nextVar : Nat := 0

instance : Nonempty InferCtx := ⟨{}⟩

/-- Generate a fresh dimension variable. -/
def InferCtx.freshVar (ctx : InferCtx) : DimVar × InferCtx :=
  (⟨ctx.nextVar⟩, { ctx with nextVar := ctx.nextVar + 1 })

/-- Extend the environment with a new binding. -/
def InferCtx.extend (ctx : InferCtx) (name : Lean.Name) (d : Dim) : InferCtx :=
  { ctx with env := ctx.env.insert name d }

/-- Update the substitution. -/
def InferCtx.withSubst (ctx : InferCtx) (σ : DimSubst) : InferCtx :=
  { ctx with subst := σ }

-- ============================================================
-- Core inference algorithm
-- ============================================================

/-- Internal inference result carrying the updated context. -/
inductive InferM where
  | ok (dim : Dim) (ctx : InferCtx)
  | error (msg : String)
  deriving Nonempty

/-- Require two dimensions to be equal (additive compatibility). -/
private def requireEqual (d1 d2 : Dim) (ctx : InferCtx) (op : String) : InferM :=
  let t1 := DimTerm.concrete d1
  let t2 := DimTerm.concrete d2
  match unify t1 t2 ctx.subst with
  | .success σ' => .ok d1 (ctx.withSubst σ')
  | .failure _ _ msg => .error s!"Dimension mismatch in {op}: {repr d1} vs {repr d2} -- {msg}"

/-- Instantiate a function signature with fresh variables, returning renamed params/ret. -/
private def instantiateSig (sig : DimSignature) (ctx : InferCtx)
    : Array DimTerm × DimTerm × InferCtx :=
  let init : Std.HashMap DimVar DimVar × InferCtx := (∅, ctx)
  let (mapping, ctx') := sig.dimVars.foldl (init := init) fun acc v =>
    let (m, c) := acc
    let (v', c') := c.freshVar
    (m.insert v v', c')
  let renameTerm (t : DimTerm) : DimTerm :=
    match t with
    | .var v => match mapping.get? v with
      | some v' => DimTerm.var v'
      | none => t
    | other => other
  let params' := sig.params.map renameTerm
  let ret' := renameTerm sig.ret
  (params', ret', ctx')

/-- Helper: fold over argument indices, inferring and unifying each. -/
private partial def inferArgs (args : Array MExpr) (params : Array DimTerm)
    (fn : Lean.Name) (idx : Nat) (ctx : InferCtx)
    (inferFn : MExpr → InferCtx → InferM) : InferM :=
  if h : idx < args.size then
    match inferFn args[idx] ctx with
    | .error msg => .error msg
    | .ok argDim ctx' =>
      if h2 : idx < params.size then
        let paramTerm := params[idx]
        let argTerm := DimTerm.concrete argDim
        match unify paramTerm argTerm ctx'.subst with
        | .failure _ _ msg =>
          .error s!"Dimension mismatch for arg {idx} of {fn}: {msg}"
        | .success σ' =>
          inferArgs args params fn (idx + 1) (ctx'.withSubst σ') inferFn
      else .error s!"Internal error: param index out of bounds for {fn}"
  else .ok Dim.dimensionless ctx  -- all args processed

/-- Infer the dimension of an expression. -/
partial def inferDim (e : MExpr) (ctx : InferCtx) : InferM :=
  match e with
  -- Literals are dimensionless
  | .lit _ => .ok Dim.dimensionless ctx
  | .natLit _ => .ok Dim.dimensionless ctx

  -- Variable lookup
  | .var name =>
    match ctx.env.get? name with
    | some d => .ok d ctx
    | none => .error s!"Unknown variable: {name}"

  -- Addition: both sides must have the same dimension
  | .add lhs rhs =>
    match inferDim lhs ctx with
    | .error msg => .error msg
    | .ok d1 ctx1 =>
      match inferDim rhs ctx1 with
      | .error msg => .error msg
      | .ok d2 ctx2 => requireEqual d1 d2 ctx2 "addition"

  -- Subtraction: both sides must have the same dimension
  | .sub lhs rhs =>
    match inferDim lhs ctx with
    | .error msg => .error msg
    | .ok d1 ctx1 =>
      match inferDim rhs ctx1 with
      | .error msg => .error msg
      | .ok d2 ctx2 => requireEqual d1 d2 ctx2 "subtraction"

  -- Multiplication: dimensions multiply
  | .mul lhs rhs =>
    match inferDim lhs ctx with
    | .error msg => .error msg
    | .ok d1 ctx1 =>
      match inferDim rhs ctx1 with
      | .error msg => .error msg
      | .ok d2 ctx2 => .ok (Dim.mul d1 d2) ctx2

  -- Division: dimensions divide
  | .div lhs rhs =>
    match inferDim lhs ctx with
    | .error msg => .error msg
    | .ok d1 ctx1 =>
      match inferDim rhs ctx1 with
      | .error msg => .error msg
      | .ok d2 ctx2 => .ok (Dim.div d1 d2) ctx2

  -- Power: dimension raised to rational exponent
  | .pow base exp =>
    match inferDim base ctx with
    | .error msg => .error msg
    | .ok d ctx1 => .ok (Dim.pow d exp) ctx1

  -- Function application: look up signature in registry
  | .app fn args =>
    match ctx.sigs.get? fn with
    | none => .error s!"No dimension signature registered for function: {fn}"
    | some sig =>
      if args.size != sig.params.size then
        .error s!"Arity mismatch for {fn}: expected {sig.params.size} args, got {args.size}"
      else
        let (params', ret', ctx0) := instantiateSig sig ctx
        match inferArgs args params' fn 0 ctx0 inferDim with
        | .error msg => .error msg
        | .ok _ ctxFinal =>
          match ret'.eval ctxFinal.subst with
          | some retDim => .ok retDim ctxFinal
          | none => .error s!"Cannot resolve return dimension for {fn}"

  -- Let binding: infer value dim, extend env, infer body
  | .letBind name val body =>
    match inferDim val ctx with
    | .error msg => .error msg
    | .ok valDim ctx1 =>
      let ctx2 := ctx1.extend name valDim
      inferDim body ctx2

  -- Annotation: infer and check against declared dimension
  | .ann expr dim =>
    match inferDim expr ctx with
    | .error msg => .error msg
    | .ok inferredDim ctx1 => requireEqual inferredDim dim ctx1 "annotation"

-- ============================================================
-- Public API
-- ============================================================

/-- Infer the dimension of an expression given an environment and signature registry.
    Returns `InferResult` with the inferred dimension and final substitution. -/
def infer (e : MExpr) (env : DimEnv := ∅) (sigs : SigRegistry := ∅) : InferResult :=
  let ctx : InferCtx := { env := env, sigs := sigs }
  match inferDim e ctx with
  | .ok dim ctx' => InferResult.ok dim ctx'.subst
  | .error msg => InferResult.error msg

/-- Register a function's dimension signature into a registry. -/
def registerSig (registry : SigRegistry) (name : Lean.Name)
    (params : Array DimTerm) (ret : DimTerm)
    (dimVars : Array DimVar := #[]) : SigRegistry :=
  registry.insert name { params := params, ret := ret, dimVars := dimVars }

-- ============================================================
-- Convenience constructors for common signatures
-- ============================================================

/-- Create a signature for a unary function: f(x : d) -> d' -/
def mkUnarySig (param ret : DimTerm) (vars : Array DimVar := #[]) : DimSignature :=
  { params := #[param], ret := ret, dimVars := vars }

/-- Create a signature for a binary function: f(x : d1, y : d2) -> d3 -/
def mkBinarySig (p1 p2 ret : DimTerm) (vars : Array DimVar := #[]) : DimSignature :=
  { params := #[p1, p2], ret := ret, dimVars := vars }

/-- Signature for dimensionless -> dimensionless functions (sin, cos, exp, log, etc.) -/
def dimlessSig : DimSignature :=
  mkUnarySig (.concrete Dim.dimensionless) (.concrete Dim.dimensionless)

/-- Create a standard math function registry with sin, cos, exp, log, etc. -/
def defaultSigRegistry : SigRegistry :=
  let r : SigRegistry := ∅
  let r := registerSig r `sin  #[.concrete Dim.dimensionless] (.concrete Dim.dimensionless)
  let r := registerSig r `cos  #[.concrete Dim.dimensionless] (.concrete Dim.dimensionless)
  let r := registerSig r `tan  #[.concrete Dim.dimensionless] (.concrete Dim.dimensionless)
  let r := registerSig r `exp  #[.concrete Dim.dimensionless] (.concrete Dim.dimensionless)
  let r := registerSig r `log  #[.concrete Dim.dimensionless] (.concrete Dim.dimensionless)
  let r := registerSig r `sqrt #[.var ⟨0⟩] (.pow (.var ⟨0⟩) (QExp.mk' 1 2)) #[⟨0⟩]
  let r := registerSig r `abs  #[.var ⟨0⟩] (.var ⟨0⟩) #[⟨0⟩]
  r

end Measure.Dim
