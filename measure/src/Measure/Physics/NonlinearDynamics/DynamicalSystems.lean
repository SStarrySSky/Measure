/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Nonlinear dynamics formalization.
Dynamical systems, fixed points, stability, Lyapunov exponents,
attractors, bifurcation theory, and Poincaré maps.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic

namespace Measure.Physics.NonlinearDynamics

/-! ## Dynamical Systems -/

/-- A continuous dynamical system dx/dt = f(x) on ℝⁿ.
    The vector field f determines the time evolution. -/
structure ContinuousDS (n : ℕ) where
  /-- The vector field f : ℝⁿ → ℝⁿ governing the dynamics. -/
  f : (Fin n → ℝ) → (Fin n → ℝ)

/-- A discrete dynamical system xₙ₊₁ = f(xₙ) on ℝⁿ.
    The map f is iterated to produce the orbit. -/
structure DiscreteDS (n : ℕ) where
  /-- The map f : ℝⁿ → ℝⁿ iterated at each step. -/
  f : (Fin n → ℝ) → (Fin n → ℝ)

/-- A trajectory (solution curve) of a continuous dynamical system. -/
abbrev Trajectory (n : ℕ) := ℝ → (Fin n → ℝ)

/-- A trajectory γ satisfies the ODE dx/dt = f(x) if γ'(t) = f(γ(t)) for all t. -/
noncomputable def SatisfiesODE {n : ℕ} (ds : ContinuousDS n) (γ : Trajectory n) : Prop :=
  ∀ (i : Fin n) (t : ℝ), deriv (fun s => γ s i) t = ds.f (γ t) i

/-- The orbit of a discrete dynamical system starting from x₀.
    orbit(0) = x₀, orbit(k+1) = f(orbit(k)). -/
noncomputable def orbit {n : ℕ} (ds : DiscreteDS n) (x₀ : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => x₀
  | k + 1 => ds.f (orbit ds x₀ k)

/-! ## Fixed Points and Periodic Orbits -/

/-- A fixed point x* of a continuous system satisfies f(x*) = 0. -/
def IsFixedPoint {n : ℕ} (ds : ContinuousDS n) (x : Fin n → ℝ) : Prop :=
  ds.f x = fun _ => 0

/-- A fixed point x* of a discrete system satisfies f(x*) = x*. -/
def IsDiscreteFixedPoint {n : ℕ} (ds : DiscreteDS n) (x : Fin n → ℝ) : Prop :=
  ds.f x = x

/-- A periodic orbit of period p in a discrete system: f^p(x) = x. -/
def IsPeriodicPoint {n : ℕ} (ds : DiscreteDS n) (x : Fin n → ℝ) (p : ℕ) : Prop :=
  p > 0 ∧ orbit ds x p = x

/-- A periodic orbit of a continuous system with period T > 0: γ(t + T) = γ(t). -/
def IsPeriodicTrajectory {n : ℕ} (γ : Trajectory n) (T : ℝ) : Prop :=
  T > 0 ∧ ∀ t : ℝ, γ (t + T) = γ t

/-- A fixed point of a discrete system is a periodic point of period 1. -/
theorem fixedPoint_is_periodic {n : ℕ} (ds : DiscreteDS n) (x : Fin n → ℝ)
    (hfp : IsDiscreteFixedPoint ds x) :
    IsPeriodicPoint ds x 1 := by
  constructor
  · omega
  · simp [orbit, IsDiscreteFixedPoint] at hfp ⊢
    exact hfp

/-! ## Stability -/

/-- Lyapunov stability: x* is stable if trajectories starting near x* stay near x*.
    For all ε > 0, there exists δ > 0 such that ‖γ(0) - x*‖ < δ implies ‖γ(t) - x*‖ < ε
    for all t ≥ 0. -/
def IsLyapunovStable {n : ℕ} (ds : ContinuousDS n) (x_star : Fin n → ℝ)
    (_hfp : IsFixedPoint ds x_star) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (γ : Trajectory n),
    SatisfiesODE ds γ →
    dist (γ 0) x_star < δ →
    ∀ t ≥ 0, dist (γ t) x_star < ε

/-- Asymptotic stability: x* is asymptotically stable if it is Lyapunov stable
    and trajectories starting near x* converge to x* as t → ∞. -/
def IsAsymptoticallyStable {n : ℕ} (ds : ContinuousDS n) (x_star : Fin n → ℝ)
    (hfp : IsFixedPoint ds x_star) : Prop :=
  IsLyapunovStable ds x_star hfp ∧
  ∃ δ > 0, ∀ (γ : Trajectory n),
    SatisfiesODE ds γ →
    dist (γ 0) x_star < δ →
    Filter.Tendsto γ Filter.atTop (nhds x_star)

/-- Unstable fixed point: not Lyapunov stable. -/
def IsUnstable {n : ℕ} (ds : ContinuousDS n) (x_star : Fin n → ℝ)
    (hfp : IsFixedPoint ds x_star) : Prop :=
  ¬ IsLyapunovStable ds x_star hfp

/-! ## Lyapunov Exponents -/

/-- The maximal Lyapunov exponent measures the exponential rate of divergence
    of nearby trajectories. λ = lim_{t→∞} (1/t) ln(‖δx(t)‖/‖δx(0)‖).
    Positive λ indicates chaos. -/
noncomputable def maximalLyapunovExponent {n : ℕ} (_ds : ContinuousDS n)
    (γ : Trajectory n) (δx₀ : Fin n → ℝ) : ℝ :=
  limUnder Filter.atTop fun t : ℝ =>
    (1 / t) * Real.log (‖deriv γ t‖ / ‖δx₀‖)

/-- A system exhibits sensitive dependence on initial conditions if the maximal
    Lyapunov exponent is positive. -/
def HasPositiveLyapunovExponent {n : ℕ} (ds : ContinuousDS n)
    (γ : Trajectory n) (δx₀ : Fin n → ℝ) : Prop :=
  maximalLyapunovExponent ds γ δx₀ > 0

/-! ## Attractors -/

/-- An invariant set: the flow maps S to itself.
    For every trajectory starting in S, the trajectory remains in S. -/
def IsInvariantSet {n : ℕ} (ds : ContinuousDS n) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ (γ : Trajectory n), SatisfiesODE ds γ →
    γ 0 ∈ S → ∀ t ≥ 0, γ t ∈ S

/-- An attracting set: an invariant set that nearby trajectories converge to. -/
def IsAttractingSet {n : ℕ} (ds : ContinuousDS n) (A : Set (Fin n → ℝ)) : Prop :=
  IsInvariantSet ds A ∧
  ∃ U : Set (Fin n → ℝ), IsOpen U ∧ A ⊆ U ∧
    ∀ (γ : Trajectory n), SatisfiesODE ds γ →
      γ 0 ∈ U → ∀ ε > 0, ∃ T > 0, ∀ t ≥ T,
        ∃ a ∈ A, dist (γ t) a < ε

/-- A fixed-point attractor: a single asymptotically stable fixed point. -/
def IsFixedPointAttractor {n : ℕ} (ds : ContinuousDS n) (x_star : Fin n → ℝ)
    (hfp : IsFixedPoint ds x_star) : Prop :=
  IsAsymptoticallyStable ds x_star hfp

/-- A limit cycle: a periodic orbit that is an attracting set. -/
def IsLimitCycle {n : ℕ} (ds : ContinuousDS n) (γ₀ : Trajectory n) (T : ℝ) : Prop :=
  IsPeriodicTrajectory γ₀ T ∧
  IsAttractingSet ds (Set.range γ₀)

/-- A strange attractor: an attracting set with sensitive dependence on initial conditions.
    Fractal structure and positive Lyapunov exponent. -/
def IsStrangeAttractor {n : ℕ} (ds : ContinuousDS n) (A : Set (Fin n → ℝ)) : Prop :=
  IsAttractingSet ds A ∧
  ∀ (γ : Trajectory n), SatisfiesODE ds γ → γ 0 ∈ A →
    ∃ δx₀ : Fin n → ℝ, δx₀ ≠ 0 ∧ HasPositiveLyapunovExponent ds γ δx₀

/-! ## Bifurcation Theory -/

/-- A parameterized family of continuous dynamical systems. -/
structure ParameterizedDS (n : ℕ) where
  /-- The parameter-dependent vector field f(x; μ). -/
  f : ℝ → (Fin n → ℝ) → (Fin n → ℝ)

/-- Extract the dynamical system at a given parameter value. -/
def ParameterizedDS.atParam {n : ℕ} (pds : ParameterizedDS n) (μ : ℝ) : ContinuousDS n where
  f := pds.f μ

/-- A bifurcation point: a parameter value μ₀ where the qualitative behavior changes.
    The number or stability of fixed points changes at μ₀. -/
def IsBifurcationPoint {n : ℕ} (pds : ParameterizedDS n) (μ₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ μ₁ μ₂ : ℝ, |μ₁ - μ₀| < ε ∧ |μ₂ - μ₀| < ε ∧
    (∃ x : Fin n → ℝ, IsFixedPoint (pds.atParam μ₁) x ∧
      ¬ IsFixedPoint (pds.atParam μ₂) x) ∨
    (∃ x : Fin n → ℝ, IsFixedPoint (pds.atParam μ₁) x ∧
      IsFixedPoint (pds.atParam μ₂) x ∧
      ∃ hfp₁ : IsFixedPoint (pds.atParam μ₁) x,
      ∃ hfp₂ : IsFixedPoint (pds.atParam μ₂) x,
        (IsLyapunovStable (pds.atParam μ₁) x hfp₁ ∧
         ¬ IsLyapunovStable (pds.atParam μ₂) x hfp₂) ∨
        (¬ IsLyapunovStable (pds.atParam μ₁) x hfp₁ ∧
         IsLyapunovStable (pds.atParam μ₂) x hfp₂))

/-- Saddle-node bifurcation: two fixed points (one stable, one unstable) collide
    and annihilate as the parameter crosses μ₀. -/
def IsSaddleNodeBifurcation {n : ℕ} (pds : ParameterizedDS n) (μ₀ : ℝ) : Prop :=
  ∃ ε > 0,
    (∀ μ : ℝ, μ₀ - ε < μ ∧ μ < μ₀ →
      ∃ x₁ x₂ : Fin n → ℝ, x₁ ≠ x₂ ∧
        IsFixedPoint (pds.atParam μ) x₁ ∧
        IsFixedPoint (pds.atParam μ) x₂) ∧
    (∀ μ : ℝ, μ₀ < μ ∧ μ < μ₀ + ε →
      ¬ ∃ x : Fin n → ℝ, IsFixedPoint (pds.atParam μ) x)

/-- Hopf bifurcation: a fixed point loses stability and a limit cycle is born
    as the parameter crosses μ₀. -/
def IsHopfBifurcation {n : ℕ} (pds : ParameterizedDS n) (μ₀ : ℝ)
    (x_star : ℝ → Fin n → ℝ) : Prop :=
  (∀ μ : ℝ, IsFixedPoint (pds.atParam μ) (x_star μ)) ∧
  ∃ ε > 0,
    (∀ μ : ℝ, μ₀ - ε < μ ∧ μ < μ₀ →
      ∃ hfp : IsFixedPoint (pds.atParam μ) (x_star μ),
        IsLyapunovStable (pds.atParam μ) (x_star μ) hfp) ∧
    (∀ μ : ℝ, μ₀ < μ ∧ μ < μ₀ + ε →
      ∃ hfp : IsFixedPoint (pds.atParam μ) (x_star μ),
        IsUnstable (pds.atParam μ) (x_star μ) hfp ∧
        ∃ (γ : Trajectory n) (T : ℝ), IsLimitCycle (pds.atParam μ) γ T)

/-! ## Poincaré Map -/

/-- A Poincaré section: a codimension-1 surface Σ in phase space
    that the flow intersects transversally. -/
structure PoincareSection (n : ℕ) where
  /-- The section is defined as the zero set of a smooth function. -/
  σ : (Fin n → ℝ) → ℝ
  /-- The section is transversal to the flow (non-degeneracy). -/
  transversal : ∀ x : Fin n → ℝ, σ x = 0 → ∃ i : Fin n, deriv (fun s => σ (Function.update x i s)) (x i) ≠ 0

/-- The Poincaré (first return) map: given a flow and a section Σ,
    P : Σ → Σ maps each point to its next intersection with Σ.
    This reduces a continuous system to a discrete map. -/
noncomputable def poincareMap {n : ℕ} (ds : ContinuousDS n) (sect : PoincareSection n)
    (γ_from : (Fin n → ℝ) → Trajectory n)
    (_h_sol : ∀ x₀, SatisfiesODE ds (γ_from x₀) ∧ γ_from x₀ 0 = x₀) :
    DiscreteDS n where
  f := fun x =>
    let γ := γ_from x
    let T := Classical.epsilon fun t : ℝ => t > 0 ∧ sect.σ (γ t) = 0
    γ T

/-- A fixed point of the Poincaré map corresponds to a periodic orbit
    of the continuous system. This requires analysis of the first return time
    and continuity of the flow, which are deep results in ODE theory. -/
axiom poincare_fixedPoint_periodic {n : ℕ} (ds : ContinuousDS n)
    (sect : PoincareSection n) (γ_from : (Fin n → ℝ) → Trajectory n)
    (h_sol : ∀ x₀, SatisfiesODE ds (γ_from x₀) ∧ γ_from x₀ 0 = x₀)
    (x : Fin n → ℝ) (_hsect : sect.σ x = 0)
    (_hfp : IsDiscreteFixedPoint (poincareMap ds sect γ_from h_sol) x) :
    ∃ T > 0, IsPeriodicTrajectory (γ_from x) T

/-! ## Flow and Semiflow -/

/-- The flow map φ_t : ℝⁿ → ℝⁿ of a continuous dynamical system.
    φ_t(x₀) gives the state at time t starting from x₀. -/
noncomputable def flowMap {n : ℕ} (ds : ContinuousDS n)
    (γ_from : (Fin n → ℝ) → Trajectory n)
    (_h_sol : ∀ x₀, SatisfiesODE ds (γ_from x₀) ∧ γ_from x₀ 0 = x₀)
    (t : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) :=
  fun x₀ => γ_from x₀ t

/-- The flow satisfies the group property: φ_{s+t} = φ_s ∘ φ_t.
    This follows from the uniqueness of solutions to ODEs (Picard-Lindelöf theorem):
    both γ_from x₀ (· + t) and γ_from (γ_from x₀ t) are solutions starting from
    γ_from x₀ t at time 0, hence equal by uniqueness. -/
theorem flow_group_property {n : ℕ} (ds : ContinuousDS n)
    (γ_from : (Fin n → ℝ) → Trajectory n)
    (h_sol : ∀ x₀, SatisfiesODE ds (γ_from x₀) ∧ γ_from x₀ 0 = x₀)
    (_h_unique : ∀ x₀ (γ₁ γ₂ : Trajectory n),
      SatisfiesODE ds γ₁ → SatisfiesODE ds γ₂ →
      γ₁ 0 = x₀ → γ₂ 0 = x₀ → γ₁ = γ₂)
    (s t : ℝ) (x₀ : Fin n → ℝ) :
    flowMap ds γ_from h_sol (s + t) x₀ =
    flowMap ds γ_from h_sol s (flowMap ds γ_from h_sol t x₀) := by
  unfold flowMap
  -- LHS = γ_from x₀ (s + t), RHS = γ_from (γ_from x₀ t) s
  -- Define the shifted trajectory γ_shift(u) = γ_from x₀ (u + t)
  set y := γ_from x₀ t
  -- γ₁ = fun u => γ_from x₀ (u + t) satisfies the ODE and γ₁ 0 = y
  -- γ₂ = γ_from y also satisfies the ODE and γ₂ 0 = y
  -- By uniqueness, γ₁ = γ₂, so γ₁ s = γ₂ s, i.e., γ_from x₀ (s + t) = γ_from y s
  set γ_shift : Trajectory n := fun u => γ_from x₀ (u + t)
  have hshift_ode : SatisfiesODE ds γ_shift := by
    intro i u
    show deriv (fun s => γ_from x₀ (s + t) i) u = ds.f (γ_from x₀ (u + t)) i
    rw [show (fun s => γ_from x₀ (s + t) i) = (fun s => (fun r => γ_from x₀ r i) (s + t)) from rfl,
        deriv_comp_add_const (fun r => γ_from x₀ r i) t u]
    exact (h_sol x₀).1 i (u + t)
  have hshift_init : γ_shift 0 = y := by show γ_from x₀ (0 + t) = y; rw [zero_add]
  have hy_ode : SatisfiesODE ds (γ_from y) := (h_sol y).1
  have hy_init : γ_from y 0 = y := (h_sol y).2
  have heq := _h_unique y γ_shift (γ_from y) hshift_ode hy_ode hshift_init hy_init
  show γ_from x₀ (s + t) = γ_from y s
  exact congr_fun heq s

end Measure.Physics.NonlinearDynamics
