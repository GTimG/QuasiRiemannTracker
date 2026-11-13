/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.ChildCutoff

/-!
# Inverse.Poisson.Interface — the second Poisson step: interface objects

Interface between the selection (`Select/*`), the restoration (`Restore/*`) and the second
Poisson step (`Poisson/*`).

`selectedEnergy`, `columnMass`, `PoissonStepAt`, `PoissonStepStatement` are stated with the
INJECTIVE mark (no `PairwiseDisjoint lists`, child `ChildBoundInj`) in `Poisson/Statement`
(they need `InjMark`, which imports this module). The items below describe them; the full-mark
child objects defined here serve the restoration modules.

* INPUT `selectedEnergy`: the canonical energy after fourth-power selection, literally the
  baseline `normalizedColumnEnergy` with squarefree column scale `Z^N'`, row ball
  `nonzeroChildFrequencyBall 1 (Z^K')` (Gauss rows `k`, `0 < ‖k‖² ≤ Z^K'`), labels `f` of norm
  `≤ Z^V` with weights `D f ≤ Dmax` carrying `χ_U(f)^4`, normalization `Z^(-(N'+V))`, profile
  `childLogTest W s₀`.
* OUTPUT child `mobiusChildSum`: the physical Möbius-column polynomial
  `P_y = ∑_{A ⊆ pool\t} μ(A) ψ(A) mask_A(m) χ_A(y)^{±1} mark(A) Φ(N A/Xc) / √(N A)`
  (exact Dirichlet normalization; `ψ` a ray twist of `Ψ`; residual slots `slots \ J`, original
  lists; residual projector puncture `t`) summed over the physical rows
  `y ∈ nonzeroChildFrequencyBall 1 (Z^(2(N'+V)-K'+κ))`, i.e. `Ny ≤ Z^(H+κ)`, `H = 2(N'+V)-K'`.
* `PoissonStepStatement`: if every child sum is `≤ B (1+|s|)^(2 degree)` then the
  selected energy is `≤ C Z^(K'-N'-V+ε) Dmax (1+|s₀|)^(2 degree) B` plus the already paid
  diagonal `C Z^(K'+ε) Dmax (Z^(-V) #labels) (Z^(-N') ∑_U |mark U|² |W(N U/Z^N')|²)`.
  With `K'=K+4u`, `N'=N-u` this prefactor is `Z^(K-F+5u)` and `H = 1-6u`
  (`prefactor_identities`).

The restoration of the child to `Interface.Contract.inverseMarkedSum` (frozen powers, puncture
restoration) is NOT part of this statement; it is carried out in `Restore/*`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators ContDiff
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.FirstCauchyArithmetic (supportMobius)
open OAI.SecondPassArithmetic (rayMonoid)
open OAI.RayFourExpansion (RayCharacter)

local notation "O" => ActualEisensteinCubic.O

/-! ## Input: the selected canonical energy

`selectedEnergy` and `columnMass` are defined in `Poisson/Statement`: they carry the INJECTIVE
mark `primeMarkInj` (`InjMark`), which imports this module. -/

/-! ## Output: the physical Möbius-column child -/

/-- The child ray characters: `Ψ` twisted by one fixed finite ray character mod 4 (the product
of the Gauss-root character `columnG = ∑ gCoeff·ray` and the quadratic cross-phase character
`∑ crossCoeff·ray·ray`; ray characters form a group, so one twist suffices). -/
def IsChildRay (Ψ ψ : O →* ℂ) : Prop :=
  ∃ χ : RayCharacter, ψ = rayMonoid χ * Ψ

/-- The physical Möbius-column row at the physical row `y`: exact Dirichlet normalization,
row character `χ_A(y)` (`negative = false`) or its conjugate (`negative = true`). -/
def mobiusChildRow {ι σ : Type} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (negative : Bool) (y : O) : ℂ :=
  ∑ A ∈ pool.powerset,
    supportMobius (fun i => Ideal.span {p i}) A * ψ (∏ i ∈ A, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) A m *
      (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y)
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y) *
      primeMark slots lists a A * Φ (primeProductNorm p A / Xc) *
      (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)

/-- The physical child moment over the rows `0 < Ny ≤ Z^Hc`. -/
def mobiusChildSum {ι σ : Type} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (negative : Bool) (Z Hc : ℝ) : ℝ :=
  ∑ y ∈ nonzeroChildFrequencyBall 1 (Z^Hc),
    ‖mobiusChildRow p hg pool ψ m slots lists a Φ Xc negative y‖^2

/-- The child hypothesis consumed by the Poisson step: every residual-projector puncture `t`
(`N t ≤ Gmax`), every set `J` of slots frozen on `g ∪ t` (residual slots `slots \ J`, original
lists), every child ray, every child profile `Φs j` at every height `s` and column scale
`0 < Xc ≤ Xmax`, both orientations. -/
def ChildBound {ι σ : Type} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) {J : ℕ} (Φs : Fin J → ℝ → ℂ) (degree : ℕ) (Z Xmax Gmax Hc B : ℝ) :
    Prop :=
  ∀ t ∈ pool.powerset, primeProductNorm p t ≤ Gmax →
  ∀ Js ∈ slots.powerset, ∀ ψ : O →* ℂ, IsChildRay Ψ ψ → ∀ j : Fin J, ∀ s : ℝ,
  ∀ Xc : ℝ, 0 < Xc → Xc ≤ Xmax → ∀ negative : Bool,
    mobiusChildSum p hg (pool \ t) ψ m (slots \ Js) lists a (childLogTest (Φs j) s) Xc
      negative Z Hc ≤ B * (1+‖s‖)^(2*degree)

/-! ## The Poisson step

`PoissonStepAt` / `PoissonStepStatement` are stated in `Poisson/Statement` with the injective
mark and the injective child `ChildBoundInj` (no `PairwiseDisjoint lists` hypothesis). The
full-mark child objects above (`mobiusChildRow`, `mobiusChildSum`, `ChildBound`) are used by
the restoration modules. -/

/-! ## Exponent bookkeeping of the Poisson step -/

/-- `K'-N'-V = K-F+5u` and `H = 2(N'+V)-K' = 1-6u` when `K = 2F-1`, `F = N+V`,
`K' = K+4u`, `N' = N-u`; and the payment `K-F+5u + (H+u) = F`. -/
theorem prefactor_identities (F N V K u : ℝ) (hF : F = N+V) (hK : K = 2*F-1) :
    (K+4*u)-(N-u)-V = K-F+5*u ∧ 2*((N-u)+V)-(K+4*u) = 1-6*u ∧
      (K-F+5*u)+((1-6*u)+u) = F := by
  subst hF hK
  refine ⟨by ring, by ring, by ring⟩

end
end Qrh.MarkedAnchor.Inverse.Poisson
