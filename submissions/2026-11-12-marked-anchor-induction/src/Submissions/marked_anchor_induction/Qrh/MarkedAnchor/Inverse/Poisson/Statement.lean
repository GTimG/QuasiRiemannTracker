/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjTuple

/-!
# Inverse.Poisson.Statement — the second Poisson step with the injective mark

The statement of the second Poisson step (described in `Poisson/Interface`) for the injective
mark `primeMarkInj` (`InjMark`) on possibly overlapping lists. It lives here (not in `Interface`)
because the injective objects (`InjMark`, `InjTuple`) import `Interface`.

* `selectedEnergy`: `columnEnergyInj` (baseline `normalizedColumnEnergy` with `primeMarkInj`) at
  column scale `Z^N'`, Gauss row ball `Z^K'`, normalization `Z^(-(N'+V))`, height `s₀`.
* `columnMass`: the paid diagonal `Z^(-N') ∑_U |markInj U|² |W(N U/Z^N')|²`.
* `PoissonStepAt`, `PoissonStepStatement`: with NO `PairwiseDisjoint lists` hypothesis and the
  child hypothesis `ChildBoundInj` (the injective child delivered by the restoration).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators ContDiff
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

/-- The canonical energy after fourth-power selection, injective marks. -/
def selectedEnergy {ι σ : Type} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (D : Ideal O → ℝ) (W : ℝ → ℂ)
    (Z N' V K' s₀ : ℝ) : ℝ :=
  columnEnergyInj p hp hcop hg pool Ψ m slots lists a labels
    (nonzeroChildFrequencyBall 1 (Z^K')) D (childLogTest W s₀) (Z^N') Z (N'+V)

/-- The already paid diagonal mass `Z^(-N') ∑_U |markInj U|² |W(N U/Z^N')|²`. -/
def columnMass {ι σ : Type} [DecidableEq ι] (p : ι → O) (pool : Finset ι) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (Z N' : ℝ) : ℝ :=
  Z^(-N') * ∑ U ∈ pool.powerset,
    ‖primeMarkInj slots lists a U‖^2 * ‖W (primeProductNorm p U / Z^N')‖^2

/-- The second Poisson step at one scale `Z` (injective marks, lists may overlap). -/
def PoissonStepAt (Kslots : ℕ) (W : ℝ → ℂ) (bo : ℝ) {J : ℕ} (Φs : Fin J → ℝ → ℂ)
    (dchild degree : ℕ) (ε κ C Z : ℝ) : Prop :=
  ∀ {ι σ : Type} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (labels : Finset (Ideal O)) (D : Ideal O → ℝ) (Dmax N' V K' : ℝ),
    (∀ u, ‖Ψ u‖ ≤ 1) → slots.card ≤ Kslots → (∀ i j, ‖a i j‖ ≤ 1) →
    (∀ f ∈ labels, CompletedGauss.primaryGenerator f ≠ 0 ∧ (Ideal.absNorm f : ℝ) ≤ Z^V) →
    (∀ f ∈ labels, 0 ≤ D f ∧ D f ≤ Dmax) → 0 ≤ Dmax →
    0 ≤ N' → 0 ≤ V → 0 ≤ K' → N'+V ≤ 2 → K' ≤ 4 →
    ∀ B : ℝ, 0 ≤ B →
    ChildBoundInj p hg pool Ψ m slots lists a Φs dchild Z (Z^N') (2*bo*Z^N')
      (2*(N'+V)-K'+κ) B →
    ∀ s₀ : ℝ,
    selectedEnergy p hp hcop hg pool Ψ m slots lists a labels D W Z N' V K' s₀ ≤
      C * Z^(K'-N'-V+ε) * Dmax * (1+‖s₀‖)^(2*degree) * B +
      C * Z^(K'+ε) * Dmax * (Z^(-V) * (labels.card : ℝ)) *
        columnMass p pool slots lists a W Z N'

/-- The second Poisson step (injective marks). Quantifier order: the child profiles `Φs` are
fixed by the column profile `W`; then `∀ dchild ∃ degree ∀ ε κ ∃ C Z₀`. -/
def PoissonStepStatement : Prop :=
  ∀ (Kslots : ℕ) (W : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo →
    Function.support W ⊆ Set.Icc ao bo → ContDiff ℝ ∞ W →
  ∃ (J : ℕ) (Φs : Fin J → ℝ → ℂ) (a' b' : ℝ), 0 < a' ∧ a' ≤ b' ∧
    (∀ j, ContDiff ℝ ∞ (Φs j) ∧ Function.support (Φs j) ⊆ Set.Icc a' b') ∧
  ∀ dchild : ℕ, ∃ degree : ℕ, ∀ ε κ : ℝ, 0 < ε → 0 < κ →
    ∃ C Z₀ : ℝ, 0 < C ∧ 1 ≤ Z₀ ∧
      ∀ Z : ℝ, Z₀ ≤ Z → PoissonStepAt Kslots W bo Φs dchild degree ε κ C Z

end
end Qrh.MarkedAnchor.Inverse.Poisson
