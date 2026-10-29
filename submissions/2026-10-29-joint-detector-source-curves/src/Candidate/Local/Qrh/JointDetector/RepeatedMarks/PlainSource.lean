/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Submissions.sil_density_split_20261026.Density.LeafRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalParentSources

/-! The ordinary parent source controls any fixed finite repeated slot type.
This is an ordinary two-plain moment, with the exact source coefficients and keep
predicate. Moving root holes must be expanded before using this interface. -/
namespace Qrh.JointDetector.RepeatedMarks.PlainSource
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open QRH.Record12518109Source QRH.Record1252270103Source
open ConcreteTraceCRT ActualEisensteinCubic CenteredMomentEnergyCapacityRemoval
local notation "O" => HeckeFamily.O

/-- Positive radial majorization of a finite literal row set. No operation on
character coefficients, coprime selectors or source profiles is made here. -/
theorem finite_rows_le_energy {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b)
    (rows : Finset O) (hkeep : ∀ z ∈ rows, keep z)
    (hweight : ∀ z ∈ rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    ∑ z ∈ rows, ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  let f : O → ℝ := fun z => if keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 *
      (Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hnonneg : ∀ z, 0 ≤ f z := by
    intro z
    dsimp [f]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  calc
    _ ≤ ∑ z ∈ rows, f z := by
      apply Finset.sum_le_sum
      intro z hz
      dsimp [f]
      rw [if_pos (hkeep z hz)]
      exact le_mul_of_one_le_right (sq_nonneg _) (hweight z hz)
    _ ≤ ∑' z, f z := by
      exact Summable.sum_le_tsum rows (fun z _ => hnonneg z)
        (compact_radial_summable (fun z => positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
          keep Φ K b hK hs)
    _ = _ := rfl

/-- Apply one actual ordinary source to an arbitrary fixed finite slot family.
In particular the family may be `Σ i, Fin (multiplicity i)`, with each copy
carrying the original width, relative character and shift. The total copied
width is charged in the literal face hypothesis. -/
theorem finite_moment_of_initial {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (B L c Z mesh ε bΦ : ℝ) (η η₀ : Character) (Q : Ideal O)
    (W : ℝ → ℂ) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ)
    (hsource : InitialAffineAt (α:=α) rayM H hH (globalFace B L c) W 2
      (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C)
    (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ)
    (t height : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hσlo : ∀ i, (33/50:ℝ) ≤ σ i) (hσhi : ∀ i, σ i ≤ 33/50)
    (hh : 0 ≤ height) (hv : ∀ i, |v i| ≤ height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦ : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ)
    (hΦp : ∀ x, 0 ≤ (Φ x).re) (hZ : 0 < Z)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hadm : (globalFace B L c).Admissible (length Z X₁) (length Z X₂) (∑ i,w i) 1)
    (rows : Finset O) (hkeep : ∀ z ∈ rows, initialKeep η (internalQ Q η₀) z)
    (hweight : ∀ z ∈ rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/Z)).re) :
    ∑ z ∈ rows, ‖positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z
      (p.profile 0) (p.profile 1) (fun i => primePool rayM H 2 (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) t X₁ X₂‖^2 ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
        (1+|t|+height)^degree*Z^(1+ε) := by
  have hm := hsource T θ w σ v t height hw hwm hσlo hσhi hh hv 1 le_rfl le_rfl
    Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm
  rw [Real.rpow_one] at hm
  exact (finite_rows_le_energy η (fixedBadMask*idealGenerator 1) 1 t
    (p.profile 0) (p.profile 1) _ _ _ X₁ X₂ _ Φ Z bΦ hΦp hZ hΦ rows hkeep hweight).trans hm

end
end Qrh.JointDetector.RepeatedMarks.PlainSource

#print axioms Qrh.JointDetector.RepeatedMarks.PlainSource.finite_moment_of_initial
