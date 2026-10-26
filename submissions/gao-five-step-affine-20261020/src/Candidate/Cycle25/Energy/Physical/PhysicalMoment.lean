import Candidate.Cycle25.Energy.Physical.SourceState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.Moments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.NumeratorPhysicalMoment

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentPositiveSummability CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily ConcreteTraceCRT CenteredMomentRowNorm ActualEisensteinCubic
local notation "O" => HeckeFamily.O

/-- Restricting the actual nonnegative radial energy to a finite physical row set. -/
theorem finite_actual_pair_le_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : Finset FreeRow) (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ : ℝ) (hU : 1 ≤ U) (_hδ : 0 ≤ δ)
    (_hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (_hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η Q u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (slots : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀i, 0 < P i) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
        ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2)
      ≤ energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
        slots β P X₁ X₂ (initialKeep η Q) Φ U := by
  let m := fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)
  let f (z : O) : ℝ := if initialKeep η Q z then
    ‖positiveSlotRow η m 1 z W₁ W₂ slots β P 0 X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/U)).re else 0
  have hUp : 0 < U := zero_lt_one.trans_le hU
  obtain ⟨B,hB⟩ := product_bounded η m 1 0
    (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂
    hs₁ hs₂ hX₁ hX₂ slots β
  have hsum : Summable f :=
    bounded_radial_summable _ B hB (initialKeep η Q) Φ U hUp
  have hf0 (z : O) : 0 ≤ f z := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hp _)
    · exact le_rfl
  have he (u : FreeRow) (hu : u ∈ rows) :
      f u.val = ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
          ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2 := by
    have hx : ‖eisEmbedding u.val‖^2/U ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hUp.le,(div_le_one hUp).mpr ?_⟩
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    dsimp [f]
    rw [ite_eq_left (hkeep u hu),hone _ hx,Complex.one_re,mul_one]
    rw [OAI.SevenEighths.WeightedNumeratorReflection.actual_pair_source_identity η u W₁ W₂ slots β P X₁ X₂ hX₁ hX₂ hP]
  calc
    _ = ∑u∈rows, f u.val := Finset.sum_congr rfl (fun u hu => (he u hu).symm)
    _ = ∑z∈rows.image Subtype.val, f z := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
    _ ≤ ∑'z, f z := Summable.sum_le_tsum _ (fun z _ => hf0 z) hsum
    _ = _ := rfl

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/
