/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.FineNaturalCount
import Candidate.Local.Qrh.JointDetector.AdaptivePrice
import Candidate.Local.Qrh.JointDetector.RefinedSupplier
import Candidate.Local.Qrh.JointDetector.FineAdaptiveSupplier.High
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

namespace Qrh.JointDetector.RepeatedMarks
open FineNaturalCount FineDetectorWords FineDetectorCount
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical LocalMoment
open HeckeDetectorWitnessRows
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentEnergyBands
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

private theorem finite_core_population_aux (coreIdeals : Finset (Ideal O))
    (hcores : ∀ I ∈ coreIdeals, I ≠ 0) (E : Finset O) (B : ℝ) (hB : 1 ≤ B)
    (hnonzero : ∀ z ∈ E, z ≠ 0)
    (hnorm : ∀ z ∈ E, ((Ideal.span {z}).absNorm : ℝ) ≤ B)
    (hcore : ∀ z ∈ E, CenteredExceptionalCount.sixthRemainder (Ideal.span {z}) ∈ coreIdeals) :
    (E.card : ℝ) ≤ 768*(coreIdeals.card : ℝ)*B^(1/6 : ℝ) := by
  let core (z : O) := CenteredExceptionalCount.sixthRemainder (Ideal.span {z})
  have hchild (I : Ideal O) (hI : I ∈ coreIdeals) :
      ((E.filter fun z => core z = I).card : ℝ) ≤ 768*B^(1/6 : ℝ) := by
    have hnI : 1 ≤ (I.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hcores I hI))
    have h := CenteredExceptionalCount.element_count_fixed_remainder
      (E.filter fun z => core z = I) I (hcores I hI) B (by linarith)
      (fun z hz => hnonzero z (Finset.mem_filter.mp hz).1)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hnorm z (Finset.mem_filter.mp hz).1)
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) ((div_le_iff₀ (by linarith : 0 < (I.absNorm : ℝ))).2
        (by nlinarith)) (by norm_num : (0 : ℝ) ≤ 1/6)) (by norm_num))
  have hcard : (E.card : ℝ) = ∑ I ∈ coreIdeals, ((E.filter fun z => core z = I).card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := E) (t := coreIdeals) (f := core)
      (fun z hz => hcore z hz)
    exact_mod_cast h
  calc
    _ = ∑ I ∈ coreIdeals, ((E.filter fun z => core z = I).card : ℝ) := hcard
    _ ≤ ∑ _I ∈ coreIdeals, 768*B^(1/6 : ℝ) := Finset.sum_le_sum fun I hI => hchild I hI
    _ = _ := by simp; ring

/-- The finite principal/initially-exceptional FREE cores have infinitely
many natural lifts; this proves their whole `B^(1/6)` complementary count.
-/
theorem finite_exceptional_raw_count (coreSet : Finset FreeRow) : ∃ C : ℝ, 0 < C ∧
      ∀ B : ℝ, 1 ≤ B → ∀ rows : Finset NonzeroFrequency,
      (∀ u ∈ rows, rawFrequencyNorm u ≤ B ∧ (sixthFrequencyEquiv.symm u).1 ∈ coreSet) →
      (rows.card : ℝ) ≤ C*B^(1/6 : ℝ) := by
  let coreIdeals := coreSet.image (fun u => (Ideal.span {u.val} : Ideal O))
  let C := 768*(coreIdeals.card : ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B hB rows hrows
  let E := rows.image Subtype.val
  have hcard : E.card = rows.card := Finset.card_image_of_injective rows Subtype.val_injective
  have hE := finite_core_population_aux coreIdeals
    (by intro I hI; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hI
        exact Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    E B hB
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz; exact u.property)
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz; exact (hrows u hu).1)
    (by intro z hz; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
        rw [raw_sixth_remainder]
        exact Finset.mem_image.mpr ⟨(sixthFrequencyEquiv.symm u).1,
          (hrows u hu).2, rfl⟩)
  rw [hcard] at hE
  exact hE.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
    (Real.rpow_nonneg (zero_le_one.trans hB) _))


end
end Qrh.JointDetector.RepeatedMarks
