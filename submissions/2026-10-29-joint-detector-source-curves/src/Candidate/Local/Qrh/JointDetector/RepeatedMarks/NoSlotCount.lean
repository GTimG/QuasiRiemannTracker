/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.NoSlotMoments
import Submissions.hailey_collet_1252270103.Cycle61.Density.ActualBatchCount

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Set Filter OAI OAI.SevenEighths
open LocalMoment HeckeFamily HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount HeckeDetectorCoefficientTransfer

/-- The genuine unmarked inverse and plain arms for every supported fiber,
with an arbitrary cutoff in [1,3/2]. No optimizing cutoff is assumed. -/
theorem actual_no_slot_fiber_counts {Label : Type*} [Fintype Label]
    (base : Label → Character) (εm : ℝ) (hεm : 0 < εm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ (a ε tstar T allowance : ℝ) (i : ℕ),
      1/2 ≤ a → 1 ≤ tstar → tstar ≤ 3/2 → 0 ≤ ε → ε ≤ 1/1000 →
    ∀ B : UnmarkedBatch Label U a ε tstar T allowance i,
      B.data=(FixedUnmarkedDictionary.ofBases base).data →
    ∀ height : ℝ, 0 ≤ height → 2*Real.pi*allowance+(3*i:ℕ)*T ≤ height →
    ∀ j left right, ∀ hne : (B.fiberRows j left right).Nonempty,
      let F := B.fiber j left right hne
      (F.rows.card:ℝ) ≤ C*(1+height)^J*
        U^(sourceExponent F.r-(2*a-1)*F.r+2*ε+εm) ∧
      (F.rows.card:ℝ) ≤ C*(1+height)^J*
        U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  let S := canonicalDensityCountingSetup
  haveI : NeZero S.modulus := ⟨S.nonzero⟩
  obtain ⟨c,κ,K0,hc,hc1,hκ,hK0,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    S.modulus S.subgroup S.units S.exclusions S.profile S.smooth S.compact S.positiveSupport
    S.nonnegative S.nontrivial S.lower S.upper S.bound S.lowerPositive S.ordered S.boundPositive
    S.support S.bounded 2 εm (by norm_num) hεm
  obtain ⟨J,C,hC,hmom⟩ := fixed_dictionary_actual_batch_moments
    (FixedUnmarkedDictionary.ofBases base) c κ εm hc hκ hεm hβ
  let Cstar := 192*C*(K0+1)
  have hCstar : 0 < Cstar := by dsimp [Cstar]; positivity
  refine ⟨J+1,Cstar,hCstar,?_⟩
  filter_upwards [hamp,hmom] with U hI hM
  refine ⟨hM.1,?_⟩
  intro a ε tstar T allowance i ha ht ht' hε hε' B hdata height hh hf j left right hne
  let F := B.fiber j left right hne
  have moments : UnmarkedMoments F c κ (C*(1+height)^J) height εm :=
    hM.2 ht ht' hε hε' B hdata height hh j left right hne
  have hgeom := HeckeDetectorSupportedWitness.fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hM.1
    F.witness F.left F.right F.fixed_left F.fixed_right
  have hr : 0 ≤ F.r := by
    change tstar-F.r-ε ≤ F.m ∧ F.r ≤ tstar+ε ∧ F.m ≤ 1/2+75*ε ∧
      tstar-1/2-76*ε ≤ F.r ∧ 0 ≤ F.m at hgeom
    linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by
    have h := hgeom.2.1
    change F.r ≤ tstar+ε at h
    linarith
  have hi := hI F.rows F.family a ε tstar T allowance i hM.1 ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr hr2 F.rowData F.reverse (C*(1+height)^J) height (by positivity) hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hp := HeckeDetectorNoSlotPlainCount.no_slot_plain_count F.rows F.family U a ε tstar T allowance i hM.1
    (by linarith) (fun u => (F.witness u).toWitness) F.label F.left F.right
    F.fixed_label F.fixed_left F.fixed_right εm (C*(1+height)^J) height (by positivity) hh hf moments.plain_unmarked
  have hpow : (1+height)^(J+1)=(1+height)^J*(1+height) := by rw [pow_succ]
  have hbase : 0 ≤ C*(1+height)^(J+1) := by positivity
  have hCi : 12*(1+height)*(C*(1+height)^J*K0) ≤ Cstar*(1+height)^(J+1) := by
    calc _ = (12*K0)*(C*(1+height)^(J+1)) := by rw [hpow]; ring
         _ ≤ (192*(K0+1))*(C*(1+height)^(J+1)) :=
           mul_le_mul_of_nonneg_right (by linarith) hbase
         _ = _ := by dsimp [Cstar]; ring
  have hCp : 192*(1+height)*(C*(1+height)^J) ≤ Cstar*(1+height)^(J+1) := by
    calc _ = 192*(C*(1+height)^(J+1)) := by rw [hpow]; ring
         _ ≤ (192*(K0+1))*(C*(1+height)^(J+1)) :=
           mul_le_mul_of_nonneg_right (by linarith) hbase
         _ = _ := by dsimp [Cstar]; ring
  exact ⟨hi.trans (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg (by linarith [hM.1]) _)),
    hp.trans (mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg (by linarith [hM.1]) _))⟩

end
end Qrh.JointDetector.RepeatedMarks
#print axioms Qrh.JointDetector.RepeatedMarks.actual_no_slot_fiber_counts
