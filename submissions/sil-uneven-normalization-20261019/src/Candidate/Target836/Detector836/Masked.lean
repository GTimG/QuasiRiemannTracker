import Candidate.Target836.Detector836.Antitone

set_option autoImplicit false
namespace Detector836
noncomputable section
open Cycle63.Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem new_le_old_at_kappa {κ δ p : ℝ} (h : InRegion δ p) (hk : kStar ≤ κ) :
    RNew δ p ≤ countingR0 κ δ p := by
  have h1 := region_compare h
  rw [ROld_eq_target] at h1
  have h2 := countingR0_mono_kappa (show 7/10 ≤ kStar by norm_num [kStar]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [h.1,h.2.1])
    (show 0 ≤ p ∧ p ≤ 1/2 by constructor <;> linarith [h.2.2.1,h.2.2.2])
  exact h1.trans h2

theorem accepted_le_old_at_kappa {κ δ p : ℝ} (h : InAcceptedRegion δ p) (hk : kStar ≤ κ) :
    DetectorAffine.RNew δ p ≤ countingR0 κ δ p := by
  have h1 := accepted_compare h
  rw [ROld_eq_target] at h1
  have h2 := countingR0_mono_kappa (show 7/10 ≤ kStar by norm_num [kStar]) hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [h.1,h.2.1])
    (show 0 ≤ p ∧ p ≤ 1/2 by constructor <;> linarith [h.2.2.1,h.2.2.2])
  exact h1.trans h2

theorem count_antitone836 {κ δ x y : ℝ} (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    count κ δ y ≤ count κ δ x := by
  have hold := countingR0_antitone hk hk1 hδ hδ1 hx hxy hy
  by_cases hks : kStar ≤ κ
  · by_cases hnX : InRegion δ x
    · have hnY : InRegion δ y := ⟨hnX.1,hnX.2.1,hnX.2.2.1.trans hxy,hy⟩
      simpa only [count,hnX,hnY,hks,and_self,ite_true] using RNew_antitone hnX hnY hxy
    · by_cases hnY : InRegion δ y
      · have hnotAX : ¬InAcceptedRegion δ x := by
          intro ha
          apply hnX
          exact ⟨hnY.1,hnY.2.1,by linarith [ha.2.2.1],hxy.trans hy⟩
        calc
          count κ δ y = RNew δ y := by simp only [count,hnY,hks,and_self,ite_true]
          _ ≤ countingR0 κ δ y := new_le_old_at_kappa hnY hks
          _ ≤ countingR0 κ δ x := hold
          _ = count κ δ x := by simp only [count,hnX,hnotAX,false_and,ite_false]
      · by_cases haX : InAcceptedRegion δ x
        · have haY : InAcceptedRegion δ y := ⟨haX.1,haX.2.1,haX.2.2.1.trans hxy,hy⟩
          have hh := OAI.SevenEighths.Cycle25DetectorRowCount.RNew_antitone
            (accepted_region_subset haX) (accepted_region_subset haY) hxy
          simpa only [count,hnX,hnY,haX,haY,hks,false_and,and_self,ite_false,ite_true] using hh
        · by_cases haY : InAcceptedRegion δ y
          · calc
              count κ δ y = DetectorAffine.RNew δ y := by
                simp only [count,hnY,haY,hks,false_and,and_self,ite_false,ite_true]
              _ ≤ countingR0 κ δ y := accepted_le_old_at_kappa haY hks
              _ ≤ countingR0 κ δ x := hold
              _ = count κ δ x := by simp only [count,hnX,haX,false_and,ite_false]
          · simpa only [count,hnX,hnY,haX,haY,false_and,ite_false] using hold
  · simpa only [count,hks,and_false,ite_false] using hold

end
end Detector836

#print axioms Detector836.count_antitone836

namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators
theorem masked_amplitude_class_count836 {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(Detector836.count κ δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(Detector836.count κ δ (q/δ)+loss) := by
  dsimp only
  have hg : ∀j∈slots,0 ≤ HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←amplitude_class_value rows slots U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width
    (HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply Detector836.count_antitone836 hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    have h' : HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin ≤ δ/2 := hqtop
    linarith

end
end OAI.SevenEighths.Cycle25DetectorRowCount
#print axioms OAI.SevenEighths.Cycle25DetectorRowCount.masked_amplitude_class_count836
