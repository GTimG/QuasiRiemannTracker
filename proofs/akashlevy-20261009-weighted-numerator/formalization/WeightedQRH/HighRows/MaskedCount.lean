import WeightedQRH.HighRows.CountIdentity
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst

/-! Transfer the original full-amplitude row count to a masked numerator mean.
Error-slot widths remain in both denominators. No masked moment is assumed. -/
noncomputable section
open scoped Classical BigOperators
namespace WeightedQRH
open OAI.SevenEighths HeckeDetectorPhysicalSelection

/-- The original certified row exponent is nonincreasing with amplitude. -/
theorem rowCount_antitone {δ x y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3/4)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1/2) :
    rowCount δ y ≤ rowCount δ x := by
  have hdx := countDen_pos hδ0 hδ1 hx0 (hxy.trans hy1)
  have hdy := countDen_pos hδ0 hδ1 (hx0.trans hxy) hy1
  have hpoly : 0 ≤ (44/9:ℝ)-8/3*(x+y)+136/81*x*y := by
    have hp := mul_nonneg hx0 (hx0.trans hxy)
    nlinarith
  have hh := mul_nonneg (mul_nonneg (sq_nonneg ((5/6:ℝ)-δ)) hδ0)
    (mul_nonneg (sub_nonneg.mpr hxy) hpoly)
  have he : countNum δ x*countDen δ y-countNum δ y*countDen δ x=
      ((5/6:ℝ)-δ)^2*δ*(y-x)*((44/9:ℝ)-8/3*(x+y)+136/81*x*y)/2 := by
    unfold countNum countDen countP countD
    ring
  unfold rowCount
  apply (div_le_div_iff₀ hdy hdx).mpr
  nlinarith only [hh,he]

def maskedGain {α : Type*} [DecidableEq α] (main : Finset α) (g : α→ℝ) (i : α) : ℝ :=
  if i∈main then g i else 0

theorem maskedMean_bounds {α : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (δ : ℝ)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2) :
    0 ≤ weightedMean slots width (maskedGain main g) ∧
    weightedMean slots width (maskedGain main g) ≤ weightedMean slots width g ∧
    weightedMean slots width g ≤ δ/2 := by
  have hmasked : ∀j∈slots,0 ≤ maskedGain main g j ∧ maskedGain main g j ≤ δ/2 := by
    intro j hj
    unfold maskedGain
    split_ifs with hm
    · exact hg j hj
    · have hh := hg j hj
      exact ⟨le_rfl,by linarith⟩
  have hb := weightedMean_bounds slots width (maskedGain main g) δ hw hL hmasked
  have hfull := weightedMean_bounds slots width g δ hw hL hg
  refine ⟨hb.1,?_,hfull.2⟩
  unfold weightedMean
  apply div_le_div_of_nonneg_right _ hL.le
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hw j hj)
  unfold maskedGain
  split_ifs with hm
  · exact le_rfl
  · exact (hg j hj).1

/-- A card bound in the original full physical bins remains true at the
weaker diluted main-slot mean. Both means divide by the full slot length. -/
theorem masked_row_count_transfer {α ι : Type*} [DecidableEq α]
    (slots main : Finset α) (width g : α→ℝ) (rows : Finset ι)
    (δ U C loss : ℝ) (hδ : 0 < δ) (hδtop : δ ≤ 3/4)
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2)
    (hcard : (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width g/δ)+loss)) :
    (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width (maskedGain main g)/δ)+loss) := by
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width g δ hw hL hg
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply rowCount_antitone hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    linarith


/-- Every amplitude in a nonempty original class equals its fixed bin value. -/
theorem amplitude_class_value {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0 < mesh) (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots cap mesh) (u : Row)
    (hu : u∈HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U cap mesh hm width Q bin)
    (j : Slot) (hj : j∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(width j)) cap mesh (Q u j)=
      HeckeDetectorFiberPartition.binValue slots cap mesh bin j := by
  have he := (Finset.mem_filter.mp hu).2
  have hv := congrArg (fun f : HeckeDetectorFiberPartition.BinLabel slots cap mesh=>(f ⟨j,hj⟩).val) he
  simpa only [HeckeDetectorFiberPartition.amplitudeLabel,HeckeDetectorFiberPartition.binValue,
    dite_eq_left hj] using hv

/-- Direct count transfer on an actual full amplitude class. The full bin is
retained, while main amplitudes are zeroed only after the count is proved. -/
theorem masked_amplitude_class_count {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(rowCount δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(rowCount δ (q/δ)+loss) := by
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
  exact masked_row_count_transfer slots main width _ _ δ U C loss hδ hδtop hU hC hw hL hg hcard

end WeightedQRH
end
