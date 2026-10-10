import Cycle25.Assembly.Count.Endpoint
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators

theorem coefficient_antitone {κ x y : ℝ} (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : coefficient y κ≤coefficient x κ := by
  have hdx : 0<denominator x κ := lt_of_lt_of_le (by norm_num) (denominator_lower hx (hxy.trans hy) hk hk1)
  have hdy : 0<denominator y κ := lt_of_lt_of_le (by norm_num) (denominator_lower (hx.trans hxy) hy hk hk1)
  let a : ℝ := 1/(3*κ)
  have ha : 0≤a := by dsimp [a]; positivity
  have ha1 : a≤10/21 := (div_le_iff₀ (show 0<3*κ by linarith)).mpr (by linarith)
  have hbx : b x κ=x*a := by unfold b; dsimp [a]; ring
  have hby : b y κ=y*a := by unfold b; dsimp [a]; ring
  have he : primeWeight x κ*denominator y κ-primeWeight y κ*denominator x κ=
      (y-x)*(4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y) := by
    unfold primeWeight denominator
    rw [hbx,hby]
    ring
  have hsum : x+y≤1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum ha
  have hp : 0≤4+2*a-6*a*(x+y)+2*a*(1+2*a)*x*y := by
    have hp := mul_nonneg (mul_nonneg (mul_nonneg ha (by linarith : 0≤1+2*a)) hx) (hx.trans hxy)
    nlinarith
  have hh := mul_nonneg (sub_nonneg.mpr hxy) hp
  unfold coefficient
  apply (div_le_div_iff₀ hdy hdx).mpr
  linarith

theorem rowCount_antitone {δ κ x y : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hx : 0≤x) (hxy : x≤y) (hy : y≤1/2) : rowCount δ y κ≤rowCount δ x κ := by
  have hc := coefficient_antitone hk hk1 hx hxy hy
  have hcx := coefficient_nonneg hx (hxy.trans hy) hk hk1
  have hcy := coefficient_nonneg (hx.trans hxy) hy hk hk1
  have hv : 0<V δ := by unfold V; linarith
  have hdx : 0<2*(V δ+δ*coefficient x κ) := by positivity
  have hdy : 0<2*(V δ+δ*coefficient y κ) := by positivity
  unfold rowCount
  apply add_le_add le_rfl
  apply (div_le_div_iff₀ hdy hdx).mpr
  have hh := mul_nonneg (mul_nonneg hδ (sq_nonneg (V δ))) (sub_nonneg.mpr hc)
  nlinarith
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
    (δ κ U C loss : ℝ) (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (hg : ∀j∈slots,0 ≤ g j ∧ g j ≤ δ/2)
    (hcard : (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width g/δ) κ+loss)) :
    (rows.card:ℝ) ≤ C*U^(rowCount δ (weightedMean slots width (maskedGain main g)/δ) κ+loss) := by
  obtain ⟨hq0,hq,hqtop⟩ := maskedMean_bounds slots main width g δ hw hL hg
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply rowCount_antitone hδ.le hδtop hk hk1
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
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(rowCount δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ) κ+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(rowCount δ (q/δ) κ+loss) := by
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
  exact masked_row_count_transfer slots main width _ _ δ κ U C loss hδ hδtop hk hk1 hU hC hw hL hg hcard

end
end OAI.SevenEighths.Cycle25DetectorRowCount
