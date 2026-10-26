/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle63.Numerator.Source.ActualBin
import Candidate.Cycle63.Numerator.Source.Parameters
import Candidate.Cycle63.Numerator.Source.SelectedBin
import Candidate.Cycle25.Assembly.Count.MaskedCount
import Candidate.Affine.Balanced

/-! Monotonicity of the region-aware count in the prime proportion, and the
masked amplitude-class transfer with the region-aware count. -/

set_option maxHeartbeats 400000

namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein

theorem countingR0_mono_kappa {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    countingR0 a d p ≤ countingR0 κ d p := by
  have hk := ha.trans hak
  have hc := counting_gap ha hak hp
  have hSa := rowDen_pos ha hd hp
  have hSk := rowDen_pos hk hd hp
  have hid : countingR0 κ d p-countingR0 a d p =
      (d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p))*
        (countingCoefficient κ p-countingCoefficient a p) := by
    unfold countingR0
    field_simp [ne_of_gt hSa, ne_of_gt hSk]
    simp only [rowDen]
    ring
  have hfac : 0 ≤ d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p) := by
    have := hd.1; positivity
  have := mul_nonneg hfac hc.1
  linarith

theorem countingR0_antitone {κ δ x y : ℝ} (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    countingR0 κ δ y ≤ countingR0 κ δ x := by
  rw [← OAI.SevenEighths.DetectorAffineCount.rowCount_eq_countingR0 hk,
    ← OAI.SevenEighths.DetectorAffineCount.rowCount_eq_countingR0 hk]
  exact rowCount_antitone hδ hδ1 hk hk1 hx hxy hy

theorem ROld_eq (δ p : ℝ) : DetectorAffine.ROld δ p = countingR0 kappaStar δ p := by
  unfold DetectorAffine.ROld countingR0 rowDen countingCoefficient countingDen
    DetectorAffine.oldNum DetectorAffine.oldDen DetectorAffine.kStar kappaStar
  ring_nf

theorem RNew_antitone {δ p p' : ℝ} (h : DetectorAffine.InRegion δ p)
    (h' : DetectorAffine.InRegion δ p') (hpp : p ≤ p') :
    DetectorAffine.RNew δ p' ≤ DetectorAffine.RNew δ p := by
  have hJ := DetectorAffine.region_JN_pos h
  have hJ' := DetectorAffine.region_JN_pos h'
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨_, _, h3', h4'⟩ := h'
  -- (1-p)cN(p) JN(p') - (1-p')cN(p') JN(p) = (p'-p) Q, Q multilinear and positive on the box
  set Q : ℝ := (-1380872038393/1398575040000)*δ*p*p' +
    (429320527/289680000)*δ*p +
    (429320527/289680000)*δ*p' +
    (-721460527/289680000)*δ +
    (91086437807/111886003200)*p*p' +
    (-142100527/115872000)*p +
    (-142100527/115872000)*p' +
    (239480527/115872000) with hQ
  have hid : (1-p)*DetectorAffine.cN p*DetectorAffine.JN δ p'-
      (1-p')*DetectorAffine.cN p'*DetectorAffine.JN δ p = (p'-p)*Q := by
    rw [hQ]
    unfold DetectorAffine.cN DetectorAffine.JN DetectorAffine.DN DetectorAffine.aN
      DetectorAffine.lam DetectorAffine.Bc
    ring
  have hQpos : 0 ≤ Q := by
    let u : ℝ := (δ-89/200)/(1/25)
    let v : ℝ := (p-199/400)/(1/400)
    let w : ℝ := (p'-199/400)/(1/400)
    have hu : 0 ≤ u ∧ u ≤ 1 := by dsimp [u]; constructor <;> linarith
    have hv : 0 ≤ v ∧ v ≤ 1 := by dsimp [v]; constructor <;> linarith
    have hw : 0 ≤ w ∧ w ≤ 1 := by dsimp [w]; constructor <;> linarith
    have hu0 : 0 ≤ u := hu.1
    have hv0 : 0 ≤ v := hv.1
    have hw0 : 0 ≤ w := hw.1
    have hu1 : 0 ≤ 1-u := by linarith [hu.2]
    have hv1 : 0 ≤ 1-v := by linarith [hv.2]
    have hw1 : 0 ≤ 1-w := by linarith [hw.2]
    have hidentity : Q = (7268325556498688041/14918133760000000000)*(1-u)*(1-v)*(1-w) +
      (36270689195194903/74590668800000000)*(1-u)*(1-v)*(w) +
      (36270689195194903/74590668800000000)*(1-u)*(v)*(1-w) +
      (180999626526841/372953344000000)*(1-u)*(v)*(w) +
      (6516287080776325393/14918133760000000000)*(u)*(1-v)*(1-w) +
      (32517887620131119/74590668800000000)*(u)*(1-v)*(w) +
      (32517887620131119/74590668800000000)*(u)*(v)*(1-w) +
      (486817441833379/1118860032000000)*(u)*(v)*(w) := by
      rw [hQ]
      dsimp [u,v,w]
      ring
    rw [hidentity]
    positivity
  have hcross : (1-p')*DetectorAffine.cN p'*DetectorAffine.JN δ p ≤
      (1-p)*DetectorAffine.cN p*DetectorAffine.JN δ p' := by
    have := mul_nonneg (sub_nonneg.mpr hpp) hQpos
    linarith
  have hfrac : (1-p')*DetectorAffine.cN p'/DetectorAffine.JN δ p' ≤
      (1-p)*DetectorAffine.cN p/DetectorAffine.JN δ p := by
    rw [div_le_div_iff₀ hJ' hJ]; linarith
  have hV : 0 ≤ (5/6-δ)*δ := mul_nonneg (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hfrac hV
  unfold DetectorAffine.RNew
  have e1 : (5/6-δ)*δ*(1-p')*DetectorAffine.cN p'/DetectorAffine.JN δ p' =
      (5/6-δ)*δ*((1-p')*DetectorAffine.cN p'/DetectorAffine.JN δ p') := by ring
  have e2 : (5/6-δ)*δ*(1-p)*DetectorAffine.cN p/DetectorAffine.JN δ p =
      (5/6-δ)*δ*((1-p)*DetectorAffine.cN p/DetectorAffine.JN δ p) := by ring
  rw [e1, e2]; linarith


/-- The region-aware count is antitone in the prime proportion. -/
theorem countingR_antitone {κ δ x y : ℝ} (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    countingR κ δ y ≤ countingR κ δ x := by
  have hd : 0 ≤ δ ∧ δ ≤ 5/6 := ⟨hδ, by linarith⟩
  unfold countingR
  by_cases hX : DetectorAffine.InRegion δ x ∧ kappaStar ≤ κ
  · have hY : DetectorAffine.InRegion δ y ∧ kappaStar ≤ κ :=
      ⟨⟨hX.1.1, hX.1.2.1, hX.1.2.2.1.trans hxy, hy⟩, hX.2⟩
    rw [if_pos hX, if_pos hY]
    exact RNew_antitone hX.1 hY.1 hxy
  · rw [if_neg hX]
    by_cases hY : DetectorAffine.InRegion δ y ∧ kappaStar ≤ κ
    · rw [if_pos hY]
      have h1 := DetectorAffine.region_compare hY.1
      rw [ROld_eq] at h1
      have h2 := countingR0_mono_kappa kappaStar_mem.1 hY.2 hd ⟨hx.trans hxy, hy⟩
      have h3 := countingR0_antitone hk hk1 hδ hδ1 hx hxy hy
      linarith
    · rw [if_neg hY]
      exact countingR0_antitone hk hk1 hδ hδ1 hx hxy hy

theorem masked_amplitude_class_count_A {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots main : Finset Slot) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Slot→ℝ) (Q : Row→Slot→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel slots (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈slots,0 ≤ width j) (hL : 0 < ∑j∈slots,width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(countingR κ δ (HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue slots (δ/2) mesh bin
    let q := weightedMean slots width (maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows slots U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(countingR κ δ (q/δ)+loss) := by
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
  apply countingR_antitone hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    have h' : HeckeDetectorAmplitudeFirst.classMean slots (δ/2) mesh width bin ≤ δ/2 := hqtop
    linarith

end
end OAI.SevenEighths.Cycle25DetectorRowCount
