/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Bundles.B067
import Candidate.Affine.Balanced

/-! Monotonicity of the region-aware count in the prime proportion, and the
masked amplitude-class transfer with the region-aware count. -/

set_option maxHeartbeats 400000

namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section
open HeckeDetectorPhysicalSelection
open scoped Classical BigOperators
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein

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
  set Q : ℝ := 2393785639/1158720000-83528567/68160000*p'-83528567/68160000*p+
    53541811447/65815296000*p*p'+δ*(-424328567/170400000+4292185639/2896800000*p'+
    4292185639/2896800000*p-812280128753/822691200000*p*p') with hQ
  have hid : (1-p)*DetectorAffine.cN p*DetectorAffine.JN δ p'-
      (1-p')*DetectorAffine.cN p'*DetectorAffine.JN δ p = (p'-p)*Q := by
    rw [hQ]
    unfold DetectorAffine.cN DetectorAffine.JN DetectorAffine.DN DetectorAffine.aN
      DetectorAffine.lam DetectorAffine.Bc
    ring
  have hQpos : 0 ≤ Q := by
    rw [hQ]
    have a1 : 0 ≤ p-99/200 := by linarith
    have a2 : 0 ≤ p'-99/200 := by linarith
    have a3 : 0 ≤ δ-89/200 := by linarith
    nlinarith [mul_nonneg a1 a2, mul_nonneg a3 a1, mul_nonneg a3 a2,
      mul_nonneg (mul_nonneg a3 a1) a2]
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
