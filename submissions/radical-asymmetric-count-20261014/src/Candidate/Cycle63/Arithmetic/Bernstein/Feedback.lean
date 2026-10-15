import Candidate.Cycle63.Arithmetic.Bernstein.Endpoint

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Cycle63.Arithmetic.Bernstein

/- The generic counting_gap and row_gap algebra is adapted from
Cycle25/Arithmetic/Perturbation.lean. Its endpoint theorems are not imported. -/

noncomputable def countingDen (κ p : ℝ) : ℝ := 3*κ*(3-p)-2*p
/-- Cκ(p), with the inner divisions cleared. -/
noncomputable def countingCoefficient (κ p : ℝ) : ℝ :=
  2*(1-p)*(3*κ-p)/countingDen κ p
noncomputable def rowDen (κ d p : ℝ) : ℝ := (5/6-d)+d*countingCoefficient κ p
/-- The detector count exponent Rκ(δ,p). -/
noncomputable def countingR (κ d p : ℝ) : ℝ :=
  1-d+d*countingCoefficient κ p*(5/6-d)/(2*rowDen κ d p)
theorem countingDen_lower {κ p : ℝ} (hk : 7/10 ≤ κ) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    (17:ℝ)/4 ≤ countingDen κ p := by
  have hprod := mul_le_mul_of_nonneg_right hk (show 0 ≤ 3-p by linarith)
  unfold countingDen
  nlinarith

theorem countingCoefficient_pos {κ p : ℝ} (hk : 7/10 ≤ κ) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    0 < countingCoefficient κ p := by
  have hden : 0 < countingDen κ p := by linarith [countingDen_lower hk hp]
  have h1 : 0 < 1-p := by linarith
  have h2 : 0 < 3*κ-p := by linarith
  unfold countingCoefficient
  positivity

theorem rowDen_pos {κ d p : ℝ} (hk : 7/10 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) : 0 < rowDen κ d p := by
  have hc := countingCoefficient_pos hk hp
  unfold rowDen
  by_cases he : d = 0
  · rw [he]; norm_num
  · have hd0 : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm he)
    have hdc : 0 < d*countingCoefficient κ p := mul_pos hd0 hc
    linarith

theorem canonical_counting_formula {κ p : ℝ} (hk : 7/10 ≤ κ) :
    countingCoefficient κ p = 2*(1-p)*(1-p/(3*κ))/(3-p-2*p/(3*κ)) := by
  have hk0 : κ ≠ 0 := ne_of_gt (by linarith)
  unfold countingCoefficient countingDen
  field_simp [hk0]

theorem counting_gap {a κ p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hp : 0 ≤ p ∧ p ≤ 1/2) :
    0 ≤ countingCoefficient κ p-countingCoefficient a p ∧
    countingCoefficient κ p-countingCoefficient a p ≤ (κ-a)/18 := by
  have hk : 7/10 ≤ κ := ha.trans hak
  have hDa : 0 < countingDen a p := by linarith [countingDen_lower ha hp]
  have hDk : 0 < countingDen κ p := by linarith [countingDen_lower hk hp]
  have hgap : 0 ≤ κ-a := sub_nonneg.mpr hak
  have hn : 0 ≤ 6*p*(1-p)^2 := by have hp0 := hp.1; positivity
  have hnupper : 6*p*(1-p)^2 ≤ (8:ℝ)/9 := by
    have hm : 0 ≤ (p-1/3)^2*(4/3-p) := mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hid : countingCoefficient κ p-countingCoefficient a p =
      (6*p*(1-p)^2/(countingDen κ p*countingDen a p))*(κ-a) := by
    unfold countingCoefficient
    field_simp [ne_of_gt hDa, ne_of_gt hDk]
    simp only [countingDen]
    ring
  have hDD : (17/4:ℝ)^2 ≤ countingDen κ p*countingDen a p := by
    rw [pow_two]
    exact mul_le_mul (countingDen_lower hk hp) (countingDen_lower ha hp)
      (by norm_num) (le_of_lt hDk)
  have hcoef : 6*p*(1-p)^2/(countingDen κ p*countingDen a p) ≤ (1:ℝ)/18 := by
    apply (div_le_iff₀ (mul_pos hDk hDa)).2
    nlinarith
  rw [hid]
  constructor
  · positivity
  · calc
      _ ≤ (1/18)*(κ-a) := mul_le_mul_of_nonneg_right hcoef hgap
      _ = (κ-a)/18 := by ring

theorem row_gap {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    countingR κ d p-countingR a d p ≤ (5/12)*((κ-a)/18) := by
  have hk := ha.trans hak
  have hc := counting_gap ha hak hp
  have hca : 0 ≤ countingCoefficient a p := le_of_lt (countingCoefficient_pos ha hp)
  have hck : 0 ≤ countingCoefficient κ p := le_of_lt (countingCoefficient_pos hk hp)
  have hSa := rowDen_pos ha hd hp
  have hSk := rowDen_pos hk hd hp
  have hd0 := hd.1
  have hV : 0 ≤ (5/6:ℝ)-d := by linarith
  have hSkV : (5/6:ℝ)-d ≤ rowDen κ d p := by
    unfold rowDen; nlinarith [mul_nonneg hd0 hck]
  have hSaV : (5/6:ℝ)-d ≤ rowDen a d p := by
    unfold rowDen; nlinarith [mul_nonneg hd0 hca]
  have hSS : ((5/6:ℝ)-d)^2 ≤ rowDen κ d p*rowDen a d p := by
    simpa only [pow_two] using mul_le_mul hSkV hSaV hV (le_of_lt hSk)
  have hratio : d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p) ≤ d/2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hSS hd0]
  have hid : countingR κ d p-countingR a d p =
      (d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p))*
        (countingCoefficient κ p-countingCoefficient a p) := by
    unfold countingR
    field_simp [ne_of_gt hSa, ne_of_gt hSk]
    simp only [rowDen]
    ring
  rw [hid]
  calc
    _ ≤ (d/2)*(countingCoefficient κ p-countingCoefficient a p) :=
      mul_le_mul_of_nonneg_right hratio hc.1
    _ ≤ (5/12)*(countingCoefficient κ p-countingCoefficient a p) :=
      mul_le_mul_of_nonneg_right (by linarith) hc.1
    _ ≤ (5/12)*((κ-a)/18) := mul_le_mul_of_nonneg_left hc.2 (by norm_num)


noncomputable def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)

noncomputable def rowExponentAt (κ d C δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
  d*(1/4+3*countingR κ δ p/4-17/50)-δ*p*C/2

noncomputable def newExponentAt (κ d δ p : ℝ) : ℝ :=
  rowExponentAt κ d (newCapacity d) δ p

noncomputable def oldExponentAt (κ d δ p : ℝ) : ℝ :=
  rowExponentAt κ d (oldCapacityAt κ d) δ p

theorem countingR_at_base {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    countingR kappaStar δ p = detectorR δ p := by
  rw [detectorR_eq_original hδ hp]
  unfold countingR rowDen
  rw [canonical_counting_formula kappaStar_mem.1]
  rfl

theorem newExponentAt_base {d δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt kappaStar d δ p = newExponent d δ p := by
  unfold newExponentAt newExponent rowExponentAt rowExponent
  rw [countingR_at_base hδ hp]

theorem oldExponentAt_base {d δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt kappaStar d δ p = oldExponent d δ p := by
  unfold oldExponentAt oldExponent rowExponentAt rowExponent oldCapacityAt oldCapacity
  rw [countingR_at_base hδ hp]

theorem newCapacity_nonneg {d : ℝ} (hd : d ∈ Set.Icc 0 dPlus) :
    0 ≤ newCapacity d := by
  have hc : 0 < 2-B := by norm_num [B]
  have hb := mul_le_mul_of_nonneg_left hd.2 hc.le
  unfold newCapacity
  apply div_nonneg _ lambda_pos.le
  norm_num [y, B, dPlus] at hb ⊢
  linarith

theorem oldCapacityAt_nonneg {κ d : ℝ} (hk : 7/10 ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) : 0 ≤ oldCapacityAt κ d := by
  unfold oldCapacityAt
  apply div_nonneg
  · apply le_min hd.1
    have hdm : dMinus < 2*y := by norm_num [dMinus, y]
    linarith [hd.2]
  · linarith

theorem oldCapacityAt_le_base {κ d : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) : oldCapacityAt κ d ≤ oldCapacity d := by
  have hm : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have hdm : dMinus < 2*y := by norm_num [dMinus, y]
    linarith [hd.2]
  unfold oldCapacityAt oldCapacity
  exact div_le_div_of_nonneg_left hm (by norm_num [kappaStar]) (by linarith)

theorem junction_capacityAt_margin {κ : ℝ} (hk : kappaStar ≤ κ) :
    76393262157133576883/65152954267200000000000 ≤
      newCapacity dMinus-oldCapacityAt κ dMinus := by
  have hc := oldCapacityAt_le_base hk
    (show dMinus ∈ Set.Icc 0 dMinus by constructor; norm_num [dMinus]; rfl)
  have hb := junction_capacity_difference
  linarith

theorem new_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt κ d δ p-newExponentAt kappaStar d δ p ≤ (κ-kappaStar)/50 := by
  have hgap : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hrow := row_gap kappaStar_mem.1 hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1, hδ.2]) hp
  have hR := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hcoef : 5*dPlus/288 ≤ (1:ℝ)/50 := by norm_num [dPlus]
  have hdprod := mul_le_mul_of_nonneg_right hd.2 hgap
  have hco := mul_le_mul_of_nonneg_right hcoef hgap
  unfold newExponentAt rowExponentAt
  nlinarith [hR, hdprod, hco]

theorem min_capacity_upper (d : ℝ) : min d (2*y-d) ≤ 1/2 := by
  rcases le_total d y with hd | hd
  · have hm := min_le_left d (2*y-d)
    linarith [y_lt_half]
  · have hm := min_le_right d (2*y-d)
    linarith [y_lt_half]

theorem old_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt κ d δ p-oldExponentAt kappaStar d δ p ≤ (κ-kappaStar)/8 := by
  have ha := kappaStar_mem.1
  have hk' := ha.trans hk
  have ha0 : 0 < kappaStar := by linarith
  have hk0 : 0 < κ := by linarith
  have hgap : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hrow := row_gap ha hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1, hδ.2]) hp
  have hR := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hd1 : d ≤ 1 := hd.2.trans dMinus_lt_h.le |>.trans (h_lt_dPlus.le.trans dPlus_lt_one.le)
  have hdprod := mul_le_mul_of_nonneg_right hd1 hgap
  have hprod : (7/10:ℝ)^2 ≤ κ*kappaStar := by
    rw [pow_two]
    exact mul_le_mul hk' ha (by norm_num) hk0.le
  have hinvid : 1/kappaStar-1/κ = (κ-kappaStar)/(κ*kappaStar) := by
    field_simp
  have hinv : 1/kappaStar-1/κ ≤ (κ-kappaStar)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hgap (by norm_num) hprod
  have hmin0 : 0 ≤ min d (2*y-d) := by
    apply le_min hd.1
    have := hd.2
    norm_num [dMinus, y] at *
    linarith
  have hmin := min_capacity_upper d
  have hdp : 0 ≤ δ*p := mul_nonneg hδ.1 hp.1
  have hdpupper : δ*p ≤ 3/8 := by
    have hm := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hcoef : 0 ≤ δ*p*min d (2*y-d)/12 := by positivity
  have hcoefupper : δ*p*min d (2*y-d)/12 ≤ 1/64 := by
    have hm := mul_le_mul hdpupper hmin hmin0 (by norm_num : (0:ℝ) ≤ 3/8)
    linarith
  have hI : (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) ≤
      (1/64)*((κ-kappaStar)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (δ*p*min d (2*y-d)/12)*((κ-kappaStar)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoefupper (by positivity)
  have hid : oldExponentAt κ d δ p-oldExponentAt kappaStar d δ p =
      (3*d/4)*(countingR κ δ p-countingR kappaStar δ p)+
      (δ*p*min d (2*y-d)/12)*(1/kappaStar-1/κ) := by
    unfold oldExponentAt rowExponentAt oldCapacityAt
    field_simp
    ring
  rw [hid]
  ring_nf at hR hdprod hI ⊢
  linarith only [hR, hdprod, hI, hgap]

noncomputable def rowCommon (δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p

noncomputable def newSlope (δ p : ℝ) : ℝ :=
  1/4+3*detectorR δ p/4-17/50+δ*p*(2-B)/(2*lambda)

theorem newExponent_affine (d δ p : ℝ) :
    newExponent d δ p = rowCommon δ p-δ*p*y/lambda+d*newSlope δ p := by
  unfold newExponent rowExponent rowCommon newSlope newCapacity
  ring

theorem affine_interval_lt {f : ℝ → ℝ} {a b A S M d : ℝ}
    (hf : ∀ z, f z = A+z*S) (hd : d ∈ Set.Icc a b)
    (ha : f a < M) (hb : f b < M) : f d < M := by
  simp only [hf] at ha hb ⊢
  rcases le_total 0 S with hS | hS
  · have hm := mul_le_mul_of_nonneg_right hd.2 hS
    linarith
  · have hm := mul_le_mul_of_nonpos_right hd.1 hS
    linarith

theorem newSlope_lt_two {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newSlope δ p < 2 := by
  have hR := detectorR_le_one hδ hp
  have hdp : δ*p ≤ 3/8 := by
    have hm := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hc : 0 ≤ (2-B)/(2*lambda) := by norm_num [B, lambda]
  have hm := mul_le_mul_of_nonneg_right hdp hc
  have hconst : 33/50+(3/8)*(2-B)/(2*lambda) < (2:ℝ) := by
    norm_num [B, lambda]
  unfold newSlope
  ring_nf at hm hconst ⊢
  linarith only [hm, hconst, hR]

theorem new_extended_endpoint_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dPlus δ p < theta-499/5000000000 := by
  have he := new_row_saving hδ hp
  have hs := newSlope_lt_two hδ hp
  have hgap : dPlus-h = (1:ℝ)/10000000000 := by norm_num [dPlus, h]
  have hid : newExponent dPlus δ p-newExponent h δ p =
      (dPlus-h)*newSlope δ p := by
    rw [newExponent_affine, newExponent_affine]
    ring
  rw [hgap] at hid
  nlinarith

theorem new_interval_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent d δ p < theta-499/5000000000 := by
  apply affine_interval_lt (f := fun z => newExponent z δ p)
    (A := rowCommon δ p-δ*p*y/lambda) (S := newSlope δ p)
    (fun z => newExponent_affine z δ p) hd
  · have := new_junction_saving hδ hp
    linarith
  · exact new_extended_endpoint_saving hδ hp

theorem rowExponent_capacity_antitone {d C₁ C₂ δ p : ℝ}
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hC : C₁ ≤ C₂) :
    rowExponent d C₂ δ p ≤ rowExponent d C₁ δ p := by
  have hm := mul_nonneg (mul_nonneg hδ hp) (sub_nonneg.mpr hC)
  unfold rowExponent
  nlinarith

noncomputable def oldLeftLine (d δ p : ℝ) : ℝ :=
  rowExponent d (d/(6*kappaStar)) δ p

noncomputable def oldRightLine (d δ p : ℝ) : ℝ :=
  rowExponent d ((2*y-d)/(6*kappaStar)) δ p

theorem oldLeftLine_affine (d δ p : ℝ) :
    oldLeftLine d δ p = rowCommon δ p+
      d*(1/4+3*detectorR δ p/4-17/50-δ*p/(12*kappaStar)) := by
  unfold oldLeftLine rowExponent rowCommon
  ring

theorem oldRightLine_affine (d δ p : ℝ) :
    oldRightLine d δ p = rowCommon δ p-δ*p*y/(6*kappaStar)+
      d*(1/4+3*detectorR δ p/4-17/50+δ*p/(12*kappaStar)) := by
  unfold oldRightLine rowExponent rowCommon
  ring

theorem oldLeftLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine d δ p ≤ oldExponent d δ p := by
  apply rowExponent_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_left d (2*y-d))
    (by norm_num [kappaStar])

theorem oldRightLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine d δ p ≤ oldExponent d δ p := by
  apply rowExponent_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_right d (2*y-d))
    (by norm_num [kappaStar])

theorem old_interval_of_endpoints {a b M d δ p : ℝ}
    (hd : d ∈ Set.Icc a b) (hδ : 0 ≤ δ) (hp : 0 ≤ p)
    (ha : oldExponent a δ p < M) (hb : oldExponent b δ p < M) :
    oldExponent d δ p < M := by
  have hL : oldLeftLine d δ p < M := by
    apply affine_interval_lt (f := fun z => oldLeftLine z δ p)
      (fun z => oldLeftLine_affine z δ p) hd
    · exact (oldLeftLine_le hδ hp).trans_lt ha
    · exact (oldLeftLine_le hδ hp).trans_lt hb
  have hR : oldRightLine d δ p < M := by
    apply affine_interval_lt (f := fun z => oldRightLine z δ p)
      (fun z => oldRightLine_affine z δ p) hd
    · exact (oldRightLine_le hδ hp).trans_lt ha
    · exact (oldRightLine_le hδ hp).trans_lt hb
  rcases le_total d (2*y-d) with hmin | hmin
  · simpa only [oldExponent, oldCapacity, min_eq_left hmin, oldLeftLine] using hL
  · simpa only [oldExponent, oldCapacity, min_eq_right hmin, oldRightLine] using hR

theorem old_lower_endpoint_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent d0 δ p < theta-1/10 := by
  have hC : 0 ≤ oldCapacity d0 := by
    simpa only [oldCapacity, oldCapacityAt] using
      oldCapacityAt_nonneg kappaStar_mem.1
        (show d0 ∈ Set.Icc 0 dMinus by norm_num [d0, dMinus])
  have hdrop := mul_nonneg (mul_nonneg hδ.1 hp.1) hC
  have hR := detectorR_le_one hδ hp
  have hRprod := mul_le_mul_of_nonneg_left hR d0_pos.le
  have hdp : δ*p ≤ 3/8 := by
    have hm := mul_le_mul hδ.2 hp.2 hp.1 (by norm_num : (0:ℝ) ≤ 3/4)
    norm_num at hm
    exact hm
  have hellprod := mul_le_mul_of_nonneg_left hdp ell_pos.le
  have hcoarse : oldExponent d0 δ p ≤
      7/8-49*h/150+7*ell/8+33*d0/50 := by
    unfold oldExponent rowExponent
    have hy := y_eq
    nlinarith [hδ.2]
  have hreserve : theta-(7/8-49*h/150+7*ell/8+33*d0/50) =
      82516499/750000000 := by norm_num [theta, h, ell, d0]
  linarith

theorem old_below_half_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 (1/2)) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p < theta-1/1000 := by
  apply old_interval_of_endpoints hd hδ.1 hp.1
  · have := old_lower_endpoint_saving hδ hp
    linarith
  · exact old_half_saving hδ hp

theorem oldExponent_above_half {d δ p : ℝ} (hd : 1/2 ≤ d) :
    oldExponent d δ p = oldRightLine d δ p := by
  have hmin : 2*y-d ≤ d := by linarith [y_lt_half]
  simp only [oldExponent, oldCapacity, min_eq_right hmin, oldRightLine]

theorem old_above_half_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc (1/2) dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p < theta-1/100000 := by
  rw [oldExponent_above_half hd.1]
  apply affine_interval_lt (f := fun z => oldRightLine z δ p)
    (fun z => oldRightLine_affine z δ p) hd
  · have hh := old_half_saving hδ hp
    rw [oldExponent_above_half (by norm_num : (1/2:ℝ) ≤ 1/2)] at hh
    linarith
  · have hh := old_junction_saving hδ hp
    rw [oldExponent_above_half half_lt_dMinus.le] at hh
    exact hh

theorem old_interval_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p < theta-1/100000 := by
  apply old_interval_of_endpoints hd hδ.1 hp.1
  · have := old_lower_endpoint_saving hδ hp
    linarith
  · exact old_junction_saving hδ hp

theorem supremum_kappa_mem {β : ℝ} (hβ : theta < β) (hβupper : β ≤ 7/8) :
    kappaStar ≤ 2*β-1 ∧ 2*β-1 ≤ 3/4 := by
  rw [kappaStar_eq]
  constructor <;> linarith

theorem new_supremum_feedback {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc 0 dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-newExponent d δ p ≤ (β-theta)/25 := by
  have hk : kappaStar ≤ 2*β-1 := by rw [kappaStar_eq]; linarith
  have hf := new_feedback hk hd hδ hp
  rw [newExponentAt_base hδ hp, kappaStar_eq] at hf
  linarith

theorem old_supremum_feedback {β d δ p : ℝ} (hβ : theta < β)
    (hd : d ∈ Set.Icc 0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-oldExponent d δ p ≤ (β-theta)/4 := by
  have hk : kappaStar ≤ 2*β-1 := by rw [kappaStar_eq]; linarith
  have hf := old_feedback hk hd hδ hp
  rw [oldExponentAt_base hδ hp, kappaStar_eq] at hf
  linarith

theorem new_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc dMinus dPlus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β <
      -(499/5000000000)-(24/25)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dPlus :=
    ⟨(by have := hd.1; norm_num [dMinus] at *; linarith), hd.2⟩
  have hk := supremum_kappa_mem hβ hβupper
  have hf := new_feedback hk.1 hd' hδ hp
  rw [newExponentAt_base hδ hp, kappaStar_eq] at hf
  have hb := new_interval_saving hd hδ hp
  linarith

theorem old_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β < -(1/100000)-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dMinus := ⟨d0_pos.le.trans hd.1, hd.2⟩
  have hk := supremum_kappa_mem hβ hβupper
  have hf := old_feedback hk.1 hd' hδ hp
  rw [oldExponentAt_base hδ hp, kappaStar_eq] at hf
  have hb := old_interval_saving hd hδ hp
  linarith

theorem old_below_half_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc d0 (1/2))
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β < -(1/1000)-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dMinus :=
    ⟨d0_pos.le.trans hd.1, hd.2.trans half_lt_dMinus.le⟩
  have hk := supremum_kappa_mem hβ hβupper
  have hf := old_feedback hk.1 hd' hδ hp
  rw [oldExponentAt_base hδ hp, kappaStar_eq] at hf
  have hb := old_below_half_saving hd hδ hp
  linarith

theorem new_supremum_saving {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc dMinus dPlus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p < β-499/5000000000 := by
  have := new_supremum_deficit hβ hβupper hd hδ hp
  linarith

theorem old_supremum_saving {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p < β-1/100000 := by
  have := old_supremum_deficit hβ hβupper hd hδ hp
  linarith

end Cycle63.Arithmetic.Bernstein

#print axioms Cycle63.Arithmetic.Bernstein.new_supremum_deficit
#print axioms Cycle63.Arithmetic.Bernstein.old_supremum_deficit
