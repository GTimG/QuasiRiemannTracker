import Candidate.Cycle63.Arithmetic.Bernstein.EndpointRows

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Cycle63.Arithmetic.Bernstein
open scoped Classical

/- The generic counting_gap and row_gap algebra is adapted from
Cycle25/Arithmetic/Perturbation.lean. Its endpoint theorems are not imported. -/

noncomputable def countingDen (κ p : ℝ) : ℝ := 3*κ*(3-p)-2*p
/-- Cκ(p), with the inner divisions cleared. -/
noncomputable def countingCoefficient (κ p : ℝ) : ℝ :=
  2*(1-p)*(3*κ-p)/countingDen κ p
noncomputable def rowDen (κ d p : ℝ) : ℝ := (5/6-d)+d*countingCoefficient κ p
/-- Collet's detector count exponent Rκ(δ,p). -/
noncomputable def countingROld (κ d p : ℝ) : ℝ :=
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

theorem row_gap_old {a κ d p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    countingROld κ d p-countingROld a d p ≤ (5/12)*((κ-a)/18) := by
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
  have hid : countingROld κ d p-countingROld a d p =
      (d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p))*
        (countingCoefficient κ p-countingCoefficient a p) := by
    unfold countingROld
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

/-- The detector count exponent: Collet's count, improved on the region of `CountAffine` by the
branch whose plain witnesses use the interior affine moment. -/
noncomputable def countingR (κ d p : ℝ) : ℝ :=
  if CountAffine.inRegion d p then min (countingROld κ d p) (CountAffine.newBranch κ d p)
  else countingROld κ d p

/-- The old plain moment just above the affine window rises slowly with κ on the region. -/
theorem plainTop_gap {a κ d p : ℝ} (ha : kappaStar ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 49/100) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    CountAffine.plainOld κ d p CountAffine.plainTop-CountAffine.plainOld a d p CountAffine.plainTop ≤
      (5/12)*((κ-a)/18) := by
  have hk0 : (749/1000:ℝ) ≤ kappaStar := by norm_num [kappaStar, theta]
  have ha0 : 0 < a := by linarith
  have hk0' : 0 < κ := by linarith
  have hq : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hq1 : d*p ≤ 49/200 := by nlinarith [hd.2, hp.2]
  have hid : CountAffine.plainOld κ d p CountAffine.plainTop-CountAffine.plainOld a d p CountAffine.plainTop =
      (2*(d*p)*(1-2*CountAffine.plainTop)/(6*a*κ))*(κ-a) := by
    unfold CountAffine.plainOld
    field_simp
    ring
  rw [hid]
  have hgap : 0 ≤ κ-a := by linarith
  have haκ : (749/1000:ℝ)*(749/1000) ≤ a*κ := by nlinarith
  have hw : 1-2*CountAffine.plainTop = 97/625 := by unfold CountAffine.plainTop; norm_num
  have hcoef : 2*(d*p)*(1-2*CountAffine.plainTop)/(6*a*κ) ≤ (5/12)*(1/18) := by
    rw [hw, div_le_iff₀ (by positivity)]
    nlinarith
  calc (2*(d*p)*(1-2*CountAffine.plainTop)/(6*a*κ))*(κ-a) ≤ ((5/12)*(1/18))*(κ-a) :=
        mul_le_mul_of_nonneg_right hcoef hgap
    _ = (5/12)*((κ-a)/18) := by ring

theorem row_gap {a κ d p : ℝ} (ha : kappaStar ≤ a) (hak : a ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    countingR κ d p-countingR a d p ≤ (5/12)*((κ-a)/18) := by
  have ha7 : 7/10 ≤ a := (kappaStar_mem.1).trans ha
  have hold := row_gap_old ha7 hak hd hp
  unfold countingR
  by_cases hreg : CountAffine.inRegion d p
  · rw [ite_eq_left hreg, ite_eq_left hreg]
    have hb := CountAffine.inRegion_bounds hreg
    have hpo := plainTop_gap ha hak ⟨hd.1, hb.2.1⟩ hp
    have hnb : CountAffine.newBranch κ d p-CountAffine.newBranch a d p ≤ (5/12)*((κ-a)/18) := by
      unfold CountAffine.newBranch
      set X := max (CountAffine.RStar d p) (CountAffine.RStarC d p)
      have hmono : CountAffine.plainOld a d p CountAffine.plainTop ≤
          CountAffine.plainOld κ d p CountAffine.plainTop := by
        have hk0 : 0 < a := by linarith [kappaStar_mem.1]
        unfold CountAffine.plainOld
        have hq : 0 ≤ d*p := mul_nonneg hd.1 hp.1
        have hw : 0 ≤ 1-2*CountAffine.plainTop := by unfold CountAffine.plainTop; norm_num
        have hfrac : 2*(d*p)*(1-2*CountAffine.plainTop)/(6*κ) ≤
            2*(d*p)*(1-2*CountAffine.plainTop)/(6*a) := by
          apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        linarith
      have hz : 0 ≤ (5/12)*((κ-a)/18) := by
        have : 0 ≤ κ-a := by linarith
        positivity
      rcases le_total X (CountAffine.plainOld a d p CountAffine.plainTop) with h1 | h1
      · rw [max_eq_right h1, max_eq_right (h1.trans hmono)]
        exact hpo
      · rw [max_eq_left h1]
        rcases le_total X (CountAffine.plainOld κ d p CountAffine.plainTop) with h2 | h2
        · rw [max_eq_right h2]; linarith
        · rw [max_eq_left h2]; linarith
    rcases le_total (countingROld a d p) (CountAffine.newBranch a d p) with h1 | h1
    · rw [min_eq_left h1]
      have : min (countingROld κ d p) (CountAffine.newBranch κ d p) ≤ countingROld κ d p := min_le_left _ _
      linarith
    · rw [min_eq_right h1]
      have : min (countingROld κ d p) (CountAffine.newBranch κ d p) ≤ CountAffine.newBranch κ d p :=
        min_le_right _ _
      linarith
  · rw [ite_eq_right hreg, ite_eq_right hreg]
    exact hold

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
  have hold : countingROld kappaStar δ p = detectorROld δ p := by
    rw [detectorROld_eq_original hδ hp]
    unfold countingROld rowDen
    rw [canonical_counting_formula kappaStar_mem.1]
    rfl
  unfold countingR detectorR
  rw [hold]

theorem newExponentAt_base {d δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt kappaStar d δ p = newExponent d δ p := by
  unfold newExponentAt newExponent rowExponentAt rowExponent rowExponentR
  rw [countingR_at_base hδ hp]

theorem oldExponentAt_base {d δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt kappaStar d δ p = oldExponent d δ p := by
  unfold oldExponentAt oldExponent rowExponentAt rowExponent rowExponentR oldCapacityAt oldCapacity
  rw [countingR_at_base hδ hp]

theorem dMinus_lt_two_y : dMinus < 2*y := by
  linarith [dMinus_lt_h, h_lt_two_y]

theorem oldCapacityAt_nonneg {κ d : ℝ} (hk : 7/10 ≤ κ)
    (hd : d ∈ Set.Icc 0 dMinus) : 0 ≤ oldCapacityAt κ d := by
  unfold oldCapacityAt
  apply div_nonneg
  · apply le_min hd.1
    linarith [hd.2, dMinus_lt_two_y]
  · linarith

theorem new_feedback {κ d δ p : ℝ} (hk : kappaStar ≤ κ)
    (hd : d ∈ Set.Icc 0 dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt κ d δ p-newExponentAt kappaStar d δ p ≤ (κ-kappaStar)/50 := by
  have hgap : 0 ≤ κ-kappaStar := sub_nonneg.mpr hk
  have hrow := row_gap le_rfl hk
    (show 0 ≤ δ ∧ δ ≤ 5/6 by constructor <;> linarith [hδ.1, hδ.2]) hp
  have hR := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3*d/4 by linarith [hd.1])
  have hcoef : 5*dPlus/288 ≤ (1:ℝ)/50 := by linarith [dPlus_lt_one]
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
  have hrow := row_gap le_rfl hk
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
    linarith [hd.2, dMinus_lt_two_y]
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
  unfold newExponent rowExponent rowExponentR rowCommon newSlope newCapacity
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
  have hl := lambda_bounds
  have hc0 : 0 ≤ (2-B)/(2*lambda) := div_nonneg (by linarith [CountAffine.B_bounds.2]) (by linarith)
  have hc1 : (2-B)/(2*lambda) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [CountAffine.B_bounds.1]
  have hm := mul_le_mul hdp hc1 hc0 (by norm_num : (0:ℝ) ≤ 3/8)
  have hsplit : δ*p*(2-B)/(2*lambda) = δ*p*((2-B)/(2*lambda)) := by ring
  unfold newSlope
  rw [hsplit]
  linarith

theorem new_extended_endpoint_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dPlus δ p < theta-rowSaving := by
  have he := new_row_saving hδ hp
  have hs := newSlope_lt_two hδ hp
  have hgap : dPlus-h = dPlusOffset := by unfold dPlus; ring
  have hid : newExponent dPlus δ p-newExponent h δ p =
      (dPlus-h)*newSlope δ p := by
    rw [newExponent_affine, newExponent_affine]
    ring
  rw [hgap] at hid
  have hm := mul_lt_mul_of_pos_left hs dPlusOffset_pos
  have hr := rowSaving_add
  linarith

theorem new_interval_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc dMinus dPlus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent d δ p < theta-rowSaving := by
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
  unfold rowExponent rowExponentR
  nlinarith

noncomputable def oldLeftLine (d δ p : ℝ) : ℝ :=
  rowExponent d (d/(6*kappaStar)) δ p

noncomputable def oldRightLine (d δ p : ℝ) : ℝ :=
  rowExponent d ((2*y-d)/(6*kappaStar)) δ p

theorem oldLeftLine_affine (d δ p : ℝ) :
    oldLeftLine d δ p = rowCommon δ p+
      d*(1/4+3*detectorR δ p/4-17/50-δ*p/(12*kappaStar)) := by
  unfold oldLeftLine rowExponent rowExponentR rowCommon
  ring

theorem oldRightLine_affine (d δ p : ℝ) :
    oldRightLine d δ p = rowCommon δ p-δ*p*y/(6*kappaStar)+
      d*(1/4+3*detectorR δ p/4-17/50+δ*p/(12*kappaStar)) := by
  unfold oldRightLine rowExponent rowExponentR rowCommon
  ring

theorem oldLeftLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldLeftLine d δ p ≤ oldExponent d δ p := by
  apply rowExponent_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_left d (2*y-d))
    (by linarith [kappaStar_mem.1])

theorem oldRightLine_le {d δ p : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) :
    oldRightLine d δ p ≤ oldExponent d δ p := by
  apply rowExponent_capacity_antitone hδ hp
  exact div_le_div_of_nonneg_right (min_le_right d (2*y-d))
    (by linarith [kappaStar_mem.1])

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
    oldExponent d0 δ p < theta-rowSaving := by
  have hC : 0 ≤ oldCapacity d0 := by
    simpa only [oldCapacity, oldCapacityAt] using
      oldCapacityAt_nonneg kappaStar_mem.1
        ⟨d0_pos.le, by unfold d0; linarith [half_lt_dMinus]⟩
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
    unfold oldExponent rowExponent rowExponentR
    have hy := y_eq
    nlinarith [hδ.2]
  have hreserve : 7/8-49*h/150+7*ell/8+33*d0/50 < theta-rowSaving := by
    rw [ell_eq]
    unfold d0 theta
    linarith [h_bounds.1, rowSaving_bounds.2]
  linarith

theorem old_interval_saving {d δ p : ℝ}
    (hd : d ∈ Set.Icc d0 dMinus) (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldExponent d δ p < theta-rowSaving := by
  apply old_interval_of_endpoints hd hδ.1 hp.1
  · have := old_lower_endpoint_saving hδ hp
    linarith
  · exact old_junction_saving hδ hp

theorem supremum_kappa_mem {β : ℝ} (hβ : theta < β) (hβupper : β ≤ 7/8) :
    kappaStar ≤ 2*β-1 ∧ 2*β-1 ≤ 3/4 := by
  rw [kappaStar_eq]
  constructor <;> linarith

theorem new_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc dMinus dPlus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentAt (2*β-1) d δ p-β <
      -rowSaving-(24/25)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dPlus :=
    ⟨by linarith [hd.1, half_lt_dMinus], hd.2⟩
  have hk := supremum_kappa_mem hβ hβupper
  have hf := new_feedback hk.1 hd' hδ hp
  rw [newExponentAt_base hδ hp, kappaStar_eq] at hf
  have hb := new_interval_saving hd hδ hp
  linarith

theorem old_supremum_deficit {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p-β < -rowSaving-(3/4)*(β-theta) := by
  have hd' : d ∈ Set.Icc 0 dMinus := ⟨d0_pos.le.trans hd.1, hd.2⟩
  have hk := supremum_kappa_mem hβ hβupper
  have hf := old_feedback hk.1 hd' hδ hp
  rw [oldExponentAt_base hδ hp, kappaStar_eq] at hf
  have hb := old_interval_saving hd hδ hp
  linarith

end Cycle63.Arithmetic.Bernstein
