import Candidate.Cycle63.Arithmetic.Bernstein.MarkedPolynomials
import Candidate.Cycle63.Arithmetic.Constants
import Candidate.Affine.Region
section
                                             
                                   

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle63.Arithmetic.Bernstein

noncomputable section

def detectorV (δ : ℝ) : ℝ := 5/6-δ

def detectorD (p : ℝ) : ℝ := 3-p-2*p/(3*kappaStar)

def detectorP (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappaStar))

def clearedDenominator (δ p : ℝ) : ℝ := detectorV δ * detectorD p + δ * detectorP p

def detectorCapacity (p : ℝ) : ℝ := detectorP p / detectorD p

def detectorR (δ p : ℝ) : ℝ :=
  1-δ+δ*detectorP p*detectorV δ/(2*clearedDenominator δ p)

def newCapacity (d : ℝ) : ℝ := (2*y-(2-B)*d)/lambda

def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappaStar)

def rowExponent (d C δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
  d*(1/4+3*detectorR δ p/4-17/50)-δ*p*C/2

def newExponent (d δ p : ℝ) : ℝ := rowExponent d (newCapacity d) δ p

def oldExponent (d δ p : ℝ) : ℝ := rowExponent d (oldCapacity d) δ p

def clearedPolynomial (d C saving δ p : ℝ) : ℝ :=
  clearedDenominator δ p *
    (theta-saving-(1+δ)/2-13*h/75+y/2+ell/2-ell*δ*p-
      d*(1/4-17/50)+δ*p*C/2) -
  3*d/4*((1-δ)*clearedDenominator δ p+δ*detectorP p*detectorV δ/2)

theorem detectorV_lower {δ : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) :
    1/12 ≤ detectorV δ := by
  unfold detectorV
  linarith [hδ.2]

theorem detectorD_lower {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) :
    2 ≤ detectorD p := by
  norm_num [detectorD, kappaStar]
  linarith [hp.2]

theorem detectorP_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) :
    0 ≤ detectorP p := by
  have h1 : 0 ≤ 1-p := by linarith [hp.2]
  have h2 : 0 ≤ 1-p/(3*kappaStar) := by
    norm_num [kappaStar]
    linarith [hp.2]
  exact mul_nonneg (mul_nonneg (by norm_num) h1) h2

theorem clearedDenominator_lower {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    1/6 ≤ clearedDenominator δ p := by
  have hv := detectorV_lower hδ
  have hd := detectorD_lower hp
  have hprod := mul_le_mul hv hd (by norm_num : (0:ℝ) ≤ 2)
    (by linarith : 0 ≤ detectorV δ)
  have hδp := mul_nonneg hδ.1 (detectorP_nonneg hp)
  unfold clearedDenominator
  nlinarith

theorem clearedDenominator_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < clearedDenominator δ p := by
  have := clearedDenominator_lower hδ hp
  linarith

theorem clearedDenominator_gt_tenth {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    1/10 < clearedDenominator δ p := by
  have := clearedDenominator_lower hδ hp
  norm_num at *
  linarith

theorem detectorR_eq_original {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorR δ p = 1-δ+
      δ*detectorCapacity p*detectorV δ/(2*(detectorV δ+δ*detectorCapacity p)) := by
  have hd : detectorD p ≠ 0 := by have := detectorD_lower hp; linarith
  have hj := (clearedDenominator_pos hδ hp).ne'
  have hquot : detectorV δ+δ*detectorCapacity p ≠ 0 := by
    intro he
    apply hj
    unfold detectorCapacity at he
    field_simp [hd] at he
    unfold clearedDenominator
    nlinarith [he]
  unfold detectorCapacity at hquot
  unfold clearedDenominator at hj
  unfold detectorR detectorCapacity clearedDenominator
  field_simp [hd, hj, hquot]

theorem detectorP_le_two {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorP p ≤ 2 := by
  have hp0 := hp.1
  have hp1 : 0 ≤ 1/2-p := by linarith [hp.2]
  have hp2 := mul_nonneg hp0 hp1
  norm_num [detectorP, kappaStar]
  nlinarith

theorem detectorR_le_one {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorR δ p ≤ 1 := by
  have hv : 0 ≤ detectorV δ := by have := detectorV_lower hδ; linarith
  have hd := detectorD_lower hp
  have hp2 := detectorP_le_two hp
  have hpd : detectorP p ≤ 2*detectorD p := by linarith
  have hpv := mul_le_mul_of_nonneg_right hpd hv
  have hj := clearedDenominator_pos hδ hp
  have hδp := mul_nonneg hδ.1 (detectorP_nonneg hp)
  have hden : detectorV δ*detectorD p ≤ clearedDenominator δ p := by
    unfold clearedDenominator
    linarith
  have hpvj : detectorP p*detectorV δ ≤ 2*clearedDenominator δ p := by
    nlinarith [hpv]
  have hm := mul_le_mul_of_nonneg_left hpvj hδ.1
  have hratio : δ*detectorP p*detectorV δ/(2*clearedDenominator δ p) ≤ δ := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hj)).mpr
    nlinarith [hm]
  unfold detectorR
  linarith

theorem clearedPolynomial_eq (d C saving δ p : ℝ)
    (hJ : clearedDenominator δ p ≠ 0) :
    clearedPolynomial d C saving δ p =
      clearedDenominator δ p * (theta-saving-rowExponent d C δ p) := by
  unfold clearedPolynomial rowExponent detectorR
  field_simp [hJ]
  ring

theorem newRow_binding (δ p : ℝ) :
    clearedPolynomial h (newCapacity h) (1/1000000) δ p = newRowPower δ p := by
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    newCapacity, theta, h, y, ell, B, lambda, kappaStar, newRowPower]
  ring

theorem oldJunction_binding (δ p : ℝ) :
    clearedPolynomial dMinus (oldCapacity dMinus) (1/100000) δ p =
      oldJunctionPower δ p := by
  have hmin : min dMinus (2*y-dMinus) = 2*y-dMinus := by
    apply min_eq_right
    norm_num [dMinus, y]
  rw [oldCapacity, hmin]
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    theta, dMinus, y, ell, h, kappaStar, oldJunctionPower]
  ring

theorem oldHalf_binding (δ p : ℝ) :
    clearedPolynomial (1/2) (oldCapacity (1/2)) (1/1000) δ p = oldHalfPower δ p := by
  have hmin : min (1/2 : ℝ) (2*y-1/2) = 2*y-1/2 := by
    apply min_eq_right
    norm_num [y]
  rw [oldCapacity, hmin]
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    theta, y, ell, h, kappaStar, oldHalfPower]
  ring

theorem row_saving_of_cleared_pos {d C saving δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hF : 0 < clearedPolynomial d C saving δ p) :
    rowExponent d C δ p < theta-saving := by
  have hj := clearedDenominator_pos hδ hp
  rw [clearedPolynomial_eq d C saving δ p hj.ne'] at hF
  have := (mul_pos_iff_of_pos_left hj).mp hF
  linarith

theorem new_row_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hreg : ¬ DetectorAffine.InRegion δ p) :
    newExponent h δ p < theta-1/1000000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [newRow_binding]
  exact newRowPower_pos hδ hp hreg

theorem old_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent dMinus δ p < theta-1/100000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [oldJunction_binding]
  exact oldJunctionPower_pos hδ hp

theorem old_half_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent (1/2) δ p < theta-1/1000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [oldHalf_binding]
  exact oldHalfPower_pos hδ hp

/-- The detector count with the affine plain capacity on the region. -/
def detectorRA (δ p : ℝ) : ℝ :=
  if DetectorAffine.InRegion δ p then DetectorAffine.RNew δ p else detectorR δ p

def rowExponentA (d C δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
  d*(1/4+3*detectorRA δ p/4-17/50)-δ*p*C/2

def newExponentA (d δ p : ℝ) : ℝ := rowExponentA d (newCapacity d) δ p

def oldExponentA (d δ p : ℝ) : ℝ := rowExponentA d (oldCapacity d) δ p

theorem detectorR_eq_ROld {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorR δ p = DetectorAffine.ROld δ p := by
  rw [detectorR_eq_original hδ hp]
  have hk : (3:ℝ)*kappaStar ≠ 0 := by norm_num [kappaStar]
  have hD : 3-p-2*p/(3*kappaStar) ≠ 0 := by
    have := detectorD_lower hp; unfold detectorD at this; linarith
  have hc : detectorCapacity p = DetectorAffine.oldNum p/DetectorAffine.oldDen p := by
    unfold detectorCapacity detectorP detectorD DetectorAffine.oldNum DetectorAffine.oldDen
      DetectorAffine.kStar
    unfold detectorD at hD
    rw [div_eq_div_iff hD (by
      have := DetectorAffine.oldDen_pos hp.1 hp.2
      unfold DetectorAffine.oldDen DetectorAffine.kStar at this; linarith)]
    norm_num [kappaStar]
    field_simp
  unfold DetectorAffine.ROld
  rw [hc]
  unfold detectorV
  ring

theorem detectorRA_le {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorRA δ p ≤ detectorR δ p := by
  unfold detectorRA
  split_ifs with hreg
  · rw [detectorR_eq_ROld hδ hp]
    exact DetectorAffine.region_compare hreg
  · exact le_rfl

theorem detectorRA_le_one {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorRA δ p ≤ 1 :=
  (detectorRA_le hδ hp).trans (detectorR_le_one hδ hp)

theorem rowExponentA_le {d C δ p : ℝ} (hd : 0 ≤ d)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    rowExponentA d C δ p ≤ rowExponent d C δ p := by
  have hR := mul_le_mul_of_nonneg_left (detectorRA_le hδ hp) hd
  unfold rowExponentA rowExponent
  nlinarith

/-- The new row closes on the affine region with the new count. -/
theorem region_row_saving {δ p : ℝ} (hreg : DetectorAffine.InRegion δ p) :
    rowExponentA h (newCapacity h) δ p < theta-1/1000000 := by
  have hJ := DetectorAffine.region_JN_pos hreg
  have hpos := DetectorAffine.regionRow_pos hreg
  rw [DetectorAffine.regionRow_binding] at hpos
  have hR := DetectorAffine.region_RNew_mul hreg
  have hRA : detectorRA δ p = DetectorAffine.RNew δ p := by
    unfold detectorRA; rw [if_pos hreg]
  have key : (theta-1/1000000-rowExponentA h (newCapacity h) δ p)*DetectorAffine.JN δ p =
      DetectorAffine.JN δ p*(21871/25000-1/1000000-(1+δ)/2-13*(1989/2500)/75+
        (17287/37500)/2+(3137/18750)/2-(3137/18750)*δ*p-(1989/2500)*(1/4-17/50)+
        δ*p*((2*(17287/37500)-(2-DetectorAffine.Bc)*(1989/2500))/DetectorAffine.lam)/2)-
      3*(1989/2500)/4*((1-δ)*DetectorAffine.JN δ p+
        (5/6-δ)*δ*(1-p)*DetectorAffine.cN p) := by
    unfold rowExponentA newCapacity
    rw [hRA]
    simp only [theta, h, y, ell, B, lambda, DetectorAffine.Bc, DetectorAffine.lam]
    linear_combination (-(3*(1989/2500)/4))*hR
  have := (mul_pos_iff_of_pos_right hJ).mp (key ▸ hpos)
  linarith

theorem new_row_savingA {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponentA h δ p < theta-1/1000000 := by
  by_cases hreg : DetectorAffine.InRegion δ p
  · exact region_row_saving hreg
  · have he : newExponentA h δ p = newExponent h δ p := by
      unfold newExponentA newExponent rowExponentA rowExponent detectorRA
      rw [if_neg hreg]
    rw [he]
    exact new_row_saving hδ hp hreg

theorem junction_capacity_difference : newCapacity dMinus-oldCapacity dMinus =
    224982742097/191618208000000 := by
  have hmin : min dMinus (2*y-dMinus) = 2*y-dMinus := by
    apply min_eq_right
    norm_num [dMinus, y]
  rw [oldCapacity, hmin]
  norm_num [newCapacity, y, B, dMinus, lambda, kappaStar]

theorem new_junction_le_old {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p ≤ oldExponent dMinus δ p := by
  have hC := junction_capacity_difference
  have hdp := mul_nonneg hδ.1 hp.1
  unfold newExponent oldExponent rowExponent
  nlinarith

theorem new_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p < theta-1/100000 :=
  (new_junction_le_old hδ hp).trans_lt (old_junction_saving hδ hp)

end
end Cycle63.Arithmetic.Bernstein

end
