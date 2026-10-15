import Candidate.Cycle62.Arithmetic.Bernstein.MarkedPolynomials
import Candidate.Cycle62.Arithmetic.Constants

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle62.Arithmetic.Bernstein

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
    clearedPolynomial h (newCapacity h) (1/10000000) δ p = newRow δ p := by
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    newCapacity, theta, h, y, ell, B, lambda, kappaStar, newRow]
  ring

theorem oldJunction_binding (δ p : ℝ) :
    clearedPolynomial dMinus (oldCapacity dMinus) (1/100000) δ p =
      oldJunction δ p := by
  have hmin : min dMinus (2*y-dMinus) = 2*y-dMinus := by
    apply min_eq_right
    norm_num [dMinus, y]
  rw [oldCapacity, hmin]
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    theta, dMinus, y, ell, h, kappaStar, oldJunction]
  ring

theorem oldHalf_binding (δ p : ℝ) :
    clearedPolynomial (1/2) (oldCapacity (1/2)) (1/1000) δ p = oldHalf δ p := by
  have hmin : min (1/2 : ℝ) (2*y-1/2) = 2*y-1/2 := by
    apply min_eq_right
    norm_num [y]
  rw [oldCapacity, hmin]
  norm_num [clearedPolynomial, clearedDenominator, detectorV, detectorD, detectorP,
    theta, y, ell, h, kappaStar, oldHalf]
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
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent h δ p < theta-1/10000000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [newRow_binding]
  exact newRow_pos hδ hp

theorem old_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent dMinus δ p < theta-1/100000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [oldJunction_binding]
  exact oldJunction_pos hδ hp

theorem old_half_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent (1/2) δ p < theta-1/1000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [oldHalf_binding]
  exact oldHalf_pos hδ hp

theorem junction_capacity_difference : newCapacity dMinus-oldCapacity dMinus =
    356696454352782967/325766596320000000000 := by
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
end Cycle62.Arithmetic.Bernstein

#print axioms Cycle62.Arithmetic.Bernstein.new_row_saving
#print axioms Cycle62.Arithmetic.Bernstein.new_junction_saving
#print axioms Cycle62.Arithmetic.Bernstein.old_half_saving
