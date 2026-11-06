/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B001
import Candidate.Bundles.B021

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.Rectangle; sha256 b16c98546861d3ce41e0523b1acefb4f29667e30e6960bb9b29eedc17a7aa06f -/
section
                                          
                                               
                                           

namespace Cycle61.Arithmetic.Bernstein

theorem six_box_cover {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) :
    (δ ∈ Set.Icc 0 (3/8) ∧ p ∈ Set.Icc 0 (1/2)) ∨
    (δ ∈ Set.Icc (3/8) (3/4) ∧ p ∈ Set.Icc 0 (1/4)) ∨
    (δ ∈ Set.Icc (3/8) (9/16) ∧ p ∈ Set.Icc (1/4) (3/8)) ∨
    (δ ∈ Set.Icc (3/8) (15/32) ∧ p ∈ Set.Icc (3/8) (1/2)) ∨
    (δ ∈ Set.Icc (15/32) (9/16) ∧ p ∈ Set.Icc (3/8) (1/2)) ∨
    (δ ∈ Set.Icc (9/16) (3/4) ∧ p ∈ Set.Icc (1/4) (1/2)) := by
  rcases le_total δ (3/8) with hd | hd
  · exact Or.inl ⟨⟨hδ.1, hd⟩, hp⟩
  · right
    rcases le_total p (1/4) with hp' | hp'
    · exact Or.inl ⟨⟨hd, hδ.2⟩, hp.1, hp'⟩
    · right
      rcases le_total δ (9/16) with hd' | hd'
      · rcases le_total p (3/8) with hp'' | hp''
        · exact Or.inl ⟨⟨hd, hd'⟩, hp', hp''⟩
        · right
          rcases le_total δ (15/32) with hd'' | hd''
          · exact Or.inl ⟨⟨hd, hd''⟩, hp'', hp.2⟩
          · exact Or.inr (Or.inl ⟨⟨hd'', hd'⟩, hp'', hp.2⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨⟨hd', hδ.2⟩, hp', hp.2⟩))

theorem newRowPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < newRowPower δ p := by
  rcases six_box_cover hδ hp with h | h | h | h | h | h
  · exact newRowBox0_pos h.1 h.2
  · exact newRowBox1_pos h.1 h.2
  · exact newRowBox2_pos h.1 h.2
  · exact newRowBox3_pos h.1 h.2
  · exact newRowBox4_pos h.1 h.2
  · exact newRowBox5_pos h.1 h.2

theorem oldJunctionPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldJunctionPower δ p := by
  rcases six_box_cover hδ hp with h | h | h | h | h | h
  · exact oldJunctionBox0_pos h.1 h.2
  · exact oldJunctionBox1_pos h.1 h.2
  · exact oldJunctionBox2_pos h.1 h.2
  · exact oldJunctionBox3_pos h.1 h.2
  · exact oldJunctionBox4_pos h.1 h.2
  · exact oldJunctionBox5_pos h.1 h.2

theorem oldHalfPower_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldHalfPower δ p :=
  oldHalfBox0_pos hδ hp

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Rectangle -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.Endpoint; sha256 5401429d36dfe8f6b799e81ab8b3ed53973e7a475967767c3a8fb2f022cc2971 -/
section
                                             
                                   

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

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
    (23114485 / 11245794) ≤ detectorD p := by
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
    (23114485 / 134949528) ≤ clearedDenominator δ p := by
  have hv := detectorV_lower hδ
  have hd := detectorD_lower hp
  have hprod := mul_le_mul hv hd (by norm_num : (0:ℝ) ≤ (23114485 / 11245794))
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
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent h δ p < theta-1/1000000 := by
  apply row_saving_of_cleared_pos hδ hp
  rw [newRow_binding]
  exact newRowPower_pos hδ hp

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

theorem junction_capacity_difference : newCapacity dMinus-oldCapacity dMinus =
    (23754265843943127740033 / 22886596514250000000000000) := by
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
end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Endpoint -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.Bernstein.Feedback; sha256 c9fe88300e1ead59d23c0a5398808d79423caf0bd49e54288981898743e4ece1 -/
section
                                            

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Cycle61.Arithmetic.Bernstein

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
    (23754265843943127740033 / 22886596514250000000000000) ≤
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
    newExponent dPlus δ p < theta-4999/5000000000 := by
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
    newExponent d δ p < theta-4999/5000000000 := by
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
      (82193986363 / 750000000000) := by norm_num [theta, h, ell, d0]
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
      -(4999/5000000000)-(24/25)*(β-theta) := by
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
    newExponentAt (2*β-1) d δ p < β-4999/5000000000 := by
  have := new_supremum_deficit hβ hβupper hd hδ hp
  linarith

theorem old_supremum_saving {β d δ p : ℝ} (hβ : theta < β)
    (hβupper : β ≤ 7/8) (hd : d ∈ Set.Icc d0 dMinus)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponentAt (2*β-1) d δ p < β-1/100000 := by
  have := old_supremum_deficit hβ hβupper hd hδ hp
  linarith

end Cycle61.Arithmetic.Bernstein

end
/- END ORIGINAL Cycle61.Arithmetic.Bernstein.Feedback -/

/- BEGIN ORIGINAL Cycle61.Physical.WitnessGeometry; sha256 605120109eac6415693381d579fa2efb9d44d5fb65224029657921882f914796 -/
section
                                            
                                      

namespace Cycle61.Physical

open Arithmetic Arithmetic.Bernstein

noncomputable section

def witnessCutoff (κ delta p : ℝ) : ℝ :=
  1 + delta * countingCoefficient κ p / (2 * rowDen κ delta p)

def rStar (κ p t : ℝ) : ℝ :=
  (2 * (1 - p / (3 * κ)) * t + p / (3 * κ) - p) /
    (3 - p - 2 * p / (3 * κ))

-- These predecessor results are variable-κ arithmetic, with no moment premise.
theorem rStar_eq_crossing (κ p t : ℝ) :
    rStar κ p t = OAI.SevenEighths.Cycle25DetectorRowCount.crossing p κ t := by
  unfold rStar OAI.SevenEighths.Cycle25DetectorRowCount.crossing
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator
    OAI.SevenEighths.Cycle25DetectorRowCount.b
  ring

theorem coefficient_eq_old {κ p : ℝ} (hk : 7 / 10 ≤ κ) :
    countingCoefficient κ p = OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p κ := by
  simpa only [OAI.SevenEighths.Cycle25DetectorRowCount.coefficient,
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight,
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator,
    OAI.SevenEighths.Cycle25DetectorRowCount.b, mul_div_assoc] using
      canonical_counting_formula hk

theorem witnessCutoff_bounds {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    1 ≤ witnessCutoff κ delta p ∧ witnessCutoff κ delta p ≤ 3 / 2 := by
  have hc := countingCoefficient_pos hk hp
  have hden := rowDen_pos hk (show 0 ≤ delta ∧ delta ≤ 5 / 6 by constructor <;> linarith) hp
  have hdc := mul_nonneg hd.1 hc.le
  have hV : 0 ≤ 5 / 6 - delta := by linarith
  unfold witnessCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hdc (by linarith))
  · have hratio : delta * countingCoefficient κ p / (2 * rowDen κ delta p) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 2 * rowDen κ delta p)).mpr
      unfold rowDen
      linarith
    linarith

theorem witness_crossing_bounds {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    13 / 21 ≤ rStar κ p (witnessCutoff κ delta p) ∧
      rStar κ p (witnessCutoff κ delta p) ≤ 1 ∧
      1 / 3 ≤ witnessCutoff κ delta p - rStar κ p (witnessCutoff κ delta p) ∧
      witnessCutoff κ delta p - rStar κ p (witnessCutoff κ delta p) ≤ 1 / 2 := by
  have ht := witnessCutoff_bounds hk.1 hd hp
  rw [rStar_eq_crossing]
  have hr := OAI.SevenEighths.Cycle25DetectorRowCount.crossing_bounds
    hp.1 hp.2 hk.1 hk.2 ht.1 ht.2
  exact ⟨by linarith [hr.1], hr.2.1, hr.2.2⟩

theorem witness_envelope {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    1 - delta + delta * countingCoefficient κ p * (3 / 2 - witnessCutoff κ delta p) =
      countingR κ delta p ∧
    1 - delta + (5 / 6 - delta) * (witnessCutoff κ delta p - 1) =
      countingR κ delta p := by
  have hn := ne_of_gt (rowDen_pos hk
    (show 0 ≤ delta ∧ delta ≤ 5 / 6 by constructor <;> linarith) hp)
  unfold witnessCutoff countingR
  constructor
  · field_simp [hn]
    unfold rowDen
    ring
  · ring

theorem witness_crossing_identity {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    let t := witnessCutoff κ delta p
    let r := rStar κ p t
    (1 - delta * p - (delta - delta * p) * r = countingR κ delta p) ∧
    (1 - delta * p / (3 * κ) - 2 * (delta - delta * p / (3 * κ)) * (t - r) =
      countingR κ delta p) := by
  dsimp only
  have hD : OAI.SevenEighths.Cycle25DetectorRowCount.denominator p κ ≠ 0 := by
    have := OAI.SevenEighths.Cycle25DetectorRowCount.denominator_lower hp.1 hp.2 hk.1 hk.2
    linarith
  have henv := (witness_envelope hk.1 hd hp).1
  rw [coefficient_eq_old hk.1] at henv
  have hi := OAI.SevenEighths.Cycle25DetectorRowCount.inverse_at_crossing
    delta p κ (witnessCutoff κ delta p) hD
  have hplain := OAI.SevenEighths.Cycle25DetectorRowCount.plain_at_crossing
    delta p κ (witnessCutoff κ delta p) hD
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.inverseExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.shortExponent at hi
  unfold OAI.SevenEighths.Cycle25DetectorRowCount.plainExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.shortExponent
    OAI.SevenEighths.Cycle25DetectorRowCount.b at hplain
  rw [rStar_eq_crossing]
  constructor
  · linarith
  · convert hplain.trans henv using 1
    ring

theorem witness_capacities {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) :
    let t := witnessCutoff κ delta p
    let r := rStar κ p t
    (0 ≤ (1 - r) / 2 ∧ (1 - r) / 2 ≤ 4 / 21) ∧
    (0 ≤ (1 - 2 * (t - r)) / (6 * κ) ∧
      (1 - 2 * (t - r)) / (6 * κ) ≤ 1 / 12) := by
  dsimp only
  have hr := witness_crossing_bounds hk hd hp
  have hden : 0 < 6 * κ := by linarith [hk.1]
  refine ⟨⟨by linarith [hr.2.1], by linarith [hr.1]⟩, ?_, ?_⟩
  · exact div_nonneg (by linarith [hr.2.2.2]) hden.le
  · apply (div_le_iff₀ hden).mpr
    linarith [hr.2.2.1, hk.1]

theorem inverse_decrement_margins {κ delta p : ℝ}
    (hk : 7 / 10 ≤ κ ∧ κ ≤ 3 / 4) (hd : 0 ≤ delta ∧ delta ≤ 3 / 4)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) (nu : ℝ) :
    let r := rStar κ p (witnessCutoff κ delta p)
    let z := (1 - r) / 2 - nu
    (1 - (r + 2 * z) = 2 * nu) ∧
    (3 - (2 * r + 8 * z) = 8 * nu + (2 * r - 1)) ∧
    8 * nu + 5 / 21 ≤ 3 - (2 * r + 8 * z) := by
  dsimp only
  have hr := (witness_crossing_bounds hk hd hp).1
  refine ⟨by ring, by ring, ?_⟩
  linarith

end

end Cycle61.Physical

#print axioms Cycle61.Physical.witness_crossing_bounds
#print axioms Cycle61.Physical.witness_envelope
#print axioms Cycle61.Physical.witness_crossing_identity
#print axioms Cycle61.Physical.witness_capacities
#print axioms Cycle61.Physical.inverse_decrement_margins

end
/- END ORIGINAL Cycle61.Physical.WitnessGeometry -/
