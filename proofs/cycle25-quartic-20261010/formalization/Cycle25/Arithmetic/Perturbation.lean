import Cycle25.Arithmetic.GlobalBound

namespace Cycle25.Arithmetic

noncomputable def countingDen (κ p : ℝ) : ℝ := 3*κ*(3-p)-2*p
/-- B0.5's Cκ(p), with the inner divisions cleared. -/
noncomputable def countingCoefficient (κ p : ℝ) : ℝ :=
  2*(1-p)*(3*κ-p)/countingDen κ p
noncomputable def rowDen (κ d p : ℝ) : ℝ := (5/6-d)+d*countingCoefficient κ p
/-- The row exponent Rκ(δ,p) of B0.40. -/
noncomputable def rowExponent (κ d p : ℝ) : ℝ :=
  1-d+d*countingCoefficient κ p*(5/6-d)/(2*rowDen κ d p)
/-- The full endpoint Fκ^(4) of B0.47. -/
noncomputable def fullBoundary (κ d p : ℝ) : ℝ :=
  (1+ell0)/2+d/2+h0*(3*rowExponent κ d p/4-5/12)+
    d*p*(ell0-(h0-4*ell0)/(12*κ))

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

theorem rowExponent_eq_certR {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    rowExponent kappa0 d p = certR d (1/2-p) := by
  have hk : (7:ℝ)/10 ≤ kappa0 := le_of_lt kappa0_range.1
  have hD : countingDen kappa0 p ≠ 0 := ne_of_gt (by linarith [countingDen_lower hk hp])
  have hS : rowDen kappa0 d p ≠ 0 := ne_of_gt (rowDen_pos hk hd hp)
  have hu : 0 ≤ (1/2:ℝ)-p ∧ (1/2:ℝ)-p ≤ 1/2 := by constructor <;> linarith
  have hJ : certJ d (1/2-p) ≠ 0 := ne_of_gt (by linarith [(certJ_bounds hd hu).1])
  unfold rowExponent certR
  field_simp [hS, hJ]
  unfold rowDen countingCoefficient
  field_simp [hD]
  simp only [countingDen, certJ, certB]
  ring_nf
  field_simp (disch := first | assumption | (solve | norm_num) |
    (convert hJ using 1; simp only [certJ]; ring))
  ring

theorem fullBoundary_kappa0 {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary kappa0 d p = boundaryF d p := by
  unfold fullBoundary boundaryF certT
  rw [rowExponent_eq_certR hd hp]

theorem fullBoundary_binding : fullBoundary kappa0 delta0 (1/2) = b0 := by
  have hd : 0 ≤ delta0 ∧ delta0 ≤ 5/6 := by
    constructor <;> linarith [delta0_interval.1, delta0_interval.2]
  rw [fullBoundary_kappa0 hd ⟨by norm_num, le_refl _⟩]
  exact boundaryF_binding

theorem fullBoundary_eq_iff {d p : ℝ} (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary kappa0 d p = b0 ↔ d = delta0 ∧ p = 1/2 := by
  rw [fullBoundary_kappa0 hd hp]
  exact boundaryF_eq_iff hd hp

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
    rowExponent κ d p-rowExponent a d p ≤ (5/12)*((κ-a)/18) := by
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
  have hid : rowExponent κ d p-rowExponent a d p =
      (d*((5/6:ℝ)-d)^2/(2*rowDen κ d p*rowDen a d p))*
        (countingCoefficient κ p-countingCoefficient a p) := by
    unfold rowExponent
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

/-- T1.3 proved by finite differences; no differentiation or limiting argument
is needed for the uniform perturbation used by the contradiction. -/
theorem fullBoundary_gap {κ d p : ℝ} (hk : kappa0 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary κ d p-fullBoundary kappa0 d p ≤ (κ-kappa0)/10 := by
  have hk0 : (7:ℝ)/10 ≤ kappa0 := le_of_lt kappa0_range.1
  have hk' : (7:ℝ)/10 ≤ κ := hk0.trans hk
  have ha0 : 0 < kappa0 := by linarith
  have hb0 : 0 < κ := by linarith
  have hgap : 0 ≤ κ-kappa0 := sub_nonneg.mpr hk
  have hh0 : 0 ≤ h0 := by linarith [h0_interval.1]
  have hg := derivative_geometry
  have hreserve : 0 ≤ h0-4*ell0 := le_of_lt hg.2.1
  have hrow := row_gap hk0 hk hd hp
  have hR : 3*h0/4*(rowExponent κ d p-rowExponent kappa0 d p) ≤
      (3/4)*(4/5)*(5/12)*((κ-kappa0)/18) := by
    calc
      _ ≤ (3*h0/4)*((5/12)*((κ-kappa0)/18)) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
      _ ≤ (3/4)*(4/5)*(5/12)*((κ-kappa0)/18) := by
        nlinarith [mul_nonneg (show 0 ≤ 4/5-h0 by linarith [hg.1]) hgap]
  have hprod : (7/10:ℝ)^2 ≤ κ*kappa0 := by
    rw [pow_two]
    exact mul_le_mul hk' hk0 (by norm_num) (le_of_lt hb0)
  have hinvid : 1/kappa0-1/κ = (κ-kappa0)/(κ*kappa0) := by
    field_simp
  have hinv : 1/kappa0-1/κ ≤ (κ-kappa0)/((7/10:ℝ)^2) := by
    rw [hinvid]
    exact div_le_div_of_nonneg_left hgap (by norm_num) hprod
  have hdp : 0 ≤ d*p := mul_nonneg hd.1 hp.1
  have hdp' : d*p ≤ (5:ℝ)/12 := by
    have hm := mul_le_mul hd.2 hp.2 hp.1 (show (0:ℝ) ≤ 5/6 by norm_num)
    norm_num at hm
    exact hm
  have hcoef : 0 ≤ d*p*(h0-4*ell0)/12 := by positivity
  have hcoef' : d*p*(h0-4*ell0)/12 ≤ (5/12)*(13/100)/12 := by
    have hm := mul_le_mul hdp' (le_of_lt hg.2.2) hreserve (show (0:ℝ) ≤ 5/12 by norm_num)
    linarith
  have hinv0 : 0 ≤ (κ-kappa0)/((7/10:ℝ)^2) := by positivity
  have hI : (d*p*(h0-4*ell0)/12)*(1/kappa0-1/κ) ≤
      ((5/12)*(13/100)/12)*((κ-kappa0)/((7/10:ℝ)^2)) := by
    calc
      _ ≤ (d*p*(h0-4*ell0)/12)*((κ-kappa0)/((7/10:ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hinv hcoef
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef' hinv0
  have hid : fullBoundary κ d p-fullBoundary kappa0 d p =
      (3*h0/4)*(rowExponent κ d p-rowExponent kappa0 d p)+
        (d*p*(h0-4*ell0)/12)*(1/kappa0-1/κ) := by
    unfold fullBoundary
    field_simp
    ring
  have hconst : (3/4:ℝ)*(4/5)*(5/12)*(1/18)+(5/12)*(13/100)/(12*(7/10)^2) ≤ 1/10 := by
    norm_num
  have hm := mul_le_mul_of_nonneg_right hconst hgap
  rw [hid]
  ring_nf at hR hI hm ⊢
  linarith only [hR, hI, hm]

theorem fullBoundary_uniform {κ d p : ℝ} (hk : kappa0 ≤ κ)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary κ d p ≤ b0+(κ-kappa0)/10 := by
  have hgap := fullBoundary_gap hk hd hp
  rw [fullBoundary_kappa0 hd hp] at hgap
  linarith [boundaryF_le_b0 hd hp]

theorem supremum_improvement {β d p : ℝ} (hβ : b0 < β)
    (hd : 0 ≤ d ∧ d ≤ 5/6) (hp : 0 ≤ p ∧ p ≤ 1/2) :
    fullBoundary (2*β-1) d p-β ≤ -(4/5)*(β-b0) := by
  have hk : kappa0 ≤ 2*β-1 := by rw [kappa0_eq]; linarith
  have hF := fullBoundary_uniform hk hd hp
  rw [kappa0_eq] at hF
  linarith

end Cycle25.Arithmetic
