import Candidate.Cycle63.CountAffine.RegionFacts
import Candidate.Cycle63.Arithmetic.Constants

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle63.Arithmetic.Bernstein

noncomputable section
open scoped Classical

def detectorV (δ : ℝ) : ℝ := 5/6-δ

def detectorD (p : ℝ) : ℝ := 3-p-2*p/(3*kappaStar)

def detectorP (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappaStar))

def clearedDenominator (δ p : ℝ) : ℝ := detectorV δ * detectorD p + δ * detectorP p

def detectorCapacity (p : ℝ) : ℝ := detectorP p / detectorD p

/-- Collet's detector count at the base parameter. -/
def detectorROld (δ p : ℝ) : ℝ :=
  1-δ+δ*detectorP p*detectorV δ/(2*clearedDenominator δ p)

/-- The detector count at the base parameter, with the affine plain branch on the staircase
region of `CountAffine`. -/
def detectorR (δ p : ℝ) : ℝ :=
  if CountAffine.inRegion δ p then min (detectorROld δ p) (CountAffine.newBranch kappaStar δ p)
  else detectorROld δ p

def newCapacity (d : ℝ) : ℝ := (2*y-(2-B)*d)/lambda

def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappaStar)

/-- The row exponent at an explicit count exponent `R`. -/
def rowExponentR (d C R δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
  d*(1/4+3*R/4-17/50)-δ*p*C/2

def rowExponent (d C δ p : ℝ) : ℝ := rowExponentR d C (detectorR δ p) δ p

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
  norm_num [detectorD, kappaStar, theta]
  linarith [hp.2]

theorem detectorP_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) :
    0 ≤ detectorP p := by
  have h1 : 0 ≤ 1-p := by linarith [hp.2]
  have h2 : 0 ≤ 1-p/(3*kappaStar) := by
    norm_num [kappaStar, theta]
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

theorem detectorROld_eq_original {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorROld δ p = 1-δ+
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
  unfold detectorROld detectorCapacity clearedDenominator
  field_simp [hd, hj, hquot]

theorem detectorP_le_two {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorP p ≤ 2 := by
  have hp0 := hp.1
  have hp1 : 0 ≤ 1/2-p := by linarith [hp.2]
  have hp2 := mul_nonneg hp0 hp1
  norm_num [detectorP, kappaStar, theta]
  nlinarith

theorem detectorROld_le_one {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorROld δ p ≤ 1 := by
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
  unfold detectorROld
  linarith

theorem detectorR_le_old (δ p : ℝ) : detectorR δ p ≤ detectorROld δ p := by
  unfold detectorR
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem detectorR_le_one {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    detectorR δ p ≤ 1 :=
  (detectorR_le_old δ p).trans (detectorROld_le_one hδ hp)

theorem rowExponentR_mono {d C R₁ R₂ δ p : ℝ} (hd : 0 ≤ d) (hR : R₁ ≤ R₂) :
    rowExponentR d C R₁ δ p ≤ rowExponentR d C R₂ δ p := by
  unfold rowExponentR
  nlinarith

theorem clearedPolynomial_eq (d C saving δ p : ℝ)
    (hJ : clearedDenominator δ p ≠ 0) :
    clearedPolynomial d C saving δ p =
      clearedDenominator δ p * (theta-saving-rowExponentR d C (detectorROld δ p) δ p) := by
  unfold clearedPolynomial rowExponentR detectorROld
  field_simp [hJ]
  ring

theorem old_saving_of_cleared_pos {d C saving δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hF : 0 < clearedPolynomial d C saving δ p) :
    rowExponentR d C (detectorROld δ p) δ p < theta-saving := by
  have hj := clearedDenominator_pos hδ hp
  rw [clearedPolynomial_eq d C saving δ p hj.ne'] at hF
  have := (mul_pos_iff_of_pos_left hj).mp hF
  linarith

/-! Certificates. Outside the region the old count is used; on the region the new branch, the
largest of the affine closed form, the capped closed form and the old plain moment at the window
top. Every numerical fact is checked by the kernel-evaluated Bernstein test `rat_pos` over the
enclosures of the computed parameters. -/

/-- Outside the region, a point of the domain lies in one of three boxes. -/
theorem outside_cases {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hreg : ¬ CountAffine.inRegion δ p) :
    (δ ∈ Set.Icc (0:ℝ) (44/100) ∧ p ∈ Set.Icc (0:ℝ) (1/2)) ∨
    (δ ∈ Set.Icc (44/100:ℝ) (49/100) ∧ p ∈ Set.Icc (0:ℝ) (495/1000)) ∨
    (δ ∈ Set.Icc (49/100:ℝ) (3/4) ∧ p ∈ Set.Icc (0:ℝ) (1/2)) := by
  unfold CountAffine.inRegion at hreg
  rcases le_total δ (44/100) with a | a
  · exact Or.inl ⟨⟨hδ.1, a⟩, hp⟩
  rcases le_total δ (49/100) with b | b
  · refine Or.inr (Or.inl ⟨⟨a, b⟩, ⟨hp.1, ?_⟩⟩)
    by_contra hc
    exact hreg ⟨a, b, (lt_of_not_ge hc).le, hp.2⟩
  · exact Or.inr (Or.inr ⟨⟨b, hδ.2⟩, hp⟩)

/-- At the junction the old capacity is the `2y - d` branch. -/
theorem oldCapacity_junction : oldCapacity dMinus = (2*y - dMinus)/(6*kappaStar) := by
  unfold oldCapacity
  rw [min_eq_right]
  linarith [y_lt_half, half_lt_dMinus]

/-- The closed-form count, cleared by its positive denominator. -/
theorem rstar_cleared_eq (d C saving δ p : ℝ) (hD : CountAffine.tDen δ p ≠ 0) :
    CountAffine.tDen δ p * (theta-saving-rowExponentR d C (CountAffine.RStar δ p) δ p) =
      CountAffine.tDen δ p*(theta-saving-((1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
        d*(1/4-17/50)-δ*p*C/2))-3*d/4*(CountAffine.tDen δ p/6+(5/6-δ)*CountAffine.tNum δ p) := by
  unfold rowExponentR CountAffine.RStar CountAffine.tStar
  field_simp
  ring

theorem rstarC_cleared_eq (d C saving δ p : ℝ) (hD : CountAffine.tDenC δ p ≠ 0) :
    CountAffine.tDenC δ p * (theta-saving-rowExponentR d C (CountAffine.RStarC δ p) δ p) =
      CountAffine.tDenC δ p*(theta-saving-((1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
        d*(1/4-17/50)-δ*p*C/2))-3*d/4*(CountAffine.tDenC δ p/6+(5/6-δ)*CountAffine.tNumC δ p) := by
  unfold rowExponentR CountAffine.RStarC CountAffine.tStarC
  field_simp
  ring

theorem rstar_row_of_pos {d C saving δ p : ℝ} (hreg : CountAffine.inRegion δ p)
    (hpos : 0 < CountAffine.tDen δ p*(theta-saving-((1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
        d*(1/4-17/50)-δ*p*C/2))-3*d/4*(CountAffine.tDen δ p/6+(5/6-δ)*CountAffine.tNum δ p)) :
    rowExponentR d C (CountAffine.RStar δ p) δ p < theta-saving := by
  have hD := (CountAffine.facts_of_region hreg).den
  rw [← rstar_cleared_eq d C saving δ p hD.ne'] at hpos
  have := (mul_pos_iff_of_pos_left hD).mp hpos
  linarith

theorem rstarC_row_of_pos {d C saving δ p : ℝ} (hreg : CountAffine.inRegion δ p)
    (hpos : 0 < CountAffine.tDenC δ p*(theta-saving-((1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+
        d*(1/4-17/50)-δ*p*C/2))-3*d/4*(CountAffine.tDenC δ p/6+(5/6-δ)*CountAffine.tNumC δ p)) :
    rowExponentR d C (CountAffine.RStarC δ p) δ p < theta-saving := by
  have hD := (CountAffine.facts_of_region hreg).denC
  rw [← rstarC_cleared_eq d C saving δ p hD.ne'] at hpos
  have := (mul_pos_iff_of_pos_left hD).mp hpos
  linarith

/-- On the region the row exponent is below `theta - saving` when all three branches are. -/
theorem region_row_bound {d C saving δ p : ℝ} (hd : 0 ≤ d) (hreg : CountAffine.inRegion δ p)
    (h1 : rowExponentR d C (CountAffine.RStar δ p) δ p < theta-saving)
    (h2 : rowExponentR d C (CountAffine.RStarC δ p) δ p < theta-saving)
    (h3 : rowExponentR d C (CountAffine.plainOld kappaStar δ p CountAffine.plainTop) δ p < theta-saving) :
    rowExponent d C δ p < theta-saving := by
  have hle : detectorR δ p ≤ CountAffine.newBranch kappaStar δ p := by
    unfold detectorR
    rw [ite_eq_left hreg]
    exact min_le_right _ _
  have hm := rowExponentR_mono (C := C) (δ := δ) (p := p) hd hle
  unfold rowExponent
  unfold CountAffine.newBranch at hm
  have hmax : rowExponentR d C (max (max (CountAffine.RStar δ p) (CountAffine.RStarC δ p))
      (CountAffine.plainOld kappaStar δ p CountAffine.plainTop)) δ p < theta - saving := by
    rcases le_total (CountAffine.RStar δ p) (CountAffine.RStarC δ p) with ha | ha
    · rw [max_eq_right ha]
      rcases le_total (CountAffine.RStarC δ p)
          (CountAffine.plainOld kappaStar δ p CountAffine.plainTop) with hb | hb
      · rw [max_eq_right hb]; exact h3
      · rw [max_eq_left hb]; exact h2
    · rw [max_eq_left ha]
      rcases le_total (CountAffine.RStar δ p)
          (CountAffine.plainOld kappaStar δ p CountAffine.plainTop) with hb | hb
      · rw [max_eq_right hb]; exact h3
      · rw [max_eq_left hb]; exact h1
  linarith

/-! The top row's affine closed form, the binding certificate. At the amplitude `1/2` the row
exponent is `theta` minus the top-row margin of `Optimization.TopRow`, which at the optimal row
length `hStar` is at least `(theta - thetaMin) (9 λ + 6 λ δ + 12 δ)/(3 λ)` by the exact quadratic
identity `margin_hStar_lower`; below `1/2` the exponent is smaller. -/

theorem tDen_half_eq (δ : ℝ) :
    CountAffine.tDen δ (1/2) = δ*Optimization.cutoffDen lambda δ/(6*lambda) := by
  have hl : lambda ≠ 0 := lambda_pos.ne'
  unfold CountAffine.tDen CountAffine.sI CountAffine.sP Optimization.cutoffDen
  field_simp
  ring

theorem tNum_half_eq (δ : ℝ) :
    CountAffine.tNum δ (1/2) =
      δ*(25/2*lambda - 10 + (6 - 6*lambda - 3*B)*δ)/(6*lambda) := by
  have hl : lambda ≠ 0 := lambda_pos.ne'
  unfold CountAffine.tNum CountAffine.sI CountAffine.sP CountAffine.aP
  field_simp
  ring

theorem RStar_half_eq {δ : ℝ} (hδ : 0 < δ) (hd : 0 < Optimization.cutoffDen lambda δ) :
    CountAffine.RStar δ (1/2) = Optimization.count lambda B δ := by
  have hl : 0 < lambda := lambda_pos
  have ht : CountAffine.tStar δ (1/2) = Optimization.cutoff lambda B δ := by
    unfold CountAffine.tStar
    rw [tNum_half_eq, tDen_half_eq]
    unfold Optimization.cutoff
    unfold Optimization.cutoffDen at hd ⊢
    field_simp
  unfold CountAffine.RStar Optimization.count
  rw [ht]

theorem top_exponent_half_eq (δ : ℝ) :
    rowExponentR h (newCapacity h) (Optimization.count lambda B δ) δ (1/2) =
      theta - Optimization.margin theta lambda B δ h := by
  unfold rowExponentR newCapacity Optimization.margin y ell
  ring

theorem top_margin_half {δ : ℝ} (hδ : δ ∈ Set.Icc (44/100:ℝ) (49/100)) :
    topSaving < Optimization.margin theta lambda B δ h := by
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hlam : 0 < lambda := by linarith [hl.1]
  have ha : Optimization.rootA2 lambda B < 0 := by
    unfold Optimization.rootA2; rat_pos [hl, hB]
  have hdisc : 0 < Optimization.rootDisc lambda B := by
    unfold Optimization.rootDisc discrim Optimization.rootA2 Optimization.rootA1 Optimization.rootA0
    rat_pos [hl, hB]
  have hδs : 0 ≤ Optimization.deltaStar lambda B := le_trans (by norm_num) deltaStar_bounds.1
  have hth := thetaClass_bounds
  have hhs := h_bounds
  unfold h at hhs
  have hk : 0 ≤ Optimization.kappa2 lambda B := by
    apply le_of_lt
    unfold Optimization.kappa2 Optimization.rootA2
    rat_pos [hl, hB, hth, hhs]
  have hd : 0 < Optimization.cutoffDen lambda δ := by
    unfold Optimization.cutoffDen; rat_pos [hδ, hl]
  have hlow := Optimization.margin_hStar_lower (θ := theta) hlam ha.ne hdisc hδs hk
    (by linarith [hδ.1]) hd
  have hgap := claimMargin_pos
  have hfac : 3 < (9*lambda + 6*lambda*δ + 12*δ)/(3*lambda) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hδ.1]
  have hh : h = Optimization.hStar lambda B := rfl
  rw [← hh, mul_div_assoc] at hlow
  have hprod : claimMargin*3 < claimMargin*((9*lambda + 6*lambda*δ + 12*δ)/(3*lambda)) :=
    mul_lt_mul_of_pos_left hfac hgap
  unfold topSaving
  unfold claimMargin at hprod ⊢
  linarith

/-- At the junction the new capacity exceeds the old one. -/
theorem junction_capacity_order : oldCapacity dMinus ≤ newCapacity dMinus := by
  rw [oldCapacity_junction]
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hh := h_bounds
  have hdm := dMinus_bounds
  apply le_of_lt
  unfold newCapacity y ell kappaStar theta
  rat_pos [hl, hB, hh, hdm]

end
end Cycle63.Arithmetic.Bernstein
