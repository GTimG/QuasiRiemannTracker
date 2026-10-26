import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Bernstein.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The count's row certificates: the old count outside the region, the three branches of the new
count on it, and the resulting row bounds of the top and junction rows. Every numerical
fact is checked by the kernel-evaluated Bernstein test `rat_pos` over the enclosures of the
computed parameters. Released under Apache 2.0. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle63.Arithmetic.Bernstein

noncomputable section
open scoped Classical

theorem topOld_outside {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hreg : ¬ CountAffine.inRegion δ p) : 0 < clearedPolynomial h (newCapacity h) topSaving δ p := by
  have hS := topSaving_bounds
  have hh := h_enclosure
  have hl := lambda_enclosure
  have hB := B_enclosure
  rcases outside_cases hδ hp hreg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · unfold clearedPolynomial clearedDenominator detectorV detectorD detectorP newCapacity y ell
      kappaStar theta
    rat_pos (depth := 30) [h1, h2, hl, hB, hh, hS]

theorem junctionOld_outside {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hreg : ¬ CountAffine.inRegion δ p) :
    0 < clearedPolynomial dMinus (oldCapacity dMinus) rowSaving δ p := by
  rw [oldCapacity_junction]
  have hh := h_bounds
  have hS := rowSaving_bounds
  have hdm := dMinus_bounds
  rcases outside_cases hδ hp hreg with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · unfold clearedPolynomial clearedDenominator detectorV detectorD detectorP y ell
      kappaStar theta
    rat_pos (depth := 30) [h1, h2, hh, hS, hdm]

/-- On the region the top row exponent of the affine closed form is largest at the amplitude
`1/2`: the linear terms grow with the amplitude faster than the closed form falls. -/
theorem top_RStar_monotone {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR h (newCapacity h) (CountAffine.RStar δ p) δ p ≤
      rowExponentR h (newCapacity h) (CountAffine.RStar δ (1/2)) δ (1/2) := by
  have hp := CountAffine.region_mem hreg
  obtain ⟨hδ, hp⟩ := hp
  have hreg' : CountAffine.inRegion δ (1/2) := CountAffine.inRegion_up hreg hp.2 le_rfl
  have hD := (CountAffine.facts_of_region hreg).den
  have hD' := (CountAffine.facts_of_region hreg').den
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hh := h_bounds
  have hcross := CountAffine.quadratic_cross (CountAffine.nA0 δ) (CountAffine.nA1 δ)
    (CountAffine.nA2 δ) (CountAffine.dA0 δ) (CountAffine.dA1 δ) (CountAffine.dA2 δ) p (1/2)
  rw [← CountAffine.tNum_quad, ← CountAffine.tNum_quad, ← CountAffine.tDen_quad,
    ← CountAffine.tDen_quad] at hcross
  have hbracket : 0 < δ*(ell - newCapacity h/2)*(CountAffine.tDen δ p*CountAffine.tDen δ (1/2)) +
      3*h/4*(5/6 - δ)*((CountAffine.nA1 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA1 δ) +
        (CountAffine.nA2 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA2 δ)*(p + 1/2) +
        (CountAffine.nA2 δ*CountAffine.dA1 δ - CountAffine.nA1 δ*CountAffine.dA2 δ)*(p*(1/2))) := by
    unfold CountAffine.tDen CountAffine.sI CountAffine.sP CountAffine.nA0 CountAffine.nA1
      CountAffine.nA2 CountAffine.dA0 CountAffine.dA1 CountAffine.dA2 newCapacity y ell theta
    rat_pos (depth := 12) [hδ, hp, hl, hB, hh]
  have hE : rowExponentR h (newCapacity h) (CountAffine.RStar δ (1/2)) δ (1/2) -
      rowExponentR h (newCapacity h) (CountAffine.RStar δ p) δ p =
      δ*(ell - newCapacity h/2)*(1/2 - p) +
        3*h/4*(5/6 - δ)*(CountAffine.tStar δ (1/2) - CountAffine.tStar δ p) := by
    unfold rowExponentR CountAffine.RStar
    ring
  have ht : CountAffine.tStar δ (1/2) - CountAffine.tStar δ p =
      (1/2 - p)*((CountAffine.nA1 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA1 δ) +
        (CountAffine.nA2 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA2 δ)*(p + 1/2) +
        (CountAffine.nA2 δ*CountAffine.dA1 δ - CountAffine.nA1 δ*CountAffine.dA2 δ)*(p*(1/2))) /
        (CountAffine.tDen δ (1/2)*CountAffine.tDen δ p) := by
    unfold CountAffine.tStar
    rw [div_sub_div _ _ hD'.ne' hD.ne', mul_comm (CountAffine.tDen δ (1/2)) (CountAffine.tNum δ p)]
    congr 1
  rw [ht] at hE
  have hq : 0 ≤ 1/2 - p := by linarith [hp.2]
  have hDD : 0 < CountAffine.tDen δ (1/2)*CountAffine.tDen δ p := mul_pos hD' hD
  have hsum : 0 ≤ δ*(ell - newCapacity h/2)*(1/2 - p) +
      3*h/4*(5/6 - δ)*((1/2 - p)*((CountAffine.nA1 δ*CountAffine.dA0 δ -
        CountAffine.nA0 δ*CountAffine.dA1 δ) +
        (CountAffine.nA2 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA2 δ)*(p + 1/2) +
        (CountAffine.nA2 δ*CountAffine.dA1 δ - CountAffine.nA1 δ*CountAffine.dA2 δ)*(p*(1/2))) /
        (CountAffine.tDen δ (1/2)*CountAffine.tDen δ p)) := by
    have hid : δ*(ell - newCapacity h/2)*(1/2 - p) +
        3*h/4*(5/6 - δ)*((1/2 - p)*((CountAffine.nA1 δ*CountAffine.dA0 δ -
          CountAffine.nA0 δ*CountAffine.dA1 δ) +
          (CountAffine.nA2 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA2 δ)*(p + 1/2) +
          (CountAffine.nA2 δ*CountAffine.dA1 δ - CountAffine.nA1 δ*CountAffine.dA2 δ)*(p*(1/2))) /
          (CountAffine.tDen δ (1/2)*CountAffine.tDen δ p)) =
        (1/2 - p)*(δ*(ell - newCapacity h/2)*(CountAffine.tDen δ p*CountAffine.tDen δ (1/2)) +
          3*h/4*(5/6 - δ)*((CountAffine.nA1 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA1 δ) +
          (CountAffine.nA2 δ*CountAffine.dA0 δ - CountAffine.nA0 δ*CountAffine.dA2 δ)*(p + 1/2) +
          (CountAffine.nA2 δ*CountAffine.dA1 δ - CountAffine.nA1 δ*CountAffine.dA2 δ)*(p*(1/2)))) /
          (CountAffine.tDen δ (1/2)*CountAffine.tDen δ p) := by
      field_simp
    rw [hid]
    exact div_nonneg (mul_nonneg hq hbracket.le) hDD.le
  linarith

theorem top_RStar_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR h (newCapacity h) (CountAffine.RStar δ p) δ p < theta - topSaving := by
  have hp := CountAffine.region_mem hreg
  obtain ⟨hδ, hp⟩ := hp
  have hl := CountAffine.lambda_mem
  have hd : 0 < Optimization.cutoffDen lambda δ := by
    unfold Optimization.cutoffDen; rat_pos [hδ, hl]
  have hmono := top_RStar_monotone hreg
  rw [RStar_half_eq (by linarith [hδ.1]) hd, top_exponent_half_eq] at hmono
  have hm := top_margin_half hδ
  linarith

/-- On the region the top row exponent of the capped closed form is largest at the amplitude
`1/2`: the linear terms grow with the amplitude faster than the closed form falls. -/
theorem top_RStarC_monotone {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR h (newCapacity h) (CountAffine.RStarC δ p) δ p ≤
      rowExponentR h (newCapacity h) (CountAffine.RStarC δ (1/2)) δ (1/2) := by
  have hp := CountAffine.region_mem hreg
  obtain ⟨hδ, hp⟩ := hp
  have hreg' : CountAffine.inRegion δ (1/2) := CountAffine.inRegion_up hreg hp.2 le_rfl
  have hD := (CountAffine.facts_of_region hreg).denC
  have hD' := (CountAffine.facts_of_region hreg').denC
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hh := h_bounds
  have hcross := CountAffine.quadratic_cross (CountAffine.nC0 δ) (CountAffine.nC1 δ)
    (CountAffine.nC2 δ) (CountAffine.dC0 δ) (CountAffine.dC1 δ) (0) p (1/2)
  rw [← CountAffine.tNumC_quad, ← CountAffine.tNumC_quad, ← CountAffine.tDenC_quad,
    ← CountAffine.tDenC_quad] at hcross
  have hbracket : 0 < δ*(ell - newCapacity h/2)*(CountAffine.tDenC δ p*CountAffine.tDenC δ (1/2)) +
      3*h/4*(5/6 - δ)*((CountAffine.nC1 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*CountAffine.dC1 δ) +
        (CountAffine.nC2 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*0)*(p + 1/2) +
        (CountAffine.nC2 δ*CountAffine.dC1 δ - CountAffine.nC1 δ*0)*(p*(1/2))) := by
    unfold CountAffine.tDenC CountAffine.sI CountAffine.sPc CountAffine.nC0 CountAffine.nC1
      CountAffine.nC2 CountAffine.dC0 CountAffine.dC1 newCapacity y ell theta
      Cycle63.Optimization.slotTop
    rat_pos (depth := 12) [hδ, hp, hl, hB, hh]
  have hE : rowExponentR h (newCapacity h) (CountAffine.RStarC δ (1/2)) δ (1/2) -
      rowExponentR h (newCapacity h) (CountAffine.RStarC δ p) δ p =
      δ*(ell - newCapacity h/2)*(1/2 - p) +
        3*h/4*(5/6 - δ)*(CountAffine.tStarC δ (1/2) - CountAffine.tStarC δ p) := by
    unfold rowExponentR CountAffine.RStarC
    ring
  have ht : CountAffine.tStarC δ (1/2) - CountAffine.tStarC δ p =
      (1/2 - p)*((CountAffine.nC1 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*CountAffine.dC1 δ) +
        (CountAffine.nC2 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*0)*(p + 1/2) +
        (CountAffine.nC2 δ*CountAffine.dC1 δ - CountAffine.nC1 δ*0)*(p*(1/2))) /
        (CountAffine.tDenC δ (1/2)*CountAffine.tDenC δ p) := by
    unfold CountAffine.tStarC
    rw [div_sub_div _ _ hD'.ne' hD.ne', mul_comm (CountAffine.tDenC δ (1/2)) (CountAffine.tNumC δ p)]
    congr 1
  rw [ht] at hE
  have hq : 0 ≤ 1/2 - p := by linarith [hp.2]
  have hDD : 0 < CountAffine.tDenC δ (1/2)*CountAffine.tDenC δ p := mul_pos hD' hD
  have hsum : 0 ≤ δ*(ell - newCapacity h/2)*(1/2 - p) +
      3*h/4*(5/6 - δ)*((1/2 - p)*((CountAffine.nC1 δ*CountAffine.dC0 δ -
        CountAffine.nC0 δ*CountAffine.dC1 δ) +
        (CountAffine.nC2 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*0)*(p + 1/2) +
        (CountAffine.nC2 δ*CountAffine.dC1 δ - CountAffine.nC1 δ*0)*(p*(1/2))) /
        (CountAffine.tDenC δ (1/2)*CountAffine.tDenC δ p)) := by
    have hid : δ*(ell - newCapacity h/2)*(1/2 - p) +
        3*h/4*(5/6 - δ)*((1/2 - p)*((CountAffine.nC1 δ*CountAffine.dC0 δ -
          CountAffine.nC0 δ*CountAffine.dC1 δ) +
          (CountAffine.nC2 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*0)*(p + 1/2) +
          (CountAffine.nC2 δ*CountAffine.dC1 δ - CountAffine.nC1 δ*0)*(p*(1/2))) /
          (CountAffine.tDenC δ (1/2)*CountAffine.tDenC δ p)) =
        (1/2 - p)*(δ*(ell - newCapacity h/2)*(CountAffine.tDenC δ p*CountAffine.tDenC δ (1/2)) +
          3*h/4*(5/6 - δ)*((CountAffine.nC1 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*CountAffine.dC1 δ) +
          (CountAffine.nC2 δ*CountAffine.dC0 δ - CountAffine.nC0 δ*0)*(p + 1/2) +
          (CountAffine.nC2 δ*CountAffine.dC1 δ - CountAffine.nC1 δ*0)*(p*(1/2)))) /
          (CountAffine.tDenC δ (1/2)*CountAffine.tDenC δ p) := by
      field_simp
    rw [hid]
    exact div_nonneg (mul_nonneg hq hbracket.le) hDD.le
  linarith

/-- A quadratic with positive leading coefficient and nonpositive discriminant is nonnegative. -/
theorem quadratic_nonneg_of_discrim {a b c x : ℝ} (ha : 0 < a) (hd : b^2 - 4*a*c ≤ 0) :
    0 ≤ a*x^2 + b*x + c := by
  have key : 4*a*(a*x^2 + b*x + c) = (2*a*x + b)^2 - (b^2 - 4*a*c) := by ring
  have h4 : 0 ≤ 4*a*(a*x^2 + b*x + c) := by rw [key]; nlinarith [sq_nonneg (2*a*x + b)]
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < 4*a)).mp h4

/-- The leading coefficient of the cleared capped margin at the window top. -/
bracket cappedA_top (digits := 12) : Optimization.cappedQuadA lambda B (Optimization.thetaMin lambda B) h
    Optimization.slotTop
  using [lambda_enclosure, B_enclosure, thetaClass_bounds, h_enclosure]
  unfolding [Optimization.cappedQuadA, Optimization.cappedLevelSlope, Optimization.ellAt,
    Optimization.slotTop]

/-- The discriminant in the zero parameter of the cleared capped margin at the window top: it is
negative, since the window top lies above the balanced top of the bin split. -/
bracket cappedDisc_top (digits := 13) :
    Optimization.cappedQuadB lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop^2 -
      4*Optimization.cappedQuadA lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop*
        Optimization.cappedQuadC (Optimization.thetaMin lambda B) h
  using [lambda_enclosure, B_enclosure, thetaClass_bounds, h_enclosure]
  unfolding [Optimization.cappedQuadA, Optimization.cappedQuadB, Optimization.cappedQuadC,
    Optimization.cappedLevelSlope, Optimization.cappedLevelConst, Optimization.ellAt,
    Optimization.slotTop]

/-- The top-row margin of the capped closed form at slot amplitude `1/2`, cleared of
`25/12 - 3 δ/2`: the capped quadratic at the class bound plus the claim margin times
`(25/12 - 3 δ/2) (2 δ + 4 δ/λ)`. -/
theorem capped_margin_identity {δ : ℝ} (hδ : 0 < δ) (hD : 0 < 25/12 - 3*δ/2) :
    (25/12 - 3*δ/2)*(theta - topSaving -
        rowExponentR h (newCapacity h) (CountAffine.RStarC δ (1/2)) δ (1/2)) =
      Optimization.cappedQuadA lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop*δ^2 +
        Optimization.cappedQuadB lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop*δ +
        Optimization.cappedQuadC (Optimization.thetaMin lambda B) h +
        claimMargin*(25/12 - 3*δ/2)*(2*δ + 4*δ/lambda) := by
  have hden : CountAffine.tDenC δ (1/2) = δ*(25/12 - 3*δ/2) := by
    unfold CountAffine.tDenC CountAffine.sI CountAffine.sPc; ring
  have hnum : CountAffine.tNumC δ (1/2) = δ*(25/12 - (1 + Optimization.slotTop/2)*δ) := by
    unfold CountAffine.tNumC CountAffine.sI CountAffine.sPc CountAffine.aPc; ring
  have hR : CountAffine.RStarC δ (1/2) =
      1/6 + (5/6 - δ)*((25/12 - (1 + Optimization.slotTop/2)*δ)/(25/12 - 3*δ/2)) := by
    unfold CountAffine.RStarC CountAffine.tStarC
    rw [hnum, hden, mul_div_mul_left _ _ hδ.ne']
  rw [hR]
  set t := (25/12 - (1 + Optimization.slotTop/2)*δ)/(25/12 - 3*δ/2) with htdef
  have ht : t*(25/12 - 3*δ/2) = 25/12 - (1 + Optimization.slotTop/2)*δ := div_mul_cancel₀ _ hD.ne'
  unfold rowExponentR newCapacity y ell topSaving claimMargin Optimization.cappedQuadA
    Optimization.cappedQuadB Optimization.cappedQuadC Optimization.cappedLevelSlope
    Optimization.cappedLevelConst Optimization.ellAt
  linear_combination (-(3*h/4)*(5/6 - δ))*ht

/-- The top-row certificate of the capped closed form at slot amplitude `1/2`: the capped quadratic
is nonnegative since its discriminant is negative at the window top, and the claim margin keeps the
margin positive. -/
theorem top_capped_half {δ : ℝ} (hδ : δ ∈ Set.Icc (43/100 : ℝ) (49/100)) :
    rowExponentR h (newCapacity h) (CountAffine.RStarC δ (1/2)) δ (1/2) < theta - topSaving := by
  have hδ0 : 0 < δ := by linarith [hδ.1]
  have hD : 0 < 25/12 - 3*δ/2 := by linarith [hδ.2]
  have hid := capped_margin_identity hδ0 hD
  have hQ := quadratic_nonneg_of_discrim
    (a := Optimization.cappedQuadA lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop)
    (b := Optimization.cappedQuadB lambda B (Optimization.thetaMin lambda B) h Optimization.slotTop)
    (c := Optimization.cappedQuadC (Optimization.thetaMin lambda B) h)
    (x := δ) (by linarith [cappedA_top.1]) (by linarith [cappedDisc_top.2])
  have hm := claimMargin_pos
  have hl := lambda_pos
  have hpos : 0 < claimMargin*(25/12 - 3*δ/2)*(2*δ + 4*δ/lambda) := by positivity
  have hprod : 0 < (25/12 - 3*δ/2)*(theta - topSaving -
      rowExponentR h (newCapacity h) (CountAffine.RStarC δ (1/2)) δ (1/2)) := by
    rw [hid]; linarith
  have := (mul_pos_iff_of_pos_left hD).mp hprod
  linarith

theorem top_RStarC_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR h (newCapacity h) (CountAffine.RStarC δ p) δ p < theta - topSaving := by
  have hmono := top_RStarC_monotone hreg
  have hhalf := top_capped_half (CountAffine.region_mem hreg).1
  linarith

theorem top_plainTop_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR h (newCapacity h) (CountAffine.plainOld kappaStar δ p CountAffine.plainTop) δ p <
      theta - topSaving := by
  have hp := CountAffine.region_mem hreg
  obtain ⟨hδ, hp⟩ := hp
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hh := h_bounds
  have hS := topSaving_bounds
  unfold rowExponentR CountAffine.plainOld CountAffine.plainTop newCapacity y ell kappaStar theta
  rat_pos (depth := 12) [hδ, hp, hl, hB, hh, hS]

theorem junction_RStar_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.RStar δ p) δ p < theta - rowSaving := by
  apply rstar_row_of_pos hreg
  rw [oldCapacity_junction]
  obtain ⟨hδ, hp⟩ := CountAffine.region_mem hreg
  have hl := CountAffine.lambda_mem
  have hB := CountAffine.B_mem
  have hh := h_bounds
  have hS := rowSaving_bounds
  have hdm := dMinus_bounds
  unfold CountAffine.tDen CountAffine.tNum CountAffine.sI CountAffine.sP CountAffine.aP
    y ell kappaStar theta
  rat_pos (depth := 24) [hδ, hp, hl, hB, hh, hS, hdm]

theorem junction_RStarC_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.RStarC δ p) δ p < theta - rowSaving := by
  apply rstarC_row_of_pos hreg
  rw [oldCapacity_junction]
  obtain ⟨hδ, hp⟩ := CountAffine.region_mem hreg
  have hh := h_bounds
  have hS := rowSaving_bounds
  have hdm := dMinus_bounds
  unfold CountAffine.tDenC CountAffine.tNumC CountAffine.sI CountAffine.sPc CountAffine.aPc
    y ell kappaStar theta Cycle63.Optimization.slotTop
  rat_pos (depth := 16) [hδ, hp, hh, hS, hdm]

theorem junction_plainTop_region {δ p : ℝ} (hreg : CountAffine.inRegion δ p) :
    rowExponentR dMinus (oldCapacity dMinus) (CountAffine.plainOld kappaStar δ p CountAffine.plainTop) δ p <
      theta - rowSaving := by
  rw [oldCapacity_junction]
  obtain ⟨hδ, hp⟩ := CountAffine.region_mem hreg
  have hh := h_bounds
  have hS := rowSaving_bounds
  have hdm := dMinus_bounds
  unfold rowExponentR CountAffine.plainOld CountAffine.plainTop y ell kappaStar theta
  rat_pos (depth := 12) [hδ, hp, hh, hS, hdm]

theorem new_row_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent h δ p < theta-topSaving := by
  have hh : (0:ℝ) ≤ h := by linarith [h_bounds.1]
  unfold newExponent
  by_cases hreg : CountAffine.inRegion δ p
  · exact region_row_bound hh hreg (top_RStar_region hreg) (top_RStarC_region hreg)
      (top_plainTop_region hreg)
  · have he : rowExponent h (newCapacity h) δ p =
        rowExponentR h (newCapacity h) (detectorROld δ p) δ p := by
      unfold rowExponent detectorR
      rw [ite_eq_right hreg]
    rw [he]
    exact old_saving_of_cleared_pos hδ hp (topOld_outside hδ hp hreg)

theorem old_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldExponent dMinus δ p < theta-rowSaving := by
  have hd : (0:ℝ) ≤ dMinus := by linarith [half_lt_dMinus]
  unfold oldExponent
  by_cases hreg : CountAffine.inRegion δ p
  · exact region_row_bound hd hreg (junction_RStar_region hreg) (junction_RStarC_region hreg)
      (junction_plainTop_region hreg)
  · have he : rowExponent dMinus (oldCapacity dMinus) δ p =
        rowExponentR dMinus (oldCapacity dMinus) (detectorROld δ p) δ p := by
      unfold rowExponent detectorR
      rw [ite_eq_right hreg]
    rw [he]
    exact old_saving_of_cleared_pos hδ hp (junctionOld_outside hδ hp hreg)

theorem new_junction_le_old {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p ≤ oldExponent dMinus δ p := by
  have hC := junction_capacity_order
  have hdp := mul_nonneg hδ.1 hp.1
  unfold newExponent oldExponent rowExponent rowExponentR
  nlinarith

theorem new_junction_saving {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    newExponent dMinus δ p < theta-rowSaving :=
  (new_junction_le_old hδ hp).trans_lt (old_junction_saving hδ hp)

end
end Cycle63.Arithmetic.Bernstein

end Record1252270103Bootstrap.PR67
