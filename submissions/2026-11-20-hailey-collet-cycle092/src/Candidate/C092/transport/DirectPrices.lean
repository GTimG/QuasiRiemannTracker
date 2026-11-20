/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectModels
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Direct
noncomputable section
open QRH.Cycle090 QRH.Coverage

/-- Source and contact guards for the exact original count denominator. -/
theorem source_contact_guards :
    0 ≤ sourceCost ∧ sourceCost ≤ 1/1000000000000 ∧
    (2/3 : ℝ) ≤ kap ∧ kap ≤ 3/4 := by
  refine ⟨allowances_pos.1.le, ?_, ?_, ?_⟩
  · exact sourceCost_le_rowPad.trans rowPad_small.le
  · norm_num [kap,QRH.ContactCertificate.alphaHi]
  · norm_num [kap,QRH.ContactCertificate.alphaHi]

/-- Both authentic rational count denominators are positive and at most 5/2
throughout the entire original density-amplitude domain. -/
theorem countJ_bounds (route : CountRoute) {d p : ℝ}
    (hd : 0 ≤ d) (hd' : d ≤ 3/4) (hp : 0 ≤ p) (hp' : p ≤ 1/2) :
    0 < countJ route sourceCost kap d p ∧ countJ route sourceCost kap d p ≤ 5/2 := by
  rcases source_contact_guards with ⟨hs,hs',hk,hk'⟩
  have hv : 0 ≤ 5/6-d := by linarith
  have hv' : 1/12 ≤ 5/6-d := by linarith
  have hden : 0 < 2+10*sourceCost := by linarith
  have hratio0 : 0 ≤ 4*p/(2+10*sourceCost) := div_nonneg (by positivity) hden.le
  have hratio1 : 4*p/(2+10*sourceCost) ≤ 2*p := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have holden : 0 < 3*kap := by linarith
  have hfrac0 : 0 ≤ p/(3*kap) := div_nonneg hp holden.le
  have hfrac1 : p/(3*kap) ≤ p/2 := by
    apply (div_le_iff₀ holden).2
    nlinarith
  have htwo : 2*p/(3*kap) = 2*(p/(3*kap)) := by ring
  cases route with
  | old =>
      have hD0 : 2 ≤ 3-p-2*p/(3*kap) := by rw [htwo]; nlinarith
      have hD1 : 3-p-2*p/(3*kap) ≤ 3 := by rw [htwo]; nlinarith
      have hC0 : 0 ≤ 2*(1-p)*(1-p/(3*kap)) :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      have hC1 : 2*(1-p)*(1-p/(3*kap)) ≤ 2 := by
        nlinarith [mul_nonneg hp (by linarith : 0 ≤ 1-p/(3*kap))]
      have hJ0 := mul_le_mul_of_nonneg_left hD0 hv
      have hJ1 := mul_le_mul_of_nonneg_left hD1 hv
      have hJ2 := mul_le_mul_of_nonneg_left hC1 hd
      dsimp [countJ]
      constructor
      · nlinarith [mul_nonneg hd hC0]
      · nlinarith
  | native =>
      have hD0 : 3/2 ≤ nativeD sourceCost p := by dsimp [nativeD]; linarith
      have hD1 : nativeD sourceCost p ≤ 3 := by dsimp [nativeD]; linarith
      have hA0 : 0 ≤ (1-p)*nativeA sourceCost p := by
        have ha : 0 ≤ nativeA sourceCost p := by dsimp [nativeA]; linarith
        exact mul_nonneg (by linarith) ha
      have hA1 : (1-p)*nativeA sourceCost p ≤ 2 := by
        dsimp [nativeA]
        nlinarith [mul_nonneg hp (by linarith : 0 ≤ 4*p/(2+10*sourceCost))]
      have hJ0 := mul_le_mul_of_nonneg_left hD0 hv
      have hJ1 := mul_le_mul_of_nonneg_left hD1 hv
      have hJ2 := mul_le_mul_of_nonneg_left hA1 hd
      dsimp [countJ]
      constructor
      · nlinarith [mul_nonneg hd hA0]
      · nlinarith
  | fixedS | fixedA => norm_num [countJ]

/-- Literal capacities on the four original edges. -/
def originalCapacity (edge : Fin 4) (h : ℝ) : ℝ :=
  if edge.val < 2 then
    min (edgeD edge h) (2*(h-2*Physical.ell)-edgeD edge h)/(6*kap)
  else cappedCapacity physicalCap (h-2*Physical.ell) sourceCost (edgeD edge h)

theorem original_capacity_proxy {h : ℝ} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (edge : Fin 4) : edgeProxy edge theta kap h ≤ originalCapacity edge h := by
  rcases source_contact_guards with ⟨hs,hs',hk,hk'⟩
  fin_cases edge
  · have hm : (1/200 : ℝ) ≤ 2*(h-2*Physical.ell)-1/200 := by
      norm_num [hLower,Physical.ell,theta] at hh ⊢; linarith
    change (1/200 : ℝ)/(6*kap) ≤ min (1/200) (2*(h-2*Physical.ell)-1/200)/(6*kap)
    rw [min_eq_left hm]
  · have hm : 2*(h-2*Physical.ell)-19/25 ≤ (19/25 : ℝ) := by
      norm_num [hUpper,Physical.ell,theta] at hh' ⊢; linarith
    change (2*(h-2*Physical.ell)-19/25)/(6*kap) ≤ min (19/25 : ℝ) (2*(h-2*Physical.ell)-19/25)/(6*kap)
    rw [min_eq_right hm]
  · simp only [originalCapacity,show ¬(2 < 2) by omega,↓reduceIte,edgeD,edgeProxy]
    dsimp [cappedCapacity]
    apply le_min le_rfl
    apply (le_div_iff₀ (by linarith : 0 < 2+10*sourceCost)).2
    norm_num [Physical.ell,theta,physicalCap,hLower] at hh ⊢
    linarith
  · simpa [edgeProxy,originalCapacity,edgeD,Physical.capacityProxy,Physical.ell] using
      Physical.actual_capacity_lower hh hh'

/-- Original count and original capacity, with the full rational numerator intact. -/
def originalPrice (route : CountRoute) (edge : Fin 4) (h d p : ℝ) : ℝ :=
  1/2+13*h/75-(h-2*Physical.ell)/2-Physical.ell/2-9*edgeD edge h/100+d/2+
    d*p*(Physical.ell-originalCapacity edge h/2)+
    3*edgeD edge h*(countN route sourceCost kap d p/countJ route sourceCost kap d p)/4

/-- A regenerated cleared lower bound pays the literal original price. -/
theorem original_price_of_cleared (route : CountRoute) (edge : Fin 4)
    {h d p : ℝ} (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hd : 0 ≤ d) (hd' : d ≤ 3/4) (hp : 0 ≤ p) (hp' : p ≤ 1/2)
    (hclear : 1/1000000 ≤ cleared route edge h d p) :
    1/2500000 ≤ theta-originalPrice route edge h d p := by
  have hj := countJ_bounds route hd hd' hp hp'
  have hcap := original_capacity_proxy hh hh' edge
  have he : cleared route edge h d p = countJ route sourceCost kap d p*
      (theta-(directBase theta kap h d p edge+
        3*edgeD edge h*(countN route sourceCost kap d p/countJ route sourceCost kap d p)/4)) := by
    dsimp [cleared,directCleared]
    field_simp [ne_of_gt hj.1]
    ring
  have hpclear : 1/2500000 ≤ theta-(directBase theta kap h d p edge+
        3*edgeD edge h*(countN route sourceCost kap d p/countJ route sourceCost kap d p)/4) := by
    rw [he] at hclear
    nlinarith
  have hweight := mul_le_mul_of_nonneg_left hcap (mul_nonneg hd hp)
  dsimp [directBase,originalPrice,Physical.ell] at hpclear ⊢
  nlinarith
end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.original_price_of_cleared
