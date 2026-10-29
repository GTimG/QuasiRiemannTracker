/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RayHighCertificate

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open HighTemplates AuxHighTemplates

/-- The affine divider uses density-scaled polynomial coordinates. -/
theorem affineCapD_eq_ray (B L c a0 a1 s ν z : ℝ) (hν : ν≠0) :
 affineCapD B L c a0 a1 s ν z=
 ν*rayCapD B L c 0 ((a0+a1*ν)/ν) s ν z := by
 unfold affineCapD rayCapD
 field_simp [hν]
 <;> ring

theorem affineCapK_eq_ray (B L c a0 a1 s ν z : ℝ) (hν : ν≠0) :
 affineCapK B L c a0 a1 s ν z=
 ν*rayCapK B L c 0 ((a0+a1*ν)/ν) s ν z := by
 unfold affineCapK rayCapK
 field_simp [hν]
 <;> ring

theorem affineBudgetD_eq_ray (B L c a0 a1 s ν z : ℝ) (hν : ν≠0) (hL : L≠0) :
 affineBudgetD B L c a0 a1 s ν z=
 ν*rayBudgetD B L c 0 ((a0+a1*ν)/ν) s ν z := by
 unfold affineBudgetD rayBudgetD
 field_simp [hν,hL]
 <;> ring

theorem affineBudgetK_eq_ray (B L c a0 a1 s ν z : ℝ) (hν : ν≠0) (hL : L≠0) :
 affineBudgetK B L c a0 a1 s ν z=
 ν*rayBudgetK B L c 0 ((a0+a1*ν)/ν) s ν z := by
 unfold affineBudgetK rayBudgetK
 field_simp [hν,hL]
 <;> ring

theorem affineCapD_hasDerivAt (B L c a0 a1 s ν z : ℝ)
 (hν : ν≠0) :
 HasDerivAt (affineCapD B L c a0 a1 s ν)
   (affineCapDz B L c a0 a1 s ν z) z := by
 have hh := (rayCapD_hasDerivAt B L c ((a0+a1*ν)/ν) s ν z).const_mul ν
 convert hh using 1
 · funext x
   exact affineCapD_eq_ray B L c a0 a1 s ν x hν
 · unfold affineCapDz rayCapDz
   field_simp [hν]
   <;> ring

theorem affineCapK_hasDerivAt (B L c a0 a1 s ν z : ℝ)
 (hν : ν≠0) :
 HasDerivAt (affineCapK B L c a0 a1 s ν)
   (affineCapKz B L c a0 a1 s ν z) z := by
 have hh := (rayCapK_hasDerivAt B L c ((a0+a1*ν)/ν) s ν z).const_mul ν
 convert hh using 1
 · funext x
   exact affineCapK_eq_ray B L c a0 a1 s ν x hν
 · unfold affineCapKz rayCapKz
   field_simp [hν]
   <;> ring

theorem affineBudgetD_hasDerivAt (B L c a0 a1 s ν z : ℝ)
 (hν : ν≠0) (hL : L≠0) :
 HasDerivAt (affineBudgetD B L c a0 a1 s ν)
   (affineBudgetDz B L c a0 a1 s ν z) z := by
 have hh := (rayBudgetD_hasDerivAt B L c ((a0+a1*ν)/ν) s ν z).const_mul ν
 convert hh using 1
 · funext x
   exact affineBudgetD_eq_ray B L c a0 a1 s ν x hν hL
 · unfold affineBudgetDz rayBudgetDz
   field_simp [hν,hL]
   <;> ring

theorem affineBudgetK_hasDerivAt (B L c a0 a1 s ν z : ℝ)
 (hν : ν≠0) (hL : L≠0) :
 HasDerivAt (affineBudgetK B L c a0 a1 s ν)
   (affineBudgetKz B L c a0 a1 s ν z) z := by
 have hh := (rayBudgetK_hasDerivAt B L c ((a0+a1*ν)/ν) s ν z).const_mul ν
 convert hh using 1
 · funext x
   exact affineBudgetK_eq_ray B L c a0 a1 s ν x hν hL
 · unfold affineBudgetKz rayBudgetKz
   field_simp [hν,hL]
   <;> ring

theorem affineCap_den_pos {B L c a0 a1 s ν z : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hz : z∈Set.Icc (0:ℝ) 1) : 0<affineCapD B L c a0 a1 s ν z := by
 rw [affineCapD_eq_ray _ _ _ _ _ _ _ _ hν.ne']
 exact mul_pos hν (rayCap_den_pos hν hνhi ((div_le_one hν).2 hahi)
   (div_nonneg ha.le hν.le) hz)

theorem affineBudget_den_pos {B L c a0 a1 s ν z : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hL : 3/2≤L) (hz : z∈Set.Icc (0:ℝ) 1) : 0<affineBudgetD B L c a0 a1 s ν z := by
 have hL0 : L≠0 := by linarith
 rw [affineBudgetD_eq_ray _ _ _ _ _ _ _ _ hν.ne' hL0]
 exact mul_pos hν (rayBudget_den_pos hν hνhi ((div_le_one hν).2 hahi)
   (div_nonneg ha.le hν.le) hL hz)

theorem capCrossingRate_eq_affine {B L c a0 a1 s ν z : ℝ}
 (hν : ν≠0) (hD : affineCapD B L c a0 a1 s ν z≠0) :
 capCrossingRate c ν ((a0+a1*ν)*z/(2*ν))=
   1-affineCapK B L c a0 a1 s ν z/affineCapD B L c a0 a1 s ν z := by
 have hden : rayCapDen ν ((a0+a1*ν)/ν) z≠0 := by
  intro hh
  apply hD
  rw [affineCapD_eq_ray _ _ _ _ _ _ _ _ hν,rayCapD_eq_den,hh,mul_zero]
 have hr := capCrossingRate_eq_ray (c:=c) hden
 have hp : ((a0+a1*ν)/ν)*z/2=(a0+a1*ν)*z/(2*ν) := by field_simp [hν]
 rw [hp] at hr
 rw [affineCapK_eq_ray _ _ _ _ _ _ _ _ hν,
   affineCapD_eq_ray _ _ _ _ _ _ _ _ hν,rayCapK_eq_save,rayCapD_eq_den]
 convert hr using 1 <;> field_simp [hν,hden] <;> ring

theorem budgetCrossingRate_eq_affine {B L c a0 a1 s ν z : ℝ}
 (hν : ν≠0) (hL : L≠0) (hD : affineBudgetD B L c a0 a1 s ν z≠0) :
 budgetCrossingRate B L ν ((a0+a1*ν)*z/(2*ν))=
   1-affineBudgetK B L c a0 a1 s ν z/affineBudgetD B L c a0 a1 s ν z := by
 have hden : rayBudgetDen L ν ((a0+a1*ν)/ν) z≠0 := by
  intro hh
  apply hD
  rw [affineBudgetD_eq_ray _ _ _ _ _ _ _ _ hν hL,rayBudgetD_eq_den,hh,mul_zero]
 have hr := budgetCrossingRate_eq_ray (B:=B) hden
 have hp : ((a0+a1*ν)/ν)*z/2=(a0+a1*ν)*z/(2*ν) := by field_simp [hν]
 rw [hp] at hr
 rw [affineBudgetK_eq_ray _ _ _ _ _ _ _ _ hν hL,
   affineBudgetD_eq_ray _ _ _ _ _ _ _ _ hν hL,rayBudgetK_eq_save,rayBudgetD_eq_den]
 convert hr using 1 <;> field_simp [hν,hden] <;> ring

/-- The affine numerator reserve controls the physical HIGH expression. -/
theorem affine_rational_high_of_polynomial {K D ν a H P S u rho : ℝ}
 (hD : 0<D) (hp : 0≤H*K-ν*P*D-a*S*D+u*D-rho*D) :
 ν*P+((1-K/D)-1)*H+a*S≤u-rho := by
 have hh : (ν*P+((1-K/D)-1)*H+a*S)*D≤(u-rho)*D := by
  field_simp [hD.ne'] at *
  nlinarith only [hp]
 exact (mul_le_mul_iff_left₀ hD).mp hh

theorem affineCap_weighted_monotone {B L c a0 a1 s ν H S : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hH : 0≤H) (hS : s*H≤S)
 (hamp : ∀z∈Set.Icc (0:ℝ) 1,0≤affineCapAmp B L c a0 a1 s ν z) :
 MonotoneOn (weightedRatio (affineCapK B L c a0 a1 s ν)
   (affineCapD B L c a0 a1 s ν) H ((a0+a1*ν)*S)) (Set.Icc (0:ℝ) 1) := by
 apply weightedRatio_monotoneOn
   (fun z _=>affineCapK_hasDerivAt B L c a0 a1 s ν z hν.ne')
   (fun z _=>affineCapD_hasDerivAt B L c a0 a1 s ν z hν.ne')
   (fun z hz=>affineCap_den_pos hν hνhi ha hahi hz)
 intro z hz
 have hp := hamp z hz
 rw [affineCap_amplitude_identity] at hp
 exact derivative_reserve_transport ha.le hH hS hp

theorem affineBudget_weighted_monotone {B L c a0 a1 s ν H S : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν) (hL : 3/2≤L)
 (hH : 0≤H) (hS : s*H≤S)
 (hamp : ∀z∈Set.Icc (0:ℝ) 1,0≤affineBudgetAmp B L c a0 a1 s ν z) :
 MonotoneOn (weightedRatio (affineBudgetK B L c a0 a1 s ν)
   (affineBudgetD B L c a0 a1 s ν) H ((a0+a1*ν)*S)) (Set.Icc (0:ℝ) 1) := by
 have hL0 : L≠0 := by linarith
 apply weightedRatio_monotoneOn
   (fun z _=>affineBudgetK_hasDerivAt B L c a0 a1 s ν z hν.ne' hL0)
   (fun z _=>affineBudgetD_hasDerivAt B L c a0 a1 s ν z hν.ne' hL0)
   (fun z hz=>affineBudget_den_pos hν hνhi ha hahi hL hz)
 intro z hz
 have hp := hamp z hz
 rw [affineBudget_amplitude_identity] at hp
 exact derivative_reserve_transport ha.le hH hS hp

theorem selected_rate_eq_affine {a0 a1 ν : ℝ}
 (hD : selectedDen a0 a1 ν≠0) (ha : a0+a1*ν≤ν) :
 detectorRate ν (a0+a1*ν)=1-selectedSave a0 a1 ν/selectedDen a0 a1 ν := by
 have hJ : witnessDen ν (a0+a1*ν)≠0 := by
  convert hD using 1 <;> unfold witnessDen selectedDen <;> ring
 simp only [detectorRate,if_pos ha]
 unfold jointCountExponent selectedSave
 field_simp [hD,hJ]
 unfold witnessDen selectedDen
 ring

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.capCrossingRate_eq_affine
#print axioms Qrh.JointDetector.RepeatedMarks.affineBudget_weighted_monotone
