/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceHighSigns
namespace Qrh.JointDetector.RepeatedMarks.SourceStep
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set HighTemplates AuxHighTemplates BernsteinBox

private theorem branch_scaled_mono {ν r P H S : ℝ} {K D : ℝ → ℝ}
 {rate : ℝ → ℝ} (ha : 0 < r*ν)
 (he : ∀ z ∈ Icc (0:ℝ) 1, rate (r*ν*z)=1-K z/D z)
 (hm : MonotoneOn (weightedRatio K D H (r*ν*S)) (Icc (0:ℝ) 1)) :
 MonotoneOn (fun v => ν*P+(rate v-1)*H+v*S) (Icc (0:ℝ) (r*ν)) := by
 apply scaled_weighted_monotone (a:=r*ν) (g:=weightedRatio K D H (r*ν*S)) (C:=ν*P-H) ha
 · intro z hz
   rw [he z hz]
   unfold weightedRatio
   ring
 · exact hm

private theorem cap_scaled_mono {B L c ν r P H S s : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : 0 < r) (hrhi : r ≤ 1)
 (hH : 0 ≤ H) (hS : s*H ≤ S)
 (hamp : ∀ z ∈ Icc (0:ℝ) 1,0 ≤ rayCapAmp B L c 0 r s ν z) :
 MonotoneOn (fun v => ν*P+(capCrossingRate c ν (v/(2*ν))-1)*H+v*S)
 (Icc (0:ℝ) (r*ν)) := by
 apply branch_scaled_mono (K:=rayCapK B L c 0 r s ν)
   (D:=rayCapD B L c 0 r s ν) (by positivity)
 · intro z hz
   have hD := rayCap_den_pos (B:=B) (L:=L) (c:=c) (s:=s) hν hνhi hrhi hr.le hz
   rw [rayCapD_eq_den] at hD
   have he : r*ν*z/(2*ν)=r*z/2 := by field_simp
   rw [he,capCrossingRate_eq_ray hD.ne']
   rw [rayCapK_eq_save,rayCapD_eq_den]
 · exact rayCap_weighted_monotone hν hνhi hr hrhi hH hS hamp

private theorem budget_scaled_mono {B L c ν r P H S s : ℝ}
 (hν : 0 < ν) (hνhi : ν ≤ 3/4) (hr : 0 < r) (hrhi : r ≤ 1)
 (hL : 3/2 ≤ L) (hH : 0 ≤ H) (hS : s*H ≤ S)
 (hamp : ∀ z ∈ Icc (0:ℝ) 1,0 ≤ rayBudgetAmp B L c 0 r s ν z) :
 MonotoneOn (fun v => ν*P+(budgetCrossingRate B L ν (v/(2*ν))-1)*H+v*S)
 (Icc (0:ℝ) (r*ν)) := by
 apply branch_scaled_mono (K:=rayBudgetK B L c 0 r s ν)
   (D:=rayBudgetD B L c 0 r s ν) (by positivity)
 · intro z hz
   have hD := rayBudget_den_pos (B:=B) (c:=c) (s:=s) hν hνhi hrhi hr.le hL hz
   rw [rayBudgetD_eq_den] at hD
   have he : r*ν*z/(2*ν)=r*z/2 := by field_simp
   rw [he,budgetCrossingRate_eq_ray hD.ne']
   rw [rayBudgetK_eq_save,rayBudgetD_eq_den]
 · exact rayBudget_weighted_monotone hν hνhi hr hrhi hL hH hS hamp


private theorem nominal_bound_of_endpoints {p : Params} {R ν r rho w : ℝ}
 (he : ∀ k : Fin 2,
   ν*endpointP p k+(R-1)*endpointH p k+(r*ν)*endpointS p k ≤ endpointU p k-rho)
 (hw : w ∈ Icc (crossing p) p.c) :
 ν*(p.B-p.L*w)+(R-1)*(1-6*(p.A*(w-crossing p)))+
   (r*ν)*(w-p.A*(w-crossing p)) ≤ p.A*(w-crossing p)-rho := by
 have hh := affine_endpoint_upper (w:=w)
   (a:=ν*p.B+(R-1)*(1+6*p.A*crossing p)+(r*ν)*p.A*crossing p+p.A*crossing p)
   (b:= -ν*p.L-6*p.A*(R-1)+(r*ν)*(1-p.A)-p.A)
   (bound:= -rho) (lo:=crossing p) (hi:=p.c)
 have h0 := he 0
 have h1 := he 1
 norm_num [endpointP,endpointH,endpointS,endpointU,endpointWidth] at h0 h1
 have hl : ν*p.B+(R-1)*(1+6*p.A*crossing p)+(r*ν)*p.A*crossing p+p.A*crossing p+
   (-ν*p.L-6*p.A*(R-1)+(r*ν)*(1-p.A)-p.A)*crossing p ≤ -rho := by nlinarith only [h0]
 have hu : ν*p.B+(R-1)*(1+6*p.A*crossing p)+(r*ν)*p.A*crossing p+p.A*crossing p+
   (-ν*p.L-6*p.A*(R-1)+(r*ν)*(1-p.A)-p.A)*p.c ≤ -rho := by nlinarith only [h1]
 have ht := hh hl hu hw
 nlinarith only [ht]

/-- Both physical width endpoints control the literal raw repeated count
at the ray divider. The parent moment cap is always one tenth. -/
theorem SourceHighSigns.raw_divider {p : Params} {r ν w : ℝ} {combined : Bool}
 (hc : SourceHighSigns p r combined) (hν : ν ∈ Icc p.q (3/4:ℝ))
 (hw : w ∈ Icc (crossing p) p.c) :
 ν*(p.B-p.L*w)+(rawRepeatedCountRate p.B0 p.L0 (1/10) ν (r*ν)-1)*
   (1-6*(p.A*(w-crossing p)))+(r*ν)*(w-p.A*(w-crossing p)) ≤
 p.A*(w-crossing p)-highRho := by
 rcases hc with ⟨hr,hrhi,hq,hqhi,hL,hcut,hca,hba,hch,hbh,hth,hsh⟩
 have hνpos : 0 < ν := hq.trans_le hν.1
 have hcD := rayCap_den_pos (B:=p.B0) (L:=p.L0) (c:=1/10) (s:=0)
   hνpos hν.2 hrhi hr.le (show (1:ℝ) ∈ Icc 0 1 from ⟨by norm_num,le_rfl⟩)
 have hbD := rayBudget_den_pos (B:=p.B0) (c:=1/10) (s:=0)
   hνpos hν.2 hrhi hr.le hL (show (1:ℝ) ∈ Icc 0 1 from ⟨by norm_num,le_rfl⟩)
 have hend k : ν*endpointP p k+
   (rawRepeatedCountRate p.B0 p.L0 (1/10) ν (r*ν)-1)*endpointH p k+
   (r*ν)*endpointS p k ≤ endpointU p k-highRho := by
  have hcp := rayCap_high_nonneg p.B0 p.L0 (1/10) 0 r
    (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho p.q (3/4) ν hqhi hν (hch k)
  have hbp := rayBudget_high_nonneg p.B0 p.L0 (1/10) 0 r
    (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho p.q (3/4) ν hqhi hν (hbh k)
  have htp := tail_high_nonneg p.B0 0 r
    (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho p.q (3/4) ν hqhi hν (hth k)
  rw [rayCap_high_identity] at hcp
  rw [rayBudget_high_identity] at hbp
  have hcb := rational_high_of_polynomial hcD hcp
  have hbb := rational_high_of_polynomial hbD hbp
  rw [rayCapK_eq_save,rayCapD_eq_den] at hcb
  rw [rayBudgetK_eq_save,rayBudgetD_eq_den] at hbb
  have hdc : 0 < rayCapDen ν r 1 := by simpa only [rayCapD_eq_den] using hcD
  have hcr := capCrossingRate_eq_ray (c:=(1/10)) hdc.ne'
  have hdb : 0 < rayBudgetDen p.L0 ν r 1 := by simpa only [rayBudgetD_eq_den] using hbD
  have hbr := budgetCrossingRate_eq_ray (B:=p.B0) hdb.ne'
  have hνr : r*ν/(2*ν)=r/2 := by field_simp
  unfold rawRepeatedCountRate
  rw [hνr]
  have hcr' : capCrossingRate (1/10) ν (r/2)=
    1-rayCapSave (1/10) ν r 1/rayCapDen ν r 1 := by simpa only [mul_one] using hcr
  have hbr' : budgetCrossingRate p.B0 p.L0 ν (r/2)=
    1-rayBudgetSave p.B0 p.L0 ν r 1/rayBudgetDen p.L0 ν r 1 := by simpa only [mul_one] using hbr
  rw [hcr',hbr']
  rcases le_total (1-rayCapSave (1/10) ν r 1/rayCapDen ν r 1)
    (1-rayBudgetSave p.B0 p.L0 ν r 1/rayBudgetDen p.L0 ν r 1) with ht | ht
  · rw [max_eq_right ht]
    rcases le_total (1-rayBudgetSave p.B0 p.L0 ν r 1/rayBudgetDen p.L0 ν r 1) (1-ν*p.B0) with ht | ht
    · rw [max_eq_right ht]; unfold tailHigh at htp; nlinarith only [htp]
    · rw [max_eq_left ht]; exact hbb
  · rw [max_eq_left ht]
    rcases le_total (1-rayCapSave (1/10) ν r 1/rayCapDen ν r 1) (1-ν*p.B0) with ht | ht
    · rw [max_eq_right ht]; unfold tailHigh at htp; nlinarith only [htp]
    · rw [max_eq_left ht]; exact hcb
 exact nominal_bound_of_endpoints hend hw


theorem SourceHighSigns.selected_divider {p : Params} {r ν w : ℝ}
 (hc : SourceHighSigns p r true) (hν : ν ∈ Icc p.q (3/4:ℝ))
 (hw : w ∈ Icc (crossing p) p.c) :
 ν*(p.B-p.L*w)+(detectorRate ν (r*ν)-1)*(1-6*(p.A*(w-crossing p)))+
 (r*ν)*(w-p.A*(w-crossing p)) ≤ p.A*(w-crossing p)-highRho := by
 rcases hc with ⟨hr,hrhi,hq,hqhi,hL,hcut,hca,hba,hch,hbh,hth,hsh⟩
 have hνpos : 0 < ν := hq.trans_le hν.1
 have ha : r*ν ≤ ν := by nlinarith
 have hD : 0 < selectedDen 0 r ν := by unfold selectedDen; nlinarith [hν.2]
 apply nominal_bound_of_endpoints (R:=detectorRate ν (r*ν))
 · intro k
   have hp := selected_high_nonneg 0 r (endpointH p k) (endpointP p k)
     (endpointS p k) (endpointU p k) highRho p.q (3/4) ν hqhi hν (hsh rfl k)
   unfold selectedHigh at hp
   have hp' : 0 ≤ (endpointH p k)*selectedSave 0 r ν-ν*(endpointP p k)*selectedDen 0 r ν-
     (r*ν)*(endpointS p k)*selectedDen 0 r ν+(endpointU p k)*selectedDen 0 r ν-highRho*selectedDen 0 r ν := by nlinarith only [hp]
   have hb := rational_high_of_polynomial hD hp'
   rw [←selected_rate_eq_saving hD.ne' ha] at hb
   exact hb
 · exact hw

/-- All amplitudes of the actual raw/selected same-event family. -/
theorem SourceHighSigns.all_amplitudes {p : Params} {r ν w : ℝ} {combined : Bool}
 (hc : SourceHighSigns p r combined) (hg : GeometryCertificate p)
 (hselectedCap : combined=true → p.c0 ≤ 1/10)
 (hpure : combined=false → r=1)
 (hν : ν ∈ Icc p.q (3/4:ℝ)) (hw : w ∈ Icc (crossing p) p.c) :
 ∀ v ∈ Icc (0:ℝ) ν,
 ν*(p.B-p.L*w)+((if combined then combineSelected (rawRepeatedCountRate p.B0 p.L0 (1/10)) ν v
   else rawRepeatedCountRate p.B0 p.L0 (1/10) ν v)-1)*(1-6*(p.A*(w-crossing p)))+
 v*(w-p.A*(w-crossing p)) ≤ p.A*(w-crossing p)-highRho := by
 have hraw := hc.raw_divider hν hw
 rcases hc with ⟨hr,hrhi,hq,hqhi,hL,hcut,hca,hba,hch,hbh,hth,hsh⟩
 have hνpos : 0 < ν := hq.trans_le hν.1
 let H := 1-6*(p.A*(w-crossing p))
 let S := w-p.A*(w-crossing p)
 have hs0 : 0 ≤ crossing p := hg.face.cross_nonneg
 have hu0 : 0 ≤ p.A*(w-crossing p) := mul_nonneg hg.A_pos.le (sub_nonneg.mpr hw.1)
 have hS0 : 0 ≤ S := by
  dsimp [S]
  nlinarith [mul_nonneg (sub_nonneg.mpr hg.A_lt.le) (sub_nonneg.mpr hw.1)]
 obtain ⟨gh,ghpos,ghAll⟩ := hg.endpoints.uniform
 have ghH := ghAll 0 w hw
 have ghC := ghAll 1 w hw
 norm_num [affineIntercepts,affineSlopes] at ghH ghC
 have hH : 0 ≤ H := by dsimp [H]; nlinarith only [ghH,ghpos]
 have hratio : crossing p*H ≤ S := nominal_slot_ratio hg.A_pos.le hg.A_lt.le hs0 hw.1
 have hmono : MonotoneOn
   (fun v => ν*(p.B-p.L*w)+(rawRepeatedCountRate p.B0 p.L0 (1/10) ν v-1)*H+v*S)
   (Icc (0:ℝ) (r*ν)) := by
  apply rawWeighted_monotoneOn hH
  · apply cap_scaled_mono hνpos hν.2 hr hrhi hH hratio
    intro z hz
    exact rayCap_nonneg p.B0 p.L0 (1/10) 0 r (crossing p) p.q (3/4) ν z hqhi hν hz hca
  · apply budget_scaled_mono hνpos hν.2 hr hrhi hL hH hratio
    intro z hz
    exact rayBudget_nonneg p.B0 p.L0 (1/10) 0 r (crossing p) p.q (3/4) ν z hqhi hν hz hba
  · intro x hx y hy hxy
    have hh := mul_le_mul_of_nonneg_right hxy hS0
    dsimp only
    linarith only [hh]
 cases combined with
 | false =>
   have hre := hpure rfl
   subst r
   simp only [Bool.false_eq_true,ite_false,one_mul] at hraw hmono ⊢
   intro v hv
   exact (hmono hv ⟨hνpos.le,le_rfl⟩ hv.2).trans hraw
 | true =>
   have hsc := hselectedCap rfl
   have hcap := ghC
   have hSH : S ≤ H/10 := by dsimp [S,H] at *; nlinarith [mul_nonneg (sub_nonneg.mpr hsc) hH]
   apply combined_weighted_bound hν.2
     ⟨by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hν.1),hcut rfl],by nlinarith⟩ hH hSH hmono hraw
   apply SourceHighSigns.selected_divider
   · exact ⟨hr,hrhi,hq,hqhi,hL,hcut,hca,hba,hch,hbh,hth,hsh⟩
   · exact hν
   · exact hw


/-- Literal full-label family reserve with no analytic hypothesis. The
moment-parent cap is .1 even when a final repeat-only child cap expands. -/
theorem SourceHighSigns.highReserve {p : Params} {r : ℝ} {combined : Bool}
 (hc : SourceHighSigns p r combined) (hg : GeometryCertificate p)
 (hB0 : 0 ≤ p.B0) (hB : p.B0 ≤ 1) (hL : 3/2 ≤ p.L0)
 (hq : p.q ∈ Ioc (0:ℝ) (3/4))
 (hselectedCap : combined=true → p.c0 ≤ 1/10)
 (hpure : combined=false → r=1) {w : ℝ} (hw : w ∈ Icc (crossing p) p.c) :
 HighReserve (repeatedFamily p.B0 p.L0 (1/10) p.q hB0 hB hL
   (by norm_num) (by norm_num) hq combined)
 p.B p.L w (p.A*(w-crossing p)) highRho := by
 intro i
 have hb := hc.all_amplitudes hg hselectedCap hpure
   (show i.val.1 ∈ Icc p.q (3/4:ℝ) from ⟨i.property.1,i.property.2.1⟩) hw
   i.val.2 i.property.2.2
 change highRho ≤ p.A*(w-crossing p)-
   (i.val.1*(p.B-p.L*w)+
    ((if combined then combineSelected (rawRepeatedCountRate p.B0 p.L0 (1/10)) i.val.1 i.val.2
      else rawRepeatedCountRate p.B0 p.L0 (1/10) i.val.1 i.val.2)-1)*
    (1-6*(p.A*(w-crossing p)))+i.val.2*(w-p.A*(w-crossing p)))
 linarith only [hb]

theorem SourceHighSigns.gates {p : Params} {r : ℝ} {combined : Bool}
 (hc : SourceHighSigns p r combined) (hg : GeometryCertificate p)
 (hB0 : 0 ≤ p.B0) (hB : p.B0 ≤ 1) (hL : 3/2 ≤ p.L0)
 (hq : p.q ∈ Ioc (0:ℝ) (3/4))
 (hselectedCap : combined=true → p.c0 ≤ 1/10)
 (hpure : combined=false → r=1) :
 Gates p (repeatedFamily p.B0 p.L0 (1/10) p.q hB0 hB hL
   (by norm_num) (by norm_num) hq combined) := by
 apply hg.gates
 refine ⟨highRho,by norm_num [highRho],?_⟩
 intro w hw
 exact hc.highReserve hg hB0 hB hL hq hselectedCap hpure hw

end
end Qrh.JointDetector.RepeatedMarks.SourceStep

#print axioms Qrh.JointDetector.RepeatedMarks.SourceStep.SourceHighSigns.highReserve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceStep.SourceHighSigns.gates
