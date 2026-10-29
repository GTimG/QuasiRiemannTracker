/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.AffineHighCertificate

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set HighTemplates AuxHighTemplates

private theorem affine_branch_scaled_mono {ν a P H S : ℝ} {K D : ℝ→ℝ}
 {rate : ℝ→ℝ} (ha : 0<a)
 (he : ∀z∈Icc (0:ℝ) 1,rate (a*z)=1-K z/D z)
 (hm : MonotoneOn (weightedRatio K D H (a*S)) (Icc (0:ℝ) 1)) :
 MonotoneOn (fun v=>ν*P+(rate v-1)*H+v*S) (Icc (0:ℝ) a) := by
 apply scaled_weighted_monotone (a:=a) (g:=weightedRatio K D H (a*S)) (C:=ν*P-H) ha
 · intro z hz
   rw [he z hz]
   unfold weightedRatio
   ring
 · exact hm

theorem affine_cap_scaled_monotone {B L c a0 a1 s ν P H S : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hH : 0≤H) (hS : s*H≤S)
 (hamp : ∀z∈Icc (0:ℝ) 1,0≤affineCapAmp B L c a0 a1 s ν z) :
 MonotoneOn (fun v=>ν*P+(capCrossingRate c ν (v/(2*ν))-1)*H+v*S)
   (Icc (0:ℝ) (a0+a1*ν)) := by
 apply affine_branch_scaled_mono (K:=affineCapK B L c a0 a1 s ν)
   (D:=affineCapD B L c a0 a1 s ν) ha
 · intro z hz
   exact capCrossingRate_eq_affine hν.ne'
     (affineCap_den_pos hν hνhi ha hahi hz).ne'
 · exact affineCap_weighted_monotone hν hνhi ha hahi hH hS hamp

theorem affine_budget_scaled_monotone {B L c a0 a1 s ν P H S : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hL : 3/2≤L) (hH : 0≤H) (hS : s*H≤S)
 (hamp : ∀z∈Icc (0:ℝ) 1,0≤affineBudgetAmp B L c a0 a1 s ν z) :
 MonotoneOn (fun v=>ν*P+(budgetCrossingRate B L ν (v/(2*ν))-1)*H+v*S)
   (Icc (0:ℝ) (a0+a1*ν)) := by
 have hL0 : L≠0 := by linarith
 apply affine_branch_scaled_mono (K:=affineBudgetK B L c a0 a1 s ν)
   (D:=affineBudgetD B L c a0 a1 s ν) ha
 · intro z hz
   exact budgetCrossingRate_eq_affine hν.ne' hL0
     (affineBudget_den_pos hν hνhi ha hahi hL hz).ne'
 · exact affineBudget_weighted_monotone hν hνhi ha hahi hL hH hS hamp

/-- All three literal raw branches are monotone below the divider.
The tail is retained even when it is not the binding certificate branch. -/
theorem affine_raw_weighted_monotone {B L c a0 a1 s ν P H S : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hL : 3/2≤L) (hH : 0≤H) (hS0 : 0≤S) (hS : s*H≤S)
 (hcap : ∀z∈Icc (0:ℝ) 1,0≤affineCapAmp B L c a0 a1 s ν z)
 (hbudget : ∀z∈Icc (0:ℝ) 1,0≤affineBudgetAmp B L c a0 a1 s ν z) :
 MonotoneOn (fun v=>ν*P+(rawRepeatedCountRate B L c ν v-1)*H+v*S)
   (Icc (0:ℝ) (a0+a1*ν)) := by
 apply rawWeighted_monotoneOn hH
 · exact affine_cap_scaled_monotone hν hνhi ha hahi hH hS hcap
 · exact affine_budget_scaled_monotone hν hνhi ha hahi hL hH hS hbudget
 · intro x hx y hy hxy
   have hh := mul_le_mul_of_nonneg_right hxy hS0
   linarith only [hh]

/-- Combining divider certificates retains the maximum of both plain
capacity branches and the no-slot tail, before the amplitude supremum. -/
theorem raw_divider_bound_of_branches {B L c ν a P H S bound : ℝ} (hH : 0≤H)
 (hcap : ν*P+(capCrossingRate c ν (a/(2*ν))-1)*H+a*S≤bound)
 (hbudget : ν*P+(budgetCrossingRate B L ν (a/(2*ν))-1)*H+a*S≤bound)
 (htail : ν*P+((1-ν*B)-1)*H+a*S≤bound) :
 ν*P+(rawRepeatedCountRate B L c ν a-1)*H+a*S≤bound := by
 unfold rawRepeatedCountRate
 rw [weighted_max_identity _ _ _ _ _ hH,weighted_max_identity _ _ _ _ _ hH]
 exact max_le (max_le hcap hbudget) htail

theorem affine_raw_weighted_bound {B L c a0 a1 s ν P H S bound : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : 0<a0+a1*ν) (hahi : a0+a1*ν≤ν)
 (hL : 3/2≤L) (hH : 0≤H) (hS0 : 0≤S) (hS : s*H≤S)
 (hcap : ∀z∈Icc (0:ℝ) 1,0≤affineCapAmp B L c a0 a1 s ν z)
 (hbudget : ∀z∈Icc (0:ℝ) 1,0≤affineBudgetAmp B L c a0 a1 s ν z)
 (hdivider : ν*P+(rawRepeatedCountRate B L c ν (a0+a1*ν)-1)*H+(a0+a1*ν)*S≤bound) :
 ∀v∈Icc (0:ℝ) (a0+a1*ν),ν*P+(rawRepeatedCountRate B L c ν v-1)*H+v*S≤bound := by
 have hm := affine_raw_weighted_monotone (P:=P) hν hνhi ha hahi hL hH hS0 hS hcap hbudget
 intro v hv
 exact (hm hv ⟨ha.le,le_rfl⟩ hv.2).trans hdivider

/-- The pure branch uses the full zero slope as divider. -/
theorem pure_raw_weighted_bound {B L c s ν P H S bound : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (hL : 3/2≤L)
 (hH : 0≤H) (hS0 : 0≤S) (hS : s*H≤S)
 (hcap : ∀z∈Icc (0:ℝ) 1,0≤affineCapAmp B L c 0 1 s ν z)
 (hbudget : ∀z∈Icc (0:ℝ) 1,0≤affineBudgetAmp B L c 0 1 s ν z)
 (hdivider : ν*P+(rawRepeatedCountRate B L c ν ν-1)*H+ν*S≤bound) :
 ∀v∈Icc (0:ℝ) ν,ν*P+(rawRepeatedCountRate B L c ν v-1)*H+v*S≤bound := by
 simpa only [zero_add,one_mul] using affine_raw_weighted_bound
   (a0:=0) (a1:=1) hν hνhi (by simpa using hν) (by simp) hL hH hS0 hS hcap hbudget
   (by simpa using hdivider)

/-- The same-event minimum is taken before maximizing amplitude. Above
the divider the selected count decreases with a strict usable slope. -/
theorem affine_combined_weighted_bound {B L c a0 a1 s ν P H S bound : ℝ}
 (hν : 0<ν) (hνhi : ν≤3/4) (ha : (500001/1000000:ℝ)≤a0+a1*ν)
 (hahi : a0+a1*ν≤ν) (hL : 3/2≤L)
 (hH : 0≤H) (hS0 : 0≤S) (hS : s*H≤S) (hSupper : S≤H/10)
 (hcap : ∀z∈Icc (0:ℝ) 1,0≤affineCapAmp B L c a0 a1 s ν z)
 (hbudget : ∀z∈Icc (0:ℝ) 1,0≤affineBudgetAmp B L c a0 a1 s ν z)
 (hraw : ν*P+(rawRepeatedCountRate B L c ν (a0+a1*ν)-1)*H+(a0+a1*ν)*S≤bound)
 (hselected : ν*P+(detectorRate ν (a0+a1*ν)-1)*H+(a0+a1*ν)*S≤bound) :
 ∀v∈Icc (0:ℝ) ν,
 ν*P+(combineSelected (rawRepeatedCountRate B L c) ν v-1)*H+v*S≤bound := by
 apply combined_weighted_bound hνhi ⟨ha,hahi⟩ hH hSupper
 · exact affine_raw_weighted_monotone hν hνhi (by linarith) hahi hL hH hS0 hS hcap hbudget
 · exact hraw
 · exact hselected

end
end Qrh.JointDetector.RepeatedMarks

#print axioms Qrh.JointDetector.RepeatedMarks.affine_combined_weighted_bound
