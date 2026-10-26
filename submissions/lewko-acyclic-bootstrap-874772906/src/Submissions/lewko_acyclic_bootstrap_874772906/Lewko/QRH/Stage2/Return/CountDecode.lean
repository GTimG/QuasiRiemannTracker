/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.CountWindows
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.CountFromMoments
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.LewkoStage2Return
noncomputable section
open LewkoStage2Finite

theorem branch_lambda_gt_one (b : CountBranch) (hb:b≠.old) : 1<branchL b := by
 cases b <;> norm_num [branchL,countCL,physicalLambda] at *

theorem linear_plain_at_crossing (b:CountBranch) (hb:b≠.old) {δ p:ℝ}
 (hD:0<D b p) (hJ:0<countJ b δ p) :
 1-δ*A b p*branchPlain b δ p-δ*Z b p=branchCount b δ p := by
 rw [←inverse_at_branch_crossing b hb hD hJ]
 have hrel : D b p*branchInverse b δ p=A b p*branchCutoff b δ p+Z b p-p := by
  unfold branchInverse branchCutoff RN DJ
  field_simp [hD.ne',hJ.ne']
  <;> ring
 have hsum := branch_lengths b hD hJ
 rw [branch_D,←hsum] at hrel
 have hh := congrArg (fun z:ℝ=>δ*z) hrel
 nlinarith [hh]

theorem branch_plain_crossing (b:CountBranch) (hb:b≠.old) {δ p:ℝ}
 (hδ:0≤δ) (hp:0≤p) (hg:∀j:Fin 15,0<admissionGuard b δ p j) :
 plainCurve (branchB b) (branchL b) (branchZ b) δ p (branchPlain b δ p)≤branchCount b δ p := by
 obtain ⟨hD,hJ,_,_,_,_,hmlo,hmhi⟩ := admitted_witness_ranges b hb hg
 have hl : 0<branchL b := lt_trans (by norm_num) (branch_lambda_gt_one b hb)
 have he := linear_plain_at_crossing b hb hD hJ
 rw [plainCurve_eq _ _ _ _ _ _ hδ hp]
 by_cases hc : isCap b = true
 · have hm : upperM b≤(branchB b-branchL b*branchZ b)/2-1/10000000 := by
    simp only [upperM,hc,if_true]
    exact min_le_right _ _
   have hz : branchZ b≤(branchB b-2*branchPlain b δ p)/branchL b :=
    (le_div_iff₀ hl).mpr (by linarith)
   rw [min_eq_left hz]
   have hA : A b p=2 := by simp [A,hc]
   have hZ : Z b p=2*p*branchZ b := by simp [Z,hc]
   rw [hA,hZ] at he
   nlinarith
 · have hm : (branchB b-branchL b*branchZ b)/2+1/10000000≤lowerM b := by
    simp only [lowerM,hc,if_false,branchZ]
    exact le_max_right _ _
   have hz : (branchB b-2*branchPlain b δ p)/branchL b≤branchZ b :=
    (div_le_iff₀ hl).mpr (by linarith)
   rw [min_eq_right hz]
   have hA : A b p=2-4*p/branchL b := by simp [A,hc]
   have hZ : Z b p=2*p*branchB b/branchL b := by simp [Z,hc]
   rw [hA,hZ] at he
   have hid : 1-2*δ*branchPlain b δ p-2*δ*p*((branchB b-2*branchPlain b δ p)/branchL b)=
     1-δ*(2-4*p/branchL b)*branchPlain b δ p-δ*(2*p*branchB b/branchL b) := by ring
   rw [hid,he]

theorem admitted_natural_tail (b:CountBranch) (hb:b≠.old) {δ p:ℝ}
 (hg:∀j:Fin 15,0<admissionGuard b δ p j) :
 1-2*δ*naturalM-2*(δ*p)*(1-2*naturalM)/(6*(naturalK/6))≤branchCount b δ p := by
 have hJ := (admitted_witness_ranges b hb hg).2.1
 have ht : 0<countN b δ p-(1-2*δ*naturalM-2*δ*p*(17/500))*countJ b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 10
 have he : (1-2*naturalM)/(6*(naturalK/6))=(17/500:ℝ) := by norm_num [naturalM,naturalK]
 rw [mul_div_assoc,he]
 unfold branchCount
 exact (le_div_iff₀ hJ).mpr (by nlinarith)
end
end QRH.LewkoStage2Return
#print axioms QRH.LewkoStage2Return.branch_plain_crossing
#print axioms QRH.LewkoStage2Return.admitted_natural_tail
