/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.slayer_recost_0p87477290596.RH20261023.Return.IntermediateCount.CountDecode
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RH20261023Return.IntermediateCount
noncomputable section
open RH20261023Return.C30

def witnessLower (b:CountBranch) : ℝ := lowerM b-1/10000000

theorem lowerM_buffer (b:CountBranch) : 2/5+1/10000000≤lowerM b := by
 unfold lowerM
 split_ifs
 · exact le_rfl
 · exact le_max_left _ _

theorem witnessLower_nonneg (b:CountBranch) : 0≤witnessLower b := by
 have hb := lowerM_buffer b
 dsimp [witnessLower]
 linarith

theorem natural_join_bounds : 2/5≤naturalM ∧ naturalM<1/2 := by
 norm_num [naturalM,naturalK]

theorem natural_kappa_bounds : (7/10:ℝ)≤naturalK/6 ∧ naturalK/6≤3/4 := by
 norm_num [naturalK]

theorem branch_cap_bounds (b:CountBranch) (hb:b≠.old) :
 branchZ b≤branchCap b ∧ branchZ b≤7/37 ∧ (1/10000000:ℝ)<branchZ b := by
 cases b <;> norm_num [branchZ,branchCap] at *

theorem admitted_widths (b:CountBranch) (hb:b≠.old) {δ p ν:ℝ}
 (hg:∀j:Fin 15,0<admissionGuard b δ p j) (hν:ν≤1/10000000) :
 ∀m:ℝ,witnessLower b≤m → m≤naturalM →
 ν<min (branchZ b) ((branchB b-2*m)/branchL b) := by
 have hl : 0<branchL b := lt_trans (by norm_num) (branch_lambda_gt_one b hb)
 have hn : 0<branchB b-2*naturalM-branchL b*(17/500+1/10000000)-2/10000000 := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 13
 intro m _ hm
 apply lt_min
 · exact lt_of_le_of_lt hν (branch_cap_bounds b hb).2.2
 · apply (lt_div_iff₀ hl).mpr
   have hv := mul_le_mul_of_nonneg_right hν hl.le
   have hpos : 0<branchL b*(17/500) := mul_pos hl (by norm_num)
   nlinarith

theorem admitted_buffered_plain (b:CountBranch) (hb:b≠.old) {δ p ε:ℝ}
 (hg:∀j:Fin 15,0<admissionGuard b δ p j) (hε:ε≤1/10000000) :
 witnessLower b+ε≤branchCutoff b δ p-branchInverse b δ p := by
 have hm := (admitted_witness_ranges b hb hg).2.2.2.2.2.2.1
 have hs := branch_lengths b (admitted_witness_ranges b hb hg).1
  (admitted_witness_ranges b hb hg).2.1
 dsimp [witnessLower]
 linarith
end
end QRH.RH20261023Return.IntermediateCount
#print axioms QRH.RH20261023Return.IntermediateCount.admitted_widths
#print axioms QRH.RH20261023Return.IntermediateCount.admitted_buffered_plain
