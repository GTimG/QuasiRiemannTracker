/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
/- Repeated marks: fork of Collet's final-stage module CountWidth (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): plain floor `2/5` and tail slope `17/500` replaced by `mMinus = 19/50`, `sMinus = 3/100`; caps `countCap`, `physicalCap` -/
/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to Submissions.arvi_density.Return and QRH.ArviDensity.Return (no other change). -/
import Candidate.Local.Qrh.PR97Refinement.Return.CountDecode
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.PR97Refinement.Return
open QRH.Record1252270103Return
noncomputable section


def witnessLower (b:CountBranch) : ℝ := lowerM b-1/10000000

theorem lowerM_buffer (b:CountBranch) : mMinus+1/10000000≤lowerM b := by
 unfold lowerM
 split_ifs
 · exact le_rfl
 · exact le_max_left _ _

theorem witnessLower_nonneg (b:CountBranch) : 0≤witnessLower b := by
 have hb := lowerM_buffer b
 have hm : (0:ℝ)≤mMinus := by norm_num [mMinus]
 dsimp [witnessLower]
 linarith

theorem natural_join_bounds : 2/5≤naturalM ∧ naturalM<1/2 := by
 norm_num [naturalM,naturalK,sMinus]

theorem natural_kappa_bounds : (7/10:ℝ)≤naturalK/6 ∧ naturalK/6≤3/4 := by
 norm_num [naturalK]

theorem branch_cap_bounds (b:CountBranch) (hb:b≠.old) :
 branchZ b≤branchCap b ∧ branchZ b≤7/37 ∧ (1/10000000:ℝ)<branchZ b := by
 cases b <;> norm_num [branchZ,branchCap,countCap,physicalCap] at *

theorem admitted_widths (b:CountBranch) (hb:b≠.old) {δ p ν:ℝ}
 (hg:∀j:Fin 15,0<admissionGuard b δ p j) (hν:ν≤1/10000000) :
 ∀m:ℝ,witnessLower b≤m → m≤naturalM →
 ν<min (branchZ b) ((branchB b-2*m)/branchL b) := by
 have hl : 0<branchL b := lt_trans (by norm_num) (branch_lambda_gt_one b hb)
 have hn : 0<branchB b-2*naturalM-branchL b*(sMinus+1/10000000)-2/10000000 := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 13
 intro m _ hm
 apply lt_min
 · exact lt_of_le_of_lt hν (branch_cap_bounds b hb).2.2
 · apply (lt_div_iff₀ hl).mpr
   have hv := mul_le_mul_of_nonneg_right hν hl.le
   have hpos : 0<branchL b*sMinus := mul_pos hl (by norm_num [sMinus])
   nlinarith

theorem admitted_buffered_plain (b:CountBranch) (hb:b≠.old) {δ p ε:ℝ}
 (hg:∀j:Fin 15,0<admissionGuard b δ p j) (hε:ε≤1/10000000) :
 witnessLower b+ε≤branchCutoff b δ p-branchInverse b δ p := by
 have hm := (admitted_witness_ranges b hb hg).2.2.2.2.2.2.1
 have hs := branch_lengths b (admitted_witness_ranges b hb hg).1
  (admitted_witness_ranges b hb hg).2.1
 have hm : (0:ℝ)≤mMinus := by norm_num [mMinus]
 dsimp [witnessLower]
 linarith
end
end QRH.PR97Refinement.Return
