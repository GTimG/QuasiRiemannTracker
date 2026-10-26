/- Normalize actual inner LOW sources against ONE licensed arithmetic majorant.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeArithmeticEnvelope

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153Reachable Cycle153JointCount
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}{N : ReachableNode C j}
variable {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}

/-- The exact raw source estimate for ANY actual configuration is
normalized to the SAME whole arithmetic envelope. Dynamic first-bin,
profile and height factors remain in control; the fixed return
coefficient and raw AtState outer power are inserted exactly once.
The genuine negative OLD reserve remains explicit in rawOldExponent. -/
theorem actual_inner_low_raw_normalization
    (envelope : NativeArithmeticEnvelope hH N Bsrc boxes)
    (actual : NativeNodeForestReceipt hH N Bsrc boxes)
    (outer target rawOldExponent oldConstant Kreturn control cost : ℝ)
    (hold : 0 ≤ oldConstant)(hreturn : 0 ≤ Kreturn)(hcontrol : 0 ≤ control)
    (hOldExponent : rawOldExponent ≤ outer+target)
    (hsource : N.localBase^outer*cost ≤ oldConstant*control*N.localBase^rawOldExponent+
      Kreturn*control*actual.family.value) :
    cost ≤ (oldConstant*N.localBase^target+
      (2*Kreturn)*N.localBase^(-outer)*envelope.receipt.family.value)*control := by
  have hZ : 0<N.localBase:=zero_lt_one.trans N.localBase_gt_one
  have houter : 0<N.localBase^outer:=Real.rpow_pos_of_pos hZ _
  have hcancel : N.localBase^outer*N.localBase^(-outer)=(1:ℝ) := by
    rw [←Real.rpow_add hZ]
    simp only [add_neg_cancel,Real.rpow_zero]
  have hOld:=Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le hOldExponent
  have hret:=mul_le_mul_of_nonneg_left (envelope.dominates actual)
    (mul_nonneg hreturn hcontrol)
  apply le_of_mul_le_mul_left ?_ houter
  calc
    _ ≤ oldConstant*control*N.localBase^rawOldExponent+Kreturn*control*actual.family.value:=hsource
    _ ≤ oldConstant*control*N.localBase^(outer+target)+
        (2*Kreturn)*control*envelope.receipt.family.value:=by
      exact add_le_add (mul_le_mul_of_nonneg_left hOld (mul_nonneg hold hcontrol)) (by nlinarith only [hret])
    _ = _:=by
      rw [Real.rpow_add hZ]
      calc
        _ = N.localBase^outer*(oldConstant*N.localBase^target*control)+
            (N.localBase^outer*N.localBase^(-outer))*
              ((2*Kreturn)*envelope.receipt.family.value*control):=by rw [hcancel];ring
        _ = _:=by ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_inner_low_raw_normalization
