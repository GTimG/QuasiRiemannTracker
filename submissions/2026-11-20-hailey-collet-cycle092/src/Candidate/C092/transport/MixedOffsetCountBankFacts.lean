/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native scalar identities for the compact actual middle-bank consumer. -/
import Candidate.C092.transport.MixedOffsetCountBank
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount.MiddleBank
noncomputable section
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record12518109Count Cycle25ProbeFinalAssembly QRH.Cycle092.PacketJoinE49
variable {D : Cycle25.Weighted.MomentData} {S : WeightedSourceData D} {η : Character} {Z : ℝ}

 theorem delta_pos (B : MiddleBank D S η Z) : 0<B.delta := by dsimp [delta];linarith [B.a_min]
 theorem baseScale_gt_one (B : MiddleBank D S η Z) (hZ : 1<Z) : 1<B.baseScale :=
  Real.one_lt_rpow hZ (by linarith [B.d_min])
 theorem k_pos (B : MiddleBank D S η Z) : 0<B.k := Return.hk B.available.1 B.available.2
 theorem full_mean (B : MiddleBank D S η Z) : B.currentSlice.fiber.q=B.delta*B.p := by
  rw [B.current_mean]
  dsimp [p]
  exact (mul_div_cancel₀ _ B.delta_pos.ne').symm

 theorem R_identity (B : MiddleBank D S η Z) : B.R=1-B.delta*(Return.aI B.p+B.k*(2*B.m)) := by
  have hj:Return.JI B.delta B.p≠0:=(Return.hJ B.available.1 B.available.2).ne'
  have hid:=Return.inverse_identity B.delta B.p hj
  have hcross : Return.crossingI B.delta B.p=2*B.m := by
    dsimp [Return.crossingI,m]
    rw [B.baseline_cutoff]
    dsimp [Return.cutoffI,p,delta];ring
  rw [hcross] at hid
  exact hid.symm

 theorem R_expanded (B : MiddleBank D S η Z) :
    B.R=1-B.delta*(B.p*(1+2*Return.line.g0)+2*B.k*B.m) := by
  rw [B.R_identity]
  dsimp [Return.aI];ring

 theorem penalty_count_with_max (B : MiddleBank D S η Z) (K : CountConstants)
    (hc : B.CountConclusion K) (hU : 0 ≤ B.baseScale) (lo hi M : ℝ)
    (hlo : 0 ≤ lo) (hkl : lo ≤ B.k) (hkh : B.k ≤ hi) (hm : B.m ≤ M) :
    (B.common.card:ℝ) ≤ max 1 (B.coefficient K)*B.baseScale^(B.R-
      B.delta*(B.penalty lo hi M-B.k*(B.currentSlice.fiber.m-B.m))+B.loss) :=
  ((hc.2 lo hi M hlo hkl hkh hm).2).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hU _))

#print axioms R_expanded
#print axioms full_mean
end
end QRH.Cycle092.MixedOffsetCount.MiddleBank
