/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original-slot-dependent loss is chosen after the fixed source mesh;
all remaining errors fit one common pre-slot reserve. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalAnalyticParametersHeight
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBufferedBudget
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open QRH.Record1252270103Source.PhysicalAnalytic

theorem high_total_loss (reserve θ τ omega rootError plainSlot otherMass:ℝ)(J:ℕ)
    (hf:FixedBudget reserve 100 100 1 θ)
    (hτ:2*τ*(J+1)≤θ/16)(hτ0:0≤τ)
    (hroot:rootError≤reserve/16)(hplain:plainSlot≤reserve/16)
    (homega:omega≤2*θ)(hmass:otherMass≤θ)
    :
    2*θ+2*θ+τ*J+omega+θ+θ+(4*θ+θ+rootError+plainSlot+otherMass)+reserve/2≤reserve := by
  have ht:τ*J≤θ/32:=by nlinarith only [hτ,hτ0]
  nlinarith only [hf.tiny,hf.positive,ht,hroot,hplain,homega,hmass]

/-- This exact LOW exponent is the output of the genuine missing-bin source.
In particular epsilonLow is chosen after N and never changes the parent mesh. -/
theorem low_total_loss (allowance reserve θ εslot Bmissing Bmaskcap:ℝ)(N:ℕ)
    (hf:FixedBudget reserve 100 100 1 θ)(hr:reserve≤allowance)
    (hs:2*εslot*100*(N:ℝ)≤θ/8)(hmissing:Bmissing≤6)(hmask:Bmaskcap≤10):
    -8*allowance+θ+θ+6*(θ/100)+θ+θ+(θ/100)*(Bmissing+θ)+
      2*εslot*100*N+θ+θ+2*θ+Bmaskcap*(θ/100)+θ ≤ -7*allowance := by
  have ht:=hf.positive
  have htheta:θ≤1:=hf.small.trans (by norm_num)
  have hm:=mul_le_mul_of_nonneg_left (show Bmissing+θ≤7 by linarith only [hmissing,htheta])
    (show 0≤θ/100 by positivity)
  have hk:=mul_le_mul_of_nonneg_right hmask (show 0≤θ/100 by positivity)
  nlinarith only [hf.tiny,hr,hs,hm,hk,ht]

/-- The complete finite fixed-L Newton reduction keeps a strict reserve after
its key-fiber loss and harmonic residual loss. -/
theorem normalized_loss_reserve (reserve θ:ℝ)(hf:FixedBudget reserve 100 100 1 θ):
    θ+(θ+4*(θ/100))-reserve/2≤-reserve/4 := by
  linarith only [hf.tiny,hf.positive]

/-- Fixed choices make both branch bounds non-growing at the final first
budget, while retaining a quarter-reserve for finite scalar absorption. -/
theorem combined_branch_reserve (allowance reserve θ:ℝ)
    (hf:FixedBudget reserve 100 100 1 θ)(hr:reserve≤allowance):
    θ+(θ+4*(θ/100))-7*allowance≤-reserve/4 ∧
    θ+(θ+4*(θ/100))-reserve/2≤-reserve/4 := by
  constructor
  · linarith only [hf.tiny,hf.positive,hr]
  · exact normalized_loss_reserve reserve θ hf
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.high_total_loss
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.low_total_loss
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.normalized_loss_reserve
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.combined_branch_reserve
