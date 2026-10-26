/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The fixed numerical source applications retain one common half reserve;
key fibers and the full residual harmonic sum leave a quarter reserve. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularSourceChoice
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open PhysicalAnalytic

def regularRootLoss (θ mesh:ℝ):ℝ:=
  100*(155*θ+100*mesh+θ+(3/4)*θ+θ)+θ+2*θ

def regularOtherLoss (θ mesh εslot:ℝ)(N:ℕ):ℝ:=
  4*θ+θ+regularRootLoss θ mesh+2*(θ/16)*100+(2*εslot*100)*N+6*(θ/100)

def regularLowLoss (allowance θ εslot:ℝ)(N:ℕ):ℝ:=
  -8*allowance+θ+θ+6*(θ/100)+θ+θ+(θ/100)*(6+θ)+
    2*εslot*100*N+θ+θ+2*θ+10*(θ/100)+θ

theorem regular_loss_ledger (reserve allowance θ mesh εslot wmin rmin τ omega fee highReserve:ℝ)
    (N J:ℕ)(hf:FixedBudget reserve 100 100 1 θ)
    (hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
    (hr:reserve≤allowance)(hhigh:reserve≤highReserve)(hfee:0≤fee)
    (hmesh:0≤mesh)(hm:100*mesh≤θ)(hτ:0≤τ)(hτJ:2*τ*(J+1)≤θ/16)
    (homega:omega≤2*θ):
    0≤regularRootLoss θ mesh ∧
    regularLowLoss allowance θ εslot N≤-(reserve/2) ∧
    2*θ+2*θ+τ*J+omega+θ+θ+regularOtherLoss θ mesh εslot N+reserve/2≤fee+highReserve ∧
    θ+(θ+4*(θ/100))-reserve/2≤-reserve/4:=by
  have hθ:=hf.positive
  have hroot:regularRootLoss θ mesh≤reserve/16:=by
    simpa only [regularRootLoss,mul_one] using (hf.root (100*mesh) (by positivity) hm).le
  have hplain:2*(θ/16)*100+(2*εslot*100)*(N:ℝ)≤reserve/16:=by
    have h:=hf.plain
    linarith only [h,hc.slot_cost]
  have hm₀:6*(θ/100)≤θ:=by linarith only [hf.positive]
  have hh:=high_total_loss reserve θ τ omega (regularRootLoss θ mesh)
    (2*(θ/16)*100+(2*εslot*100)*N) (6*(θ/100)) J hf hτJ hτ hroot hplain homega hm₀
  have hl:=low_total_loss allowance reserve θ εslot 6 10 N hf hr hc.slot_cost le_rfl le_rfl
  have hr0:0<reserve:=by linarith only [hf.tiny,hf.positive]
  refine ⟨by unfold regularRootLoss;positivity,?_,?_,normalized_loss_reserve reserve θ hf⟩
  · change regularLowLoss allowance θ εslot N≤-7*allowance at hl
    linarith only [hl,hr,hr0]
  · unfold regularOtherLoss
    linarith only [hh,hfee,hhigh]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_loss_ledger
