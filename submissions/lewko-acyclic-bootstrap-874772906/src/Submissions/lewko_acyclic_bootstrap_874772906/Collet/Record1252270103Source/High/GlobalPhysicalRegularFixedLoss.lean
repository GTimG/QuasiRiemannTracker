/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual point source uses the fixed upper root error reserve/16. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularLossLedger
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open PhysicalAnalytic

def regularFixedOtherLoss (reserve θ εslot:ℝ)(N:ℕ):ℝ:=
  4*θ+θ+reserve/16+2*(θ/16)*100+(2*εslot*100)*N+6*(θ/100)

theorem regular_fixed_loss_ledger (reserve allowance θ εslot wmin rmin τ omega fee:ℝ)
    (N J:ℕ)(hf:FixedBudget reserve 100 100 1 θ)
    (hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
    (hr:reserve≤allowance)(hfee:0≤fee)(hτ:0≤τ)(hτJ:2*τ*(J+1)≤θ/16)
    (homega:omega≤2*θ):
    regularLowLoss allowance θ εslot N≤-(reserve/2) ∧
    2*θ+2*θ+τ*J+omega+θ+θ+regularFixedOtherLoss reserve θ εslot N+reserve/2≤fee+reserve:=by
  have hplain:2*(θ/16)*100+(2*εslot*100)*(N:ℝ)≤reserve/16:=by
    have h:=hf.plain
    linarith only [h,hc.slot_cost]
  have hm:6*(θ/100)≤θ:=by linarith only [hf.positive]
  have hh:=high_total_loss reserve θ τ omega (reserve/16)
    (2*(θ/16)*100+(2*εslot*100)*N) (6*(θ/100)) J hf hτJ hτ le_rfl hplain homega hm
  have hl:=low_total_loss allowance reserve θ εslot 6 10 N hf hr hc.slot_cost le_rfl le_rfl
  have hr0:0<reserve:=by linarith only [hf.tiny,hf.positive]
  refine ⟨?_,?_⟩
  · change regularLowLoss allowance θ εslot N≤-7*allowance at hl
    linarith only [hl,hr,hr0]
  · unfold regularFixedOtherLoss
    linarith only [hh,hfee]
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_fixed_loss_ledger
