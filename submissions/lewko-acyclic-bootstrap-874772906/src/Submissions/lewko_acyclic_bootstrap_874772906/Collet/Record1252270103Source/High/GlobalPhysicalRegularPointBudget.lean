/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact numerical LOW and HIGH source budgets share one profile control
and retain half the fixed reserve. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularHighPointSomeGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularFixedLoss
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open Set HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentAmplificationChildInput
open Cycle61InitialMass LocalMoment PhysicalAnalytic
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment
open Record1252270103Finite Record1252270103Second CenteredMomentSectorLocalization
open Admission.SelectedRegularHighPoint

def regularPointBox (θ:ℝ):ℝ:=
  ((Finset.Icc (⌊-((256:ℝ)+5*6)/θ⌋:ℤ) ⌊((256:ℝ)+5*6)/θ⌋).card^4:ℕ)

theorem regular_point_budget_exact {α:Type}[Fintype α]
    (n:Source)(N J:ℕ)(θ reserve εslot wmin C Z:ℝ)(W:ℝ→ℂ)(bound:ℕ→ℝ)
    (hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
    (hθ:0<θ)(hes:0<εslot)(hb:∀k,0≤bound k)
    (control:Finset (ℕ×ℕ))(s:Input α)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (ξ:ℝ)(p:Profiles (1/4) (9/4)):
    let P:=regularParameters W θ εslot J bound hWs hW hθ hes hb
    pointBudget n N J θ reserve εslot wmin C Z P control s reflected bin ξ p=
      ∑k∈BufferedSelectedPaidSome.highBins (highBuffer 1 1 εslot (θ/16)) (n.q:ℝ),
        bufferedPaidBudget N (bufferCount (highBuffer 1 1 εslot (θ/16))) J θ 2 P.τ 2 Z
          (highBuffer 1 1 εslot (θ/16)) (frequencyLoss Z 32 ξ+θ) θ θ
          (n.highFee:ℝ) reserve (regularFixedOtherLoss reserve θ εslot N) (2*θ)
          C (forcedProfileCost s)
          (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
          ((p.control control)^2) (regularPointBox θ) k:=by
  dsimp only [pointBudget,regularPointBox,bufferedPaidBudget,regularFixedOtherLoss,
    regularParameters,actualPhysicalParameters,highParameters]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2 <;> ring

theorem regular_point_budgets_paid
    (n:Source)(reserve θ εslot wmin rmin:ℝ)(N J JL:ℕ)
    (hf:FixedBudget reserve 100 100 1 θ)
    (hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
    (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))(hq:1/2≤(n.q:ℝ))
    (W:ℝ→ℂ)(bound:ℕ→ℝ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
    (hb:∀k,0≤bound k)(CL Cpref Cslot CH pcCap:ℝ)(SL SH:Finset (ℕ×ℕ))
    (hCL:0≤CL)(hCpref:0≤Cpref)(hCslot:0≤Cslot)(hCH:0≤CH)(hpc:0≤pcCap):
    let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hb
    ∃C:ℝ,0<C ∧ ∀{α:Type}[Fintype α](s:Input α)(Z ξ height:ℝ)
      (p:Profiles (1/4) (9/4))(reflected:Bool)(bin:ℤ×(Fin 5→ℤ)),
      1<Z→1≤height→forcedProfileCost s≤pcCap→
      0≤frequencyLoss Z 32 ξ+θ→frequencyLoss Z 32 ξ+θ≤2*θ→
      4*regularLowBudget N JL CL Cpref Cslot (forcedProfileCost s)
          (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
          ((p.control SL)^2) height Z (regularLowLoss (n.allowance:ℝ) θ εslot N)+
        pointBudget n N J θ reserve εslot wmin CH Z P SH s reflected bin ξ p≤
      C*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
        (p.control (regularProfileControl SL SH))^2*height^JL*Z^(-(reserve/2)):=by
  intro P
  obtain ⟨C,hC,hpay⟩:=regular_budget_common_control N (bufferCount (highBuffer 1 1 εslot (θ/16)))
    JL J θ 2 P.τ 2 (highBuffer 1 1 εslot (θ/16)) (n.q:ℝ) (reserve/2)
    CL Cpref Cslot CH pcCap (regularPointBox θ) SL SH hCL hCpref hCslot hCH hpc
    (by unfold regularPointBox;positivity) (by norm_num) hq P.hτ.le
  refine ⟨C,hC,?_⟩
  intro α inst s Z ξ height p reflected bin hZ hheight hpc' hω0 hω
  have ht:=regular_parameters_height W θ εslot J bound hWs hW hf.positive hc.slot_pos hb
  have hl:=regular_fixed_loss_ledger reserve (n.allowance:ℝ) θ εslot wmin rmin P.τ
    (frequencyLoss Z 32 ξ+θ) (n.highFee:ℝ) N J hf hc hr hfee P.hτ.le ht.2.2.2.2.2.1 hω
  rw [regular_point_budget_exact]
  exact hpay p Z height (forcedProfileCost s)
    (geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin)
    (frequencyLoss Z 32 ξ+θ) θ θ (n.highFee:ℝ) reserve
    (regularFixedOtherLoss reserve θ εslot N) (2*θ) (regularLowLoss (n.allowance:ℝ) θ εslot N)
    hZ hheight (forcedProfileCost_nonneg s) hpc' (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
    hω0 hf.positive.le hl.1 hl.2
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_point_budget_exact
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_point_budgets_paid
