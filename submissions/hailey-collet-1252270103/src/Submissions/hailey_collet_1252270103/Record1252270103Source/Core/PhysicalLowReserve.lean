/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal LOW scalar price with the conservative node plain budget.
All losses are numerical; no source energy or desired capacity is assumed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.PhysicalLowGuard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalLowReserve
noncomputable section
open Record1252270103Finite Record1252270103StepScalar

def plainBudget (n : Source) (b width : ℝ) : ℝ :=
  sourceTReal n b+(n.L:ℝ)*width

def nodeGain (n low : Source) (width : ℝ) : ℝ :=
  (n.lowFee:ℝ)-(n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ)

theorem conservative_weak_cap (K : ℚ) (n low : Source) (b width : ℝ)
    (hg : RealGeometry K n low b) (hL : 0≤(n.L:ℝ)) (hw : 0≤width) :
    ((low.B:ℝ)*sourceFReal n low b-plainBudget n b width)/(low.L:ℝ)≤
      (low.cap:ℝ)*sourceFReal n low b := by
  apply le_trans ?_ hg.weak_cap
  apply div_le_div_of_nonneg_right _ hg.lowL_pos.le
  have hh := mul_nonneg hL hw
  dsimp only [plainBudget]
  linarith only [hh]

theorem conservative_gain (K : ℚ) (n low : Source) (b width : ℝ)
    (hg : RealGeometry K n low b) :
    sourceAReal n low b-(n.q:ℝ)*
      (b+(plainBudget n b width-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ))=
      nodeGain n low width := by
  calc
    _=(sourceAReal n low b-(n.q:ℝ)*
        (b+(sourceTReal n b-(low.B:ℝ)*sourceFReal n low b)/(low.L:ℝ)))-
        (n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ) := by
      dsimp only [plainBudget]
      ring
    _=nodeGain n low width := by rw [hg.fee_identity];rfl

/-- The common width step costs at most one sixteenth of an allowance. -/
theorem width_charge (n low : Source) (width : ℝ)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1) (hlam : 1≤(low.L:ℝ))
    (hw : width≤PhysicalLowGuard.step n) :
    (n.q:ℝ)*(n.L:ℝ)*width/(low.L:ℝ)≤(n.allowance:ℝ)/16 := by
  have hplain : (n.L:ℝ)*width≤(n.allowance:ℝ)/16 := by
    apply (mul_le_mul_of_nonneg_left hw hL).trans
    rw [PhysicalLowGuard.step,←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<16*((n.L:ℝ)+1))).mpr
    nlinarith only [he]
  have hq := mul_le_mul_of_nonneg_left hplain hq0
  have hq' := mul_le_mul_of_nonneg_right hq1 (div_nonneg he (by norm_num : (0:ℝ)≤16))
  have hl := mul_le_mul_of_nonneg_left hlam (div_nonneg he (by norm_num : (0:ℝ)≤16))
  apply (div_le_iff₀ (zero_lt_one.trans_le hlam)).mpr
  nlinarith only [hq,hq',hl]

/-- The node's two fee gates leave at least thirteen and a half allowances. -/
theorem minimum_gain_reserve (K : ℚ) (n low : Source) (b width : ℝ)
    (hg : RealGeometry K n low b)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1) (hlam : 1≤(low.L:ℝ))
    (hB : 0≤(low.B:ℝ)) (hh : 0≤(low.cap:ℝ))
    (hw : width≤PhysicalLowGuard.step n) :
    (27/2:ℝ)*(n.allowance:ℝ)≤min (sourceAReal n low b) (nodeGain n low width) := by
  have hc := width_charge n low width he hL hq0 hq1 hlam hw
  have hp : 0≤((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ))*(n.allowance:ℝ) :=
    mul_nonneg (add_nonneg (div_nonneg (mul_nonneg hq0 hB) hg.lowL_pos.le)
      (mul_nonneg hq0 hh)) he
  have hf := hg.low_fee_room
  have ha := hg.a_allowance
  apply le_min
  · linarith only [ha,he]
  · dsimp only [nodeGain]
    nlinarith only [hc,hp,hf,he]

/-- Every displayed scalar error may be as large as a quarter allowance.
This bound retains both affine and capped erasure branches. -/
theorem error_budget (e q B lam h rho loss mesh err errv radialRound : ℝ)
    (he : 0≤e) (hq0 : 0≤q) (hq1 : q≤1)
    (hB0 : 0≤B) (hB1 : B≤1) (hlam : 1≤lam) (hh0 : 0≤h) (hh1 : h≤1)
    (hρ : rho≤e/4) (hloss : loss≤e/4) (hm : mesh≤e/4)
    (herr : err≤e/4) (herrv : errv≤e/4) (hrad : radialRound≤e/4) :
    q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound≤(3/2)*e := by
  have hBr : B*rho≤e/4 :=
    (mul_le_mul_of_nonneg_left hρ hB0).trans (by
      simpa using mul_le_mul_of_nonneg_right hB1 (div_nonneg he (by norm_num : (0:ℝ)≤4)))
  have hhr : h*rho≤e/4 :=
    (mul_le_mul_of_nonneg_left hρ hh0).trans (by
      simpa using mul_le_mul_of_nonneg_right hh1 (div_nonneg he (by norm_num : (0:ℝ)≤4)))
  have haff : (B*rho+loss)/lam≤e/2 := by
    apply (div_le_iff₀ (zero_lt_one.trans_le hlam)).mpr
    have hh := mul_le_mul_of_nonneg_left hlam (div_nonneg he (by norm_num : (0:ℝ)≤2))
    nlinarith only [hBr,hloss,hh]
  have hmax : max ((B*rho+loss)/lam) (h*rho)≤e/2 :=
    max_le haff (by linarith only [hhr,he])
  have hq := mul_le_mul_of_nonneg_left (add_le_add hmax hm) hq0
  have hq' := mul_le_mul_of_nonneg_right hq1 (by positivity : 0≤e/2+e/4)
  nlinarith only [hq,hq',herr,herrv,hrad]

theorem node_price_reserve (K : ℚ) (n low : Source) (b width rho loss mesh err errv radialRound : ℝ)
    (hg : RealGeometry K n low b)
    (he : 0≤(n.allowance:ℝ)) (hL : 0≤(n.L:ℝ))
    (hq0 : 0≤(n.q:ℝ)) (hq1 : (n.q:ℝ)≤1) (hlam : 1≤(low.L:ℝ))
    (hB0 : 0≤(low.B:ℝ)) (hB1 : (low.B:ℝ)≤1)
    (hh0 : 0≤(low.cap:ℝ)) (hh1 : (low.cap:ℝ)≤1)
    (hw : width≤PhysicalLowGuard.step n)
    (hρ : rho≤(n.allowance:ℝ)/4) (hloss : loss≤(n.allowance:ℝ)/4)
    (hm : mesh≤(n.allowance:ℝ)/4) (herr : err≤(n.allowance:ℝ)/4)
    (herrv : errv≤(n.allowance:ℝ)/4) (hrad : radialRound≤(n.allowance:ℝ)/4) :
    -min (sourceAReal n low b) (nodeGain n low width)+
      (n.q:ℝ)*(max (((low.B:ℝ)*rho+loss)/(low.L:ℝ)) ((low.cap:ℝ)*rho)+mesh)+
      err+errv+radialRound≤-12*(n.allowance:ℝ) := by
  have hmin := minimum_gain_reserve K n low b width hg he hL hq0 hq1 hlam hB0 hh0 hw
  have herrs := error_budget (n.allowance:ℝ) (n.q:ℝ) (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)
    rho loss mesh err errv radialRound he hq0 hq1 hB0 hB1 hlam hh0 hh1 hρ hloss hm herr herrv hrad
  linarith only [hmin,herrs]

end
end QRH.Record1252270103Source.PhysicalLowReserve
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.conservative_weak_cap
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.conservative_gain
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.width_charge
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.minimum_gain_reserve
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.error_budget
#print axioms QRH.Record1252270103Source.PhysicalLowReserve.node_price_reserve
