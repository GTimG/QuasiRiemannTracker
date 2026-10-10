import Cycle25.Assembly.Count.Crossing

namespace OAI

noncomputable section
namespace SevenEighths.Cycle25DetectorBranchBudget
open Cycle25DetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x κ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(6*κ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(6*κ)-ν)=
      2*(δ*x)*(1-2*m)/(6*κ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (κ x t r m ε ν : ℝ)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤crossing x κ t) (hleft : t-r-ε≤m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*κ)) :
    0≤(1-2*m)/(6*κ)-ν ∧ (1-2*m)/(6*κ)-ν≤7/37 ∧
      2*m+6*κ*((1-2*m)/(6*κ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 hk hk1 ht ht1
  have hm : 1/4≤m := by linarith [hcross.2.2.1]
  have hd : 0<6*κ := by linarith
  have hc : (1-2*m)/(6*κ)≤5/42 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  rw [mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.Cycle25DetectorBranchBudget
end
end OAI
