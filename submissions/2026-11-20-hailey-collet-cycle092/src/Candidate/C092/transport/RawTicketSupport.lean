/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Closed original raw support, physical reciprocal order, and cutoff separation. -/
import Candidate.C092.transport.RawTicketActual
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090

theorem original_reciprocal_order {dn : ℝ} (hdn : dn≤downMax) :
    tHi<1/(hUpper+rowPad)-dn := by
  have hp0 : 0≤rowPad := by unfold rowPad;positivity
  have hpad : rowPad≤1/10^(20:ℕ) := by
    change 1/(10:ℝ)^258≤1/(10:ℝ)^20
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have hr:=one_div_le_one_div_of_le (show 0<hUpper+rowPad by norm_num [hUpper];linarith only [hp0])
    (show hUpper+rowPad≤hUpper+1/10^(20:ℕ) by linarith only [hpad])
  have hn : tHi<1/(hUpper+1/10^(20:ℕ))-downMax := by norm_num [tHi,hUpper,downMax]
  linarith only [hr,hn,hdn]

theorem original_support_geometry {t₀ t₁ γ x y : ℝ}
    (ht₀ : tLo≤t₀) (ht₁ : t₁≤tHi)
    (hg : γ≤gammaMax) (hx : x≤xMax) (hy : y≤yMax) :
    1<t₀-γ ∧ t₁<3/2 ∧
    t₀-γ>2*t₁/3+x+oldAnn ∧
    18/25<2*t₀/3-γ-y-3*oldAnn ∧
    2*t₁/3+2*max x y+3*oldAnn<311/400 ∧
    rawYLo≤t₀/3-γ-x-2*oldAnn ∧ t₁/3+y+oldAnn≤rawYHi := by
  have hmax : max x y≤xMax := max_le hx (hy.trans (by norm_num [xMax,yMax]))
  norm_num [tLo,tHi,gammaMax,xMax,yMax,oldAnn,rawYLo,rawYHi] at ht₀ ht₁ hg hx hy ⊢
  dsimp [xMax] at hmax
  constructor;· linarith only [ht₀,hg]
  constructor;· linarith only [ht₁]
  constructor;· linarith only [ht₀,hg,ht₁,hx]
  constructor;· linarith only [ht₀,hg,hy]
  constructor;· linarith only [ht₁,hmax]
  constructor <;> linarith only [ht₀,hg,hx,ht₁,hy]

/-- Positive contour damping at every CLOSED actual point of every mixed row.
The admitted physical cap remains the original 17/200. -/
theorem actual_contour_damping {r : QRH.Cycle092.TopData.Row} (hr : r∈QRH.Cycle092.TopData.rows)
    {point : QRH.Coverage.Point} (hp : r.box.Contains point) :
    0<point.1*(1-point.2)/2-17/200 := by
  have he:=row_endpoint_hull hr
  have hd : dLo≤point.1 := he.1.1.trans hp.1
  have hv : point.2≤pHi := hp.2.2.2.trans he.2.2.2.2
  have hd0 : 0≤point.1 := (by norm_num [dLo] : (0:ℝ)≤dLo).trans hd
  have hm:=mul_le_mul hd (by linarith only [hv] : 1-pHi≤1-point.2) (by norm_num [pHi]) hd0
  norm_num [dLo,pHi] at hm
  linarith only [hm]

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.actual_contour_damping
#print axioms QRH.Cycle092.RawTicket.original_reciprocal_order
