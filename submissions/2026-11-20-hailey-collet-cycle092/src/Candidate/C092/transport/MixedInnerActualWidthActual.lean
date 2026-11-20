/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.MixedInnerActualWidthCheck00
import Candidate.C092.transport.MixedInnerActualWidthCheck01
import Candidate.C092.transport.MixedInnerActualWidthCheck02
import Candidate.C092.transport.MixedInnerActualWidthCheck03
import Candidate.C092.transport.MixedInnerActualWidthCheck04
import Candidate.C092.transport.MixedInnerActualWidthCheck05
import Candidate.C092.transport.MixedInnerActualWidthCheck06
import Candidate.C092.transport.MixedInnerActualWidthCheck07
import Candidate.C092.transport.MixedInnerActualWidthCheck08
import Candidate.C092.transport.MixedInnerActualWidthCheck09
import Candidate.C092.transport.MixedInnerActualWidthCheck10
import Candidate.C092.transport.MixedInnerActualWidthCheck11
import Candidate.C092.transport.MixedInnerActualWidthCheck12
import Candidate.C092.transport.MixedInnerActualWidthCheck13
import Candidate.C092.transport.MixedInnerActualWidthCheck14
import Candidate.C092.transport.MixedInnerActualWidthCheck15
import Candidate.C092.transport.MixedInnerActualWidthCheck16
import Candidate.C092.transport.MixedInnerActualWidthCheck17
import Candidate.C092.transport.MixedInnerActualWidthCheck18
import Candidate.C092.transport.MixedInnerActualWidthCheck19
import Candidate.C092.transport.MixedInnerActualWidthCheck20
import Candidate.C092.transport.MixedInnerActualWidthCheck21
import Candidate.C092.transport.MixedInnerActualWidthCheck22
import Candidate.C092.transport.MixedInnerActualWidthCheck23
import Candidate.C092.transport.MixedInnerActualWidthCheck24
import Candidate.C092.transport.MixedInnerActualWidthCheck25
import Candidate.C092.transport.MixedInnerActualWidthCheck26
import Candidate.C092.transport.MixedInnerActualWidthCheck27
import Candidate.C092.transport.MixedInnerActualWidthCheck28
import Candidate.C092.transport.MixedInnerActualWidthCheck29
import Candidate.C092.transport.MixedInnerActualWidthCheck30
import Candidate.C092.transport.MixedInnerActualWidthCheck31
import Candidate.C092.transport.MixedInnerActualWidthGeometry
set_option autoImplicit false
namespace QRH.Cycle092.MixedInnerActualWidth
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.RawTicket
theorem all_rows_width_checked : rows.all widthCheck = true := by
  simp only [rows,List.all_append,group00_width_checked, group01_width_checked, group02_width_checked, group03_width_checked, group04_width_checked, group05_width_checked, group06_width_checked, group07_width_checked, group08_width_checked, group09_width_checked, group10_width_checked, group11_width_checked, group12_width_checked, group13_width_checked, group14_width_checked, group15_width_checked, group16_width_checked, group17_width_checked, group18_width_checked, group19_width_checked, group20_width_checked, group21_width_checked, group22_width_checked, group23_width_checked, group24_width_checked, group25_width_checked, group26_width_checked, group27_width_checked, group28_width_checked, group29_width_checked, group30_width_checked, group31_width_checked,Bool.and_true]

theorem actual_row_width_guards {r : Row} (hr : r∈rows) :
    widthLo≤(lowerM r.box:ℝ)-(rowGamma r.box r.B:ℝ)-(lambdaX r:ℝ)-3/10^(13:ℕ) ∧
    (upperM r.box:ℝ)+(lambdaY r:ℝ)+1/10^(13:ℕ)≤ widthHi := by
  have h:=List.all_eq_true.mp all_rows_width_checked r hr
  simp only [widthCheck,decide_eq_true_eq] at h
  constructor
  · have hh:=(Rat.cast_le (K:=ℝ)).mpr h.1
    norm_num only [Rat.cast_sub,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at hh
    simpa only [widthLo,widthHi,show (10:ℝ)^13=10000000000000 by norm_num] using hh
  · have hh:=(Rat.cast_le (K:=ℝ)).mpr h.2
    norm_num only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] at hh
    simpa only [widthLo,widthHi,show (10:ℝ)^13=10000000000000 by norm_num] using hh

theorem row_budget_nonneg (r : Row) : 0≤(rowBudget r.B:ℝ) := by
  unfold rowBudget
  push_cast
  positivity

theorem actual_quotient_bounds {r : Row} (hr : r∈rows) {delta p k q0 : ℝ}
    (hp : r.box.Contains (delta,p)) (hk : (lowerK r.box:ℝ)≤ k)
    (hq0 : 0≤ q0) (hq : q0≤(rowBudget r.B:ℝ)) :
    0< delta ∧ 0< k ∧
    4*q0/(3*delta*k)≤(lambdaX r:ℝ) ∧ 2*q0/(3*delta*k)≤(lambdaY r:ℝ) := by
  have hh:=row_endpoint_hull hr
  have ha0 : 0<(r.box.uLo:ℝ):=(by norm_num [dLo] : (0:ℝ)< dLo).trans_le hh.1.1
  have hdelta : 0< delta:=ha0.trans_le hp.1
  have he : (r.box.vHi:ℝ)≤1/2:=by simpa only [pHi] using hh.2.2.2.2
  have hk0 : 0<(lowerK r.box:ℝ):=by
    simp only [lowerK,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    linarith only [he]
  have hkpos:=hk0.trans_le hk
  have hprod:=mul_le_mul hp.1 hk hk0.le hdelta.le
  have hden : 3*(r.box.uLo:ℝ)*(lowerK r.box:ℝ)≤3*delta*k:=by linarith only [hprod]
  have hden0 : 0<3*(r.box.uLo:ℝ)*(lowerK r.box:ℝ):=by positivity
  have hx:=div_le_div₀ (show 0≤4*(rowBudget r.B:ℝ) by have:=row_budget_nonneg r;positivity)
    (show 4*q0≤4*(rowBudget r.B:ℝ) by linarith only [hq]) hden0 hden
  have hy:=div_le_div₀ (show 0≤2*(rowBudget r.B:ℝ) by have:=row_budget_nonneg r;positivity)
    (show 2*q0≤2*(rowBudget r.B:ℝ) by linarith only [hq]) hden0 hden
  refine ⟨hdelta,hkpos,?_,?_⟩
  · simpa only [lambdaX,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hx
  · simpa only [lambdaY,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat] using hy

/-- Genuine P12 upgrade: insufficient native saturation count on the actual
supporting lengths forces the precise inner source interval. -/
theorem actual_width_of_insufficient {row : Row} (hr : row∈rows)
    {delta p k r m t0 H q0 xi ann : ℝ}
    (hp : row.box.Contains (delta,p)) (hk : (lowerK row.box:ℝ)≤ k)
    (hq0 : 0≤ q0) (hq : q0≤(rowBudget row.B:ℝ))
    (htlo : (lowerM row.box:ℝ)≤ t0/3) (hthi : t0/3≤(upperM row.box:ℝ))
    (hxi : xi≤(rowGamma row.box row.B:ℝ)) (hann : ann≤3/10^(13:ℕ))
    (hsupport : t0-xi-ann≤ r+m)
    (hinsuff : delta*MixedCenteredFaces.center k r m (t0/3) H<4*q0/3) :
    widthLo≤ m ∧ m≤ widthHi := by
  obtain ⟨hd,hkpos,hx,hy⟩:=actual_quotient_bounds hr hp hk hq0 hq
  have hs:=insufficient_actual_range hd hkpos hinsuff hsupport
  have hw:=actual_row_width_guards hr
  constructor <;> linarith only [hs.1,hs.2,hw.1,hw.2,htlo,hthi,hxi,hann,hx,hy]

end
end QRH.Cycle092.MixedInnerActualWidth
#print axioms QRH.Cycle092.MixedInnerActualWidth.all_rows_width_checked
#print axioms QRH.Cycle092.MixedInnerActualWidth.actual_width_of_insufficient
