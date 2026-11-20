/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual Q.2 endpoint funds the entire all-long same-zero branch. -/
import Candidate.C092.transport.MixedUpperFinalAdmission
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Cycle092.RawTicket
variable [QRH.Record1252270103Return.Geometry.Parameters]

/-- The grid uses the upward rounded ORIGINAL Q.2 gamma. At its last
response the native amplified inverse count pays the true Q1 row budget. -/
theorem all_long_count_funds {r : Row} (hr : r∈rows) {δ p : ℝ}
    (hp : r.box.Contains (δ,p)) :
    4*(rowBudget r.B:ℝ)/3 ≤ (5/6-δ)*(rowGamma r.box r.B:ℝ) := by
  have hv:0<(rowV r.box:ℝ):=(by norm_num [Vmin] : (0:ℝ)<Vmin).trans_le
    (row_inner_parameters hr).2.1.1
  have hγ:0 ≤ (rowGamma r.box r.B:ℝ):=(row_inner_parameters hr).2.2.2.2.2.1
  have hround:=rounding (x:=4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ)))
    (n:=10^(13:ℕ)) (by norm_num)
  have hcast : (rowGamma r.box r.B:ℝ)=
      ceilAt (4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ))) (10^(13:ℕ)) := by
    rw [rowGamma,ceil13_cast]
    push_cast
    rfl
  have hlo : 4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ)) ≤ (rowGamma r.box r.B:ℝ) :=
    hcast.symm ▸ hround.2.2.1
  have hm:=(div_le_iff₀ (show 0<3*(rowV r.box:ℝ) by positivity)).mp hlo
  have hvd:(rowV r.box:ℝ) ≤ 5/6-δ := by
    norm_num [rowV]
    linarith only [hp.2.1]
  have hprod:=mul_le_mul_of_nonneg_right hvd hγ
  nlinarith only [hm,hprod]

#print axioms all_long_count_funds
end
end QRH.Cycle092.MixedUpperFinal
