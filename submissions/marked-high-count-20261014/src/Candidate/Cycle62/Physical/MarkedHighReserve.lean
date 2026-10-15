import Candidate.Cycle62.Physical.NonexceptionalLedger

namespace Cycle62.Physical
noncomputable section
open Cycle62.Arithmetic OAI.SevenEighths.LocalMoment

/-- Quantitative reserve growth above the lower high-zero cutoff. -/
theorem high_main_reserve_increase {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤3/4) :
    highMainReserve b q0+(δ-q0)/4≤highMainReserve b δ := by
  have hδ : 0<5-2*δ := by linarith [hd.2]
  have hq : 0<5-2*q0 := by norm_num [q0]
  have hden : 0<3*(5-2*δ)*(5-2*q0) := by positivity
  have hn : 0≤50*(1-6*amp b) := by
    have ha := (amp_bounds hb).2
    linarith
  have hprod : 3*(5-2*δ)*(5-2*q0)≤3*(5-2*q0)^2 := by nlinarith [hd.1]
  have hfrac := div_le_div_of_nonneg_left hn hden hprod
  have hbase := high_derivative_reserve hb
  have hder : 1/4≤50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b := by linarith
  have hid : highMainReserve b δ-highMainReserve b q0=
      (δ-q0)*(50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b) := by
    unfold highMainReserve unmarkedDensity
    field_simp [hδ.ne',hq.ne',show 5-δ*2≠0 by linarith [hd.2]]
    ring
  have hh := mul_le_mul_of_nonneg_left hder (sub_nonneg.mpr hd.1)
  rw [←hid] at hh
  linarith

/-- The marked-count saving pays for the enlarged affine intercept. -/
theorem marked_high_reserve {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤3/4) :
    720486667/30493190000000≤highMainReserve b δ+1/625 := by
  have hh := high_main_reserve_bound hb hd
  linarith

/-- The unmarked argument already suffices above delta = 7/10. -/
theorem unmarked_upper_high_reserve {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : 7/10≤δ ∧ δ≤3/4) :
    720486667/30493190000000≤highMainReserve b δ := by
  have hδ : q0≤δ ∧ δ≤3/4 := by norm_num [q0];constructor <;> linarith [hd.1,hd.2]
  have hh := high_main_reserve_increase hb hδ
  have hr : highMainReserve b q0= -9517022237/6098638000000 := by
    have hρ : unmarkedDensity q0=rho0 := by norm_num [unmarkedDensity,q0,rho0]
    simpa only [highMainReserve,hρ] using high_reserve b
  rw [hr] at hh
  norm_num [q0] at hh
  linarith [hd.1]

end
end Cycle62.Physical
#print axioms Cycle62.Physical.marked_high_reserve
#print axioms Cycle62.Physical.unmarked_upper_high_reserve
