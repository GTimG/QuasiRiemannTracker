/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.BudgetProfiles

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators
open Filter

/-- Fixed common logarithmic windows cost an arbitrarily small power,
uniformly over every subsequently chosen pair of endpoints. -/
theorem eventual_common_sobolev_fee (width ε : ℝ)(hw : 0≤width)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀lo hi low high : ℝ,
      lo≤hi →low≤high →hi-lo≤width*Real.log Z →high-low≤width*Real.log Z →
      (1+2*(hi-lo))*(1+2*(high-low))≤(1+2*width)^2*Z^ε := by
  have hlog:=(isLittleO_log_rpow_rpow_atTop (2:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [hlog,eventually_ge_atTop (Real.exp 1),eventually_gt_atTop (1:ℝ)] with Z hlog hZexp hZ
  refine ⟨hZ,?_⟩
  intro lo hi low high hlo hlow hx hy
  have hz : 1≤Real.log Z := by
    have hh:=Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^2≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),one_mul] using hlog
  have hx' : 1+2*(hi-lo)≤(1+2*width)*Real.log Z := by nlinarith
  have hy' : 1+2*(high-low)≤(1+2*width)*Real.log Z := by nlinarith
  have hm:=mul_le_mul hx' hy' (by linarith : 0≤1+2*(high-low)) (by positivity : 0≤(1+2*width)*Real.log Z)
  exact hm.trans ((show ((1+2*width)*Real.log Z)*((1+2*width)*Real.log Z)=
      (1+2*width)^2*(Real.log Z)^2 by ring).le.trans
    (mul_le_mul_of_nonneg_left hp (sq_nonneg _)))

/-- The erased-slot cardinality is bounded by the original ambient
dictionary, never by a Fourier-row count. -/
theorem deleted_slots_fee {α : Type*}[Fintype α](S F : Finset α)(N : ℕ)
    (hN : Fintype.card α≤N)(C Z exponent : ℝ)(hC : 0≤C)(hZ : 1≤Z)(he : 0≤exponent) :
    (C*Z^exponent)^((S\F).card)≤(max 1 C)^N*Z^(exponent*(N:ℝ)) := by
  have hk : (S\F).card≤N := (Finset.card_le_univ _).trans hN
  have hpow : 1≤max 1 C*Z^exponent :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ he)
  have hCZ : C*Z^exponent≤max 1 C*Z^exponent :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply (pow_le_pow_left₀ (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hZ) _)) hCZ _).trans
  apply (pow_le_pow_right₀ hpow hk).trans_eq
  rw [mul_pow,←Real.rpow_mul_natCast (zero_le_one.trans hZ)]

/-- The actual common radius and missing-radical powers cancel against
the complete coefficient. Every remaining small loss stays explicit. -/
theorem common_raw_power_cancellation (Z missing M E ε : ℝ)(hZ : 0<Z) :
    Z^missing*Z^(E-missing-M)*Z^(M+ε)=Z^(E+ε) := by
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.eventual_common_sobolev_fee
#print axioms OAI.SevenEighths.Record12518109Raw.deleted_slots_fee
#print axioms OAI.SevenEighths.Record12518109Raw.common_raw_power_cancellation
