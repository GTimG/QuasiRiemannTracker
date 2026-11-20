/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Pay the actual dyadic factors, independently of the live first label and
whole-slot assignment, at one eventual threshold for a fixed slot count. -/
import Candidate.C092.transport.FirstGroupWindow
import Candidate.C092.transport.FixedRegularPrice
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter QRH.SourceCertificate QRH.Cycle092.PackedPrice
namespace QRH.Cycle092.FixedFramePacking

theorem early_dyad_cost (N:ℕ) (fee:ℝ) (hf:0<fee) :
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀ j ≤ N,
      Real.logb Z (64*((2:ℝ)^j)^4) ≤ fee ∧ Real.logb Z ((2:ℝ)^j) ≤ fee := by
  filter_upwards [eventually_gt_atTop (1:ℝ),(tendsto_rpow_atTop hf).eventually_ge_atTop (64*((2:ℝ)^N)^4)] with Z hZ hZc
  refine ⟨hZ,?_⟩
  intro j hj
  have hle : (2:ℝ)^j  ≤  2^N := pow_le_pow_right₀ (by norm_num) hj
  have hN:1 ≤ (2:ℝ)^N:=one_le_pow₀ (by norm_num)
  have hp:0<((2:ℝ)^j):=by positivity
  have h₁:64*((2:ℝ)^j)^4  ≤  Z^fee := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le hle _) (by norm_num : (0:ℝ) ≤ 64)).trans hZc
  have h₂: (2:ℝ)^j  ≤  Z^fee := by
    have hpow:(2:ℝ)^N  ≤  ((2:ℝ)^N)^4 := by simpa only [pow_one] using
      (pow_le_pow_right₀ hN (by norm_num : 1 ≤ 4))
    have hh : (2:ℝ)^j  ≤  ((2:ℝ)^N)^4 := hle.trans hpow
    exact hh.trans ((by linarith only [show 0 ≤ ((2:ℝ)^N)^4 by positivity] : ((2:ℝ)^N)^4  ≤  64*((2:ℝ)^N)^4).trans hZc)
  constructor
  · have hh:=Real.logb_le_logb_of_le hZ (by positivity : 0<64*((2:ℝ)^j)^4) h₁
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  · have hh:=Real.logb_le_logb_of_le hZ hp h₂
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

/-- Combine uniform group geometry with the retained positive reserve. A
filled prefix is within one mesh of u. The exhausted source uses the exact
zero-slot price and therefore also pays its actual, possibly zero, width. -/
theorem paid_group_prices {u' M mesh collar aRoot dyad : ℝ} (hm:0 ≤ mesh)
    (hlo:1-6*u'+mesh-collar  ≤  M) (hu:u'  ≤  (u:ℝ)) (hu0:0 ≤ u')
    (hhi:M  ≤  2*aRoot+2*dyad+mesh) (hcap:aRoot ≤ 9179599/10000000)
    (hd:dyad ≤ 1/100) (hm1:mesh ≤ 1/100) (hc:0 ≤ collar)
    (hpaid:mesh+collar ≤ terminalReserve) :
    0 ≤ M ∧ M ≤ 19/10 ∧
    (∀ w p s, (u:ℝ)-mesh  ≤  u' →
       (regular terminalReserve terminalReserve_le).f w p s M  ≤  u') ∧
    ((5/6:ℝ)*max 0 (1-6*u'-M)  ≤  collar) := by
  have hR:=terminalReserve_pos
  have hH : (H:ℝ)=1-6*(u:ℝ) := by norm_num [H]
  have hcollar : collar ≤ terminalReserve := by linarith
  have hM0:0 ≤ M := by
    have hb:(u:ℝ)=3/1000000:=by norm_num [u]
    have ht:terminalReserve ≤ 1/100:=by norm_num [terminalReserve,rho]
    linarith
  have hMF:(H:ℝ) ≤ M+collar:=by linarith
  refine ⟨hM0,by linarith,?_,?_⟩
  · intro w p s hfill
    have h:=filled terminalReserve terminalReserve_le w p s M collar hc hMF
    linarith
  · have h:=max_le hc (by linarith : 1-6*u'-M ≤ collar)
    linarith

#print axioms early_dyad_cost
#print axioms paid_group_prices
end QRH.Cycle092.FixedFramePacking
