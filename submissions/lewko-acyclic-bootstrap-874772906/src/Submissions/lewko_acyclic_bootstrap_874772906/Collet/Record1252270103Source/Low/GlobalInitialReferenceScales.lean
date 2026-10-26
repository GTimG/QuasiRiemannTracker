/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal equal-product reference scales with the actual width-local radius. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.LengthGeometry
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open QRH.Record1252270103Restoration QRH.Record1252270103Source
open CenteredMomentEnergyBands

theorem reference_scales (Z X₁ X₂ r B : ℝ) (hZ : 1<Z)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr : 0≤r) (hprod : X₁*X₂≤Z^B) :
    0<X₁*X₂/Z^r ∧ 0<Z^r ∧ (X₁*X₂/Z^r)*Z^r=X₁*X₂ ∧ X₁*X₂/Z^r≤Z^B := by
  have hz:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r
  exact ⟨div_pos (mul_pos hX₁ hX₂) hz,hz,div_mul_cancel₀ _ hz.ne',
    (div_le_self (mul_pos hX₁ hX₂).le (Real.one_le_rpow hZ.le hr)).trans hprod⟩

/-- The reference radius retains the width cell; no replacement by cap occurs. -/
theorem width_local_reference_budget (K bWidth : ℝ) :
    (49/100-K*bWidth)+K*bWidth=(49/100:ℝ) := by ring

/-- Literal raw product, with clipped exponents used only in the domain. -/
theorem global_raw_plain_product (B lam cap Z X₁ X₂ s : ℝ)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hlam : 0≤lam) (hs : 0≤s)
    (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) s 1) :
    X₁*X₂≤Z^B := by
  have hx (X : ℝ) : X≤Z^(length Z X) := by
    rw [length,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
      (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hsum : length Z X₁+length Z X₂≤B := by
    have h:=hadm.2.2.2.2.2.2
    change length Z X₁+length Z X₂+lam*s≤B*1 at h
    nlinarith [mul_nonneg hlam hs]
  calc
    _≤Z^(length Z X₁)*Z^(length Z X₂):=
      mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^(length Z X₁+length Z X₂):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm
    _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.le hsum

/-- The fixed cutoff for ForwardFull and Reference holds on both the original
and equal-product reference pair, with no positive lower ordinary exponent. -/
theorem global_reference_cutoff (B lam cap Z X₁ X₂ s r : ℝ)
    (hZ : 6≤Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hlam : 0≤lam) (hs : 0≤s)
    (hB : B≤1) (hadm : (globalFace B lam cap).Admissible (length Z X₁) (length Z X₂) s 1) :
    (9/4:ℝ)^2*(X₁*X₂/Z^r)*Z^r≤Z^(2:ℝ) := by
  have hZ1 : 1<Z:=by linarith
  have hz:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ1) r
  have he : (9/4:ℝ)^2*(X₁*X₂/Z^r)*Z^r=(9/4:ℝ)^2*X₁*X₂ := by
    rw [mul_assoc,div_mul_cancel₀ _ hz.ne']
    ring
  rw [he]
  exact (global_raw_product_bound hZ1 hZ hX₁ hX₂ hlam hs hadm).trans
    (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.global_reference_cutoff
#print axioms QRH.Record1252270103Low.reference_scales
