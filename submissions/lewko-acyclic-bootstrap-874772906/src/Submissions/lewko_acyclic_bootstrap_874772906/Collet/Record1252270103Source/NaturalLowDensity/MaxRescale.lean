/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/MaxRescale.lean. Original formulas and source attribution retained. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.NaturalLowDensity.Homogeneous

set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity
open Record12518109Gain
noncomputable section
open scoped Classical BigOperators

theorem gain_zero_slots (ν F : ℝ) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hF : 0≤F) :
    gain ν 0 F = 0 := by
  have h0 := gain_nonneg hν0 hν1 (le_refl (0:ℝ)) hF
  have h1 := gain_le_phi ν 0 F
  simp only [mul_zero] at h1
  exact le_antisymm h1 h0

/-- Expanding every surviving subset pays the product of maxima at the
full width, using the proved monotonicity of νS−G(S,F). -/
theorem max_product_of_subproducts {Row Slot : Type*}
    (rows : Finset Row) (slots : Finset Slot) (w : Slot→ℝ) (a : Row→Slot→ℝ)
    (ν F U A loss : ℝ) (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hU : 1≤U) (hA : 0≤A)
    (hw : ∀s∈slots,0≤w s) (ha : ∀u∈rows,∀s∈slots,0≤a u s)
    (hsub : ∀selected : Finset Slot,selected⊆slots →
      (∑u∈rows,∏s∈selected,a u s)≤A*U^(rho ν+ν*(∑s∈selected,w s)-gain ν (∑s∈selected,w s) F+loss)) :
    (∑u∈rows,∏s∈slots,max 1 (a u s)) ≤
      (2^slots.card : ℝ)*A*U^(rho ν+ν*(∑s∈slots,w s)-gain ν (∑s∈slots,w s) F+loss) := by
  have hwidth (selected : Finset Slot) (hs : selected⊆slots) :
      (∑s∈selected,w s)≤∑s∈slots,w s :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun s hs _=>hw s hs)
  have hone (selected : Finset Slot) (hs : selected⊆slots) :
      (∑u∈rows,∏s∈selected,a u s) ≤
        A*U^(rho ν+ν*(∑s∈slots,w s)-gain ν (∑s∈slots,w s) F+loss) :=
    (hsub selected hs).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU
        (by linarith [weighted_exponent_mono (F:=F) hν0 hν1 (hwidth selected hs)])) hA)
  calc
    _ ≤ ∑u∈rows,∏s∈slots,(1+a u s) := by
      apply Finset.sum_le_sum
      intro u hu
      exact Finset.prod_le_prod₀ (fun s hs=>le_trans (by norm_num) (le_max_left _ _))
        (fun s hs=>max_le (by linarith [ha u hu s hs]) (by linarith))
    _ = ∑u∈rows,∑selected∈slots.powerset,∏s∈selected,a u s := by
      apply Finset.sum_congr rfl
      intro u hu
      exact Finset.prod_one_add slots
    _ = ∑selected∈slots.powerset,∑u∈rows,∏s∈selected,a u s := Finset.sum_comm
    _ ≤ ∑selected∈slots.powerset,
        A*U^(rho ν+ν*(∑s∈slots,w s)-gain ν (∑s∈slots,w s) F+loss) :=
      Finset.sum_le_sum (fun selected hs=>hone selected (Finset.mem_powerset.mp hs))
    _ = _ := by simp [Finset.card_powerset,mul_assoc]

theorem gain_rescale (ν S F : ℝ) (hF : 0<F) :
    F*gain ν (S/F) 1 = gain ν S F := by
  have hh := gain_homogeneous ν (S/F) 1 F hF.le
  rw [mul_div_cancel₀ _ hF.ne',mul_one] at hh
  exact hh.symm

theorem homogeneous_power_rescale (ν S F Z : ℝ) (hF : 0<F) (hZ : 0≤Z) :
    (Z^F)^(rho ν+ν*(S/F)-gain ν (S/F) 1) =
      Z^(rho ν*F+ν*S-gain ν S F) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  rw [←gain_rescale ν S F hF]
  field_simp

theorem prime_scale_rescale (Z q w : ℝ) (hZ : 0≤Z) (hq : 0<q) :
    (Z^q)^(w/q) = Z^w := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

theorem normalized_mesh {w μ q : ℝ} (hμ : 0≤μ) (hq : 1/50≤q) (hw : w≤μ/50) :
    w/q≤μ := by
  apply (div_le_iff₀ (show 0<q by linarith)).mpr
  nlinarith

end
end QRH.Record1252270103Source.NaturalLowDensity
