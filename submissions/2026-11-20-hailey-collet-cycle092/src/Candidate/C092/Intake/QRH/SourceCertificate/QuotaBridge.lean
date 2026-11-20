/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.RealBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Curved inverse quota and exact fifth-root certificates

This identifies the real radical in the curved quota with a root satisfying
the equation used by the finite checker. It proves that the conservative
rational quota, and hence its short-inverse cost bound, is valid for that real
formula. Admissibility of an inverse estimate with this quota is separate.
-/

set_option autoImplicit false
namespace QRH.SourceCertificate
noncomputable section

/-- The actual curved inverse quota with its real fifth root. -/
def curvedQuota (r : ℝ) : ℝ :=
  (1-r)/2+(11/16)*r-7/24-(5/16)*(7*r^4*(r-2/3))^(1/5 : ℝ)

/-- The scaled real fifth root satisfies the equation checked by the certificate. -/
theorem curvedRoot_equation {r : ℝ} (hr : (3:ℝ)/4 ≤ r) :
    ((5/16)*(7*r^4*(r-2/3))^(1/5 : ℝ))^5 = (5/16)^5*7*r^4*(r-2/3) := by
  have hr0 : 0 ≤ 7*r^4*(r-2/3) := by
    have hdiff : 0 ≤ r-2/3 := by linarith
    positivity
  have hroot : ((7*r^4*(r-2/3))^((5:ℝ)⁻¹))^5 = 7*r^4*(r-2/3) :=
    Real.rpow_inv_natCast_pow hr0 (by norm_num : (5:ℕ) ≠ 0)
  rw [mul_pow]
  have hinv : (1/5:ℝ) = (5:ℝ)⁻¹ := by norm_num
  rw [hinv, hroot]
  ring

/-- A checked rational root enclosure gives a conservative quota for the actual real radical. -/
theorem quota_le_curvedQuota {r rootUpper : ℚ}
    (hlo : (3:ℚ)/4 ≤ r) (hhi : r < (7:ℚ)/9) (hguard : RootGuard r rootUpper) :
    (quota r rootUpper : ℝ) ≤ curvedQuota (r : ℝ) := by
  obtain ⟨hroot0, hroot5⟩ := hguard ⟨hlo,hhi⟩
  have hloR : (3:ℝ)/4 ≤ (r:ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).2 hlo
  have hroot0R : (0:ℝ) ≤ (rootUpper:ℝ) := by exact_mod_cast hroot0
  have hroot5R : (5/16:ℝ)^5*7*(r:ℝ)^4*((r:ℝ)-2/3) ≤ (rootUpper:ℝ)^5 := by
    have hcast : (quotaRadicand r : ℝ) ≤ ((rootUpper^5 : ℚ) : ℝ) := Rat.cast_mono hroot5
    simpa [quotaRadicand] using hcast
  have hbound := curved_quota_lower hroot0R hroot5R (curvedRoot_equation hloR)
  have hnotlo : ¬r < (3:ℚ)/4 := not_lt.mpr hlo
  have hnothi : ¬(7:ℚ)/9 ≤ r := not_le.mpr hhi
  simpa [quota, hnotlo, hnothi, curvedQuota] using hbound

/-- The real short-inverse cost using the actual curved quota. -/
def shortCostCurvedReal (b : ℚ) (e : ℝ) (c : Cutoff) : ℝ :=
  e*((b:ℝ)+(capacity b:ℝ)-(H:ℝ)*((c.inverse:ℝ)+curvedQuota (c.inverse:ℝ))/2)

/-- Using the actual curved quota can only improve the checked conservative short cost. -/
theorem shortCostCurvedReal_le (b : ℚ) (c : Cutoff) {e : ℝ}
    (he : 0 ≤ e) (hlo : (3:ℚ)/4 ≤ c.inverse) (hhi : c.inverse < (7:ℚ)/9)
    (hguard : RootGuard c.inverse c.rootUpper) :
    shortCostCurvedReal b e c ≤ shortCostReal b e c := by
  have hquota := quota_le_curvedQuota hlo hhi hguard
  have hH : (0:ℝ) ≤ (H:ℝ) := by norm_num [H,u]
  unfold shortCostCurvedReal shortCostReal
  apply mul_le_mul_of_nonneg_left _ he
  have h := mul_le_mul_of_nonneg_left hquota hH
  linarith

end
end QRH.SourceCertificate
