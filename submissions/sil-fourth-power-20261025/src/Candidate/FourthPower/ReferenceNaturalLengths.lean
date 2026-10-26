/- Copyright (c) 2026 Sil. Apache-2.0.
Actual lengths of the original or naturally reflected second factor. The
choice is made at the square root of a common conductor cap, retaining the
annular cutoff and every extraction denominator in the resulting bounds.
-/
import Candidate.FourthPower.ReferenceNaturalData

set_option autoImplicit false
namespace Candidate.FourthPower.ReferenceNaturalLengths
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentReflectionDeletion CenteredMomentSectorLocalization
open ReferenceNaturalData
local notation "Id" => Ideal HeckeFamily.O

def selectedLength {χ : Character} (r : Data χ) (X U : ℝ) (n : ℤ)
    (D : Finset Id) (H : SmoothIdeal r.support) : ℝ :=
  if X ≤ Real.sqrt U then X else dyadicScale n*r.dualLength X D H

theorem selected_positive {χ : Character} (r : Data χ) (X U : ℝ) (n : ℤ)
    (hX : 0 < X) (D : Finset Id) (hD : D ∈ r.support.powerset)
    (H : SmoothIdeal r.support) : 0 < selectedLength r X U n D H := by
  unfold selectedLength
  split_ifs
  · exact hX
  · exact mul_pos (dyadicScale_pos n)
      (r.dualLength_bound X ((χ.modulus.absNorm : ℝ)/X) hX
        (by rw [div_mul_cancel₀ _ hX.ne']) D hD H).1

theorem selected_bounds {χ : Character} (r : Data χ) (X U R : ℝ) (n : ℤ)
    (hX : 0 < X) (hU : 0 ≤ U) (hR : 1 ≤ R)
    (hmod : (χ.modulus.absNorm : ℝ) ≤ U) (hn : Retained R n)
    (D : Finset Id) (hD : D ∈ r.support.powerset) (H : SmoothIdeal r.support) :
    selectedLength r X U n D H ≤ 4*R*Real.sqrt U ∧
    selectedLength r X U n D H ≤ 4*R*(U/X) := by
  have hs := Real.sqrt_nonneg U
  have hs2 := Real.sq_sqrt hU
  have hfour : 1 ≤ 4*R := by linarith
  have hratio : 0 ≤ U/X := div_nonneg hU hX.le
  unfold selectedLength
  split_ifs with hsmall
  · have hh : X ≤ U/X := (le_div_iff₀ hX).mpr (by nlinarith)
    exact ⟨hsmall.trans (le_mul_of_one_le_left hs hfour),
      hh.trans (le_mul_of_one_le_left hratio hfour)⟩
  · have hb := (r.dualLength_bound X (U/X) hX
        (by rw [div_mul_cancel₀ _ hX.ne']; exact hmod) D hD H).2
    have hratio' : U/X ≤ Real.sqrt U := (div_le_iff₀ hX).mpr (by nlinarith)
    have hbase : dyadicScale n*r.dualLength X D H ≤ 4*R*(U/X) :=
      mul_le_mul (retained_scale_le R n hn) hb
        (r.dualLength_bound X (U/X) hX
          (by rw [div_mul_cancel₀ _ hX.ne']; exact hmod) D hD H).1.le (by linarith)
    exact ⟨hbase.trans (mul_le_mul_of_nonneg_left hratio' (by linarith)),hbase⟩

/-- Both caps apply to the same selected, shortened column. The second cap
has exactly the d₂/(d₁ f) ratio paid by KernelCommonScalarMass. -/
theorem extracted_column_bounds {χ : Character} (r : Data χ)
    (X₁ X₂ U V d₁ d₂ f R : ℝ) (n : ℤ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hd₁ : 1 ≤ d₁) (hd₂ : 0 < d₂) (hf : 1 ≤ f) (hR : 1 ≤ R)
    (hmod : (χ.modulus.absNorm : ℝ) ≤ U) (hn : Retained R n)
    (D : Finset Id) (hD : D ∈ r.support.powerset) (H : SmoothIdeal r.support) :
    let N := (X₁/d₁)*selectedLength r (X₂/d₂) U n D H*(V/f)
    N ≤ 4*R*X₁*V*Real.sqrt U ∧
    N ≤ 4*R*(X₁*V*U/X₂)*(d₂/(d₁*f)) := by
  have hd₁p : 0 < d₁ := zero_lt_one.trans_le hd₁
  have hfp : 0 < f := zero_lt_one.trans_le hf
  have hb := selected_bounds r (X₂/d₂) U R n (div_pos hX₂ hd₂) hU hR hmod hn D hD H
  have hfirst : X₁/d₁ ≤ X₁ := (div_le_iff₀ hd₁p).mpr (by nlinarith)
  have hmarked : V/f ≤ V := (div_le_iff₀ hfp).mpr (by nlinarith)
  dsimp only
  constructor
  · calc
      _ ≤ X₁*(4*R*Real.sqrt U)*V :=
        mul_le_mul (mul_le_mul hfirst hb.1
          (selected_positive r _ _ _ (div_pos hX₂ hd₂) D hD H).le hX₁.le)
          hmarked (div_nonneg hV hfp.le) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (X₁/d₁)*(4*R*(U/(X₂/d₂)))*(V/f) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb.2 (div_pos hX₁ hd₁p).le) (div_nonneg hV hfp.le)
      _ = _ := by field_simp

end
end Candidate.FourthPower.ReferenceNaturalLengths
