import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

/- Exact normalization of the ORIGINAL source residue integral for arbitrary
   X=Z^xi and total slot length ell. This does not prove a contour deformation
   from the physical probe or either asymptotic estimate for that probe. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.PrincipalExtension
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
variable {κ ι : Type*}

def sourceShift (ξ ℓ : ℝ) : ℝ := ξ/3-5/6+ℓ/6

def slotResidue (χ : Character) (H : ℂ→ℂ) (c a Z : ℝ)
    (S : Finset κ) (T : κ→Finset ι) (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)+(c : ℂ)) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
      H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I)

theorem source_power_identity {Z : ℝ} (hZ : 0<Z) (ξ ℓ : ℝ) (s : ℂ) :
    ((Z^ξ : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ)) * (Z : ℂ)^(s+(sourceShift ξ ℓ : ℂ)) := by
  have hz : (Z : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [←Complex.cpow_mul_ofReal_nonneg hZ.le ξ (1/3),
    ←Complex.cpow_add _ _ hz,←Complex.cpow_add _ _ hz]
  congr 1
  unfold sourceShift
  push_cast
  ring_nf

theorem balanced_source_shift (ℓ b : ℝ) :
    sourceShift ((1-ℓ-b)/2) ℓ = -2/3-b/6 := by
  unfold sourceShift
  ring

theorem rational_source_shift : sourceShift lxRat ellRat = -2/3-bRat/6 := by
  exact balanced_source_shift ellRat bRat

theorem normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (ξ ℓ Y Z : ℝ) (hZ : 0<Z) (s : ℂ) (H B : ℂ→ℂ→ℂ)
    (S : Finset κ) (T : κ→Finset ι) (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M≠0)
    (hB : B 1 (1/6)=slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M^2/6 *
      sourceMultiplier W0 W1 (Z^ξ) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s+(sourceShift ξ ℓ : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) /
        LFunction χ s * slotRatio S T w Q A η s := by
  rw [source_double_residue,source_normalizer_cast S T w hZ,hB]
  have hp := source_power_identity hZ ξ ℓ s
  have hz : (Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ))≠0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio,div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ)) * ((Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s+(sourceShift ξ ℓ : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc,mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (ξ ℓ a Y Z : ℝ) (hZ : 0<Z)
    (H B : ℂ→ℂ→ℂ→ℂ) (S : Finset κ) (T : κ→Finset ι)
    (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M≠0)
    (hm : ∀j∈S,0<slotMass T w j)
    (hB : ∀t : ℝ,B ((a : ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ)≠0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^ξ) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ)) =
        slotResidue χ (fun s=>H s 1 (1/6)) (sourceShift ξ ℓ) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm),?_⟩
  unfold sourceResidueIntegral ProbePhysical.verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [mul_div_assoc,←integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue W0 W1 M χ ξ ℓ Y Z hZ _ (H _) (B _)
    S T w Q A η hc (hB _)

#print axioms normalized_source_double_residue
#print axioms sourceResidueIntegral_normalized
end
end BelowSevenEighthsTight.PrincipalExtension
