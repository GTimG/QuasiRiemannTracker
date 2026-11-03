/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalNormalizedIdentity.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalResidue

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open PrincipalMellinResidues
open ProbePhysical
variable {κ ι : Type*}

theorem source_power_identity_with_perturbed_lengths {Z : ℝ} (hZ : 0 < Z) (s : ℂ) (t : ℝ) :
    ((Z^(xBase-t/2 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-((1/6 : ℝ)+t)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s+(signalOffset : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (xBase-t/2) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  simp only [xBase, signalOffset, skew]
  push_cast
  ring_nf

theorem normalized_source_double_residue_with_perturbed_lengths (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z t : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(xBase-t/2 : ℝ)) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6+t) (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s+(signalOffset : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity_with_perturbed_lengths hZ s t
  have hz : (Z : ℂ)^(((-((1/6 : ℝ)+t)/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-((1/6 : ℝ)+t)/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-((1/6 : ℝ)+t)/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s+(signalOffset : ℂ)) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized_with_perturbed_lengths (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z lengthShift : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6+lengthShift) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^(xBase-lengthShift/2 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6+lengthShift) (slotMass T w) : ℂ)) =
        asymmetricSlotResidue χ (fun s => H s 1 (1/6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral asymmetricSlotResidue
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue_with_perturbed_lengths W0 W1 M χ Y Z lengthShift hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem source_double_residue_integrable_with_perturbed_lengths (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z lengthShift : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => asymmetricKernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(xBase-lengthShift/2 : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hiraw := asymmetric_raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 1/6+lengthShift))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6+lengthShift) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (normalized_source_double_residue_with_perturbed_lengths W0 W1 M χ Y Z lengthShift hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm


end SevenEighths.PrincipalSignalComparison

end

end OAI
