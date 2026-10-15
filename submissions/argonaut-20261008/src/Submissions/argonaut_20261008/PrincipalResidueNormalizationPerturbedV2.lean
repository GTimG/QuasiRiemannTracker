import Submissions.argonaut_20261008.PrincipalGeometryPerturbedV2
import Submissions.argonaut_20261008.PrincipalSameSCutoffsV2
import Submissions.argonaut_20261008.PrincipalSignalFiniteSigma
import Submissions.argonaut_20261008.PrincipalSigmaAliasesV2
import Submissions.argonaut_20261008.PrincipalSignalBoundsV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

namespace OAI.SevenEighths.LocalPrincipalResidueV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter Set MeasureTheory Asymptotics
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeRaySlots ProbePrincipalPhysical ProbePrincipalNormalized
open PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbeMellinBoundary ProbePrincipalContours
open LocalPrincipalGeometryV2 LocalPrincipalCutoffsV2
local notation "Id" => Ideal HeckeFamily.O

/- New total-E residue normalization and genuine Sigma finite-slot capsule. NOT_RUN. -/
theorem raw_inverse_ae_reciprocal_v2 (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

variable {κ ι : Type*}

abbrev SlotBounds_v2 (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ) (P : ℝ) : Prop :=
  SlotBoundsSigma analyticBoundaryB0 S T w Q A eta P

-- `slotRatio_error_b0` is supplied by the actual sigma finite-slot alias.
-- `slotRatio_bound_b0` is supplied by the actual sigma finite-slot alias.
-- `principalSlot_differentiableAt_b0` is supplied by the actual sigma finite-slot alias.
-- `slotRatio_continuous_line_b0` is supplied by the actual sigma finite-slot alias.
theorem slotResidue_eq_reciprocal_v2 (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal_v2 χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

theorem kernel_continuous_v2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0 < s.re})
    {a Z : ℝ} (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (LocalPrincipalSignalShiftV2.quotient_holomorphic_pc2 χ H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound_v2 (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, analyticBoundaryB0 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := LocalPrincipalSignalShiftV2.quotient_polynomial_bound_pc2 χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable_v2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0 < s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous_v2 χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound_v2 χ H hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound_v2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0 < s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds_v2 S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(analyticBoundaryB0 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable_v2 χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line_actual_b0 S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound_actual_b0 S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error_actual_b0 S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [slotResidue_eq_reciprocal_v2,
      LocalPrincipalSignalBoundsV2.contour_shift_left_pc2 χ H hH hb (-11/16) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(analyticBoundaryB0 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(analyticBoundaryB0 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(analyticBoundaryB0 : ℝ))) :=
        mul_le_mul (kernel_norm_bound_v2 χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(analyticBoundaryB0 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem exists_slotResidue_bound_v2 (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | analyticBoundaryB0 < s.re})
    (hb : ∀ s : ℂ, analyticBoundaryB0 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SlotBounds_v2 S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
          D * Z^(a-11/16) * P^(-(analyticBoundaryB0 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact slotResidue_bound_of_reciprocal_bound_v2 χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem raw_slot_integrable_v2 (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal_v2 χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf


theorem idealCoeff_norm_one_of_coprime_v2 (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, ite_eq_right hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

theorem prime_coprime_of_norm_gt_v2 (η : Character) (P : PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

theorem normalized_source_double_residue_v2 (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^lx) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z E (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := LocalPrincipalGeometryV2.source_power_identity hZ geometry s
  have hz : (Z : ℂ)^(((-E/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-E/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-E/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized_v2 (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z E (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^lx) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z E (slotMass T w) : ℂ)) =
        slotResidue χ (fun s => H s 1 (1/6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue_v2 W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem source_double_residue_integrable_v2 (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^lx) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hiraw := raw_slot_integrable_v2 χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := E))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z E (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (normalized_source_double_residue_v2 W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

theorem exists_normalized_actual_source_bound_v2 (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E)
    (hcut : ∀ P : PrimeIdeal, P.val.absNorm ≤ commonCutoff → P.val ∈ E) (η : Character) {a : ℝ}
    (ha : analyticBoundaryB0 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(analyticBoundaryB0 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z LocalPrincipalGeometryV2.E (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^lx) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^lx) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(analyticBoundaryB0 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  have hcorrection := same_source_correction E hE hcut η
  obtain ⟨D, hD, hb⟩ := exists_slotResidue_bound_v2 (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    hcorrection.1.differentiableOn hcorrection.2 ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sourceResidueIntegral_normalized_v2 W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : SlotBounds_v2 S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime_v2 η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact source_double_residue_integrable_v2 W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end
end OAI.SevenEighths.LocalPrincipalResidueV2
