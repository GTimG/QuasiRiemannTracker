/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighHighSlices.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.crossnox_perturbed_boundary.OAIHighUniformTails

open OAI.SevenEighths.AsymmetricGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours

open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem source_uniform_high_slices_on_perturbed_region
    {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a Bs Bz cw : ℝ)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hcw : 1 < cw) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Character) (S : Finset Id)
      (hS : SourceExclusions S), PerturbedCorrectionTail S →
      ∀ (J : Finset ι) (T : ι → Finset PrimeIdeal)
      (b : ι → PrimeIdeal → ℂ),
      (∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) →
      ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Icc a Bs, ∀ ξ ∈ Icc (33 / 200 : ℝ) Bz,
      ∀ υ ∈ Icc (19 / 20 : ℝ) cw,
      ∀ axis : SliceAxis,
      (axis ≠ .w → υ ≠ 1) → (axis ≠ .z → 6 * ξ ≠ 1) →
      ∀ R : ℝ, 1 ≤ |R| →
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
          ((σ : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I)
          ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime)
          ((υ : ℂ) + p.2 * I)
      Integrable (fun q : ℝ × ℝ => F (sliceMap axis R q))
        (volume.prod volume) ∧
      (∫ q : ℝ × ℝ, ‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
        arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
          (joinWGap axis υ) (joinZGap axis ξ) * K / height R ^ N := by
  obtain ⟨K, hK, hk⟩ := profile_arithmetic_slices
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33 / 200) Bz (19 / 20) cw (by norm_num) 8 N
  refine ⟨K, hK, ?_⟩
  intro η S hS hTail J T b hT X Y Z hX hY hZ
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  refine ⟨C, hC, ?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := arithmetic_onLines_measurable_all η S hS.prime J T b
    X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ × ℝ) :=
    bound_arithmetic_on_lines_with_gaps_on_perturbed_region
      η S hS hTail J T b hT X Y Z a Bs Bz cw σ ξ υ C
      hX hY hZ ha hσ hξ hcw hυ
      (joinWGap axis υ) (joinZGap axis ξ)
      (joinWGap_pos axis υ hυ1) (joinZGap_pos axis ξ hξ1)
      hC hR (sliceMap axis R q)
      (slice_w_gap axis R υ hR0 q)
      (slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
      (joinWGap axis υ) (joinZGap axis ξ))
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C
      _ _ hcw hC
      (joinWGap_pos axis υ hυ1).le
      (joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ × ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ : ℂ) + (sliceMap axis R q).1.1 * I)
      ((υ : ℂ) + (sliceMap axis R q).2 * I)
      ((ξ : ℂ) + (sliceMap axis R q).1.2 * I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines, arithmetic_profile_eq_source] using hh

theorem raw_source_uniform_high_slices_on_perturbed_region
    {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a Bs Bz cw : ℝ)
    (ha : (boundary : ℝ) ≤ a)
    (hβ : HeckeZeroSupremum.beta < a)
    (hcw : 1 < cw) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Character) (S : Finset Id)
      (hS : SourceExclusions S), PerturbedCorrectionTail S →
      ∀ (J : Finset ι) (T : ι → Finset PrimeIdeal)
      (b : ι → PrimeIdeal → ℂ),
      (∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) →
      ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ σ ∈ Icc a Bs, ∀ ξ ∈ Icc (33 / 200 : ℝ) Bz,
      ∀ υ ∈ Icc (19 / 20 : ℝ) cw,
      ∀ axis : SliceAxis,
      (axis ≠ .w → υ ≠ 1) → (axis ≠ .z → 6 * ξ ≠ 1) →
      ∀ R : ℝ, 1 ≤ |R| →
      let F := fun p : HeightSpace =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
          ((σ : ℂ) + p.1.1 * I)
          (globalClosedCorrection η S ((σ : ℂ) + p.1.1 * I))
          (slotMultiplier η J T b ((σ : ℂ) + p.1.1 * I))
          ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime)
          (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime)
          ((υ : ℂ) + p.2 * I)
      Integrable (fun q : ℝ × ℝ => F (sliceMap axis R q))
        (volume.prod volume) ∧
      (∫ q : ℝ × ℝ, ‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
        arithmeticAmplitude S J T b X Y Z a Bs Bz cw C
          (joinWGap axis υ) (joinZGap axis ξ) * K / height R ^ N := by
  obtain ⟨K, hK, hk⟩ := source_uniform_high_slices_on_perturbed_region
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a Bs Bz cw ha hβ hcw N
  refine ⟨K, hK, ?_⟩
  intro η S hS hTail J T b hT X Y Z hX hY hZ
  obtain ⟨C, hC, hc⟩ := hk η S hS hTail J T b hT X Y Z hX hY hZ
  refine ⟨C, hC, ?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := continued_high_slice_ae_raw
    η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
      (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,
    (integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end SevenEighths.ProbePrincipalContours

end

end OAI
