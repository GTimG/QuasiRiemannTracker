/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Fourier/LocalCosetIndicators.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBallMasses
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalSchwartzIntegral
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactSubgroupCharacterIntegral

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

 local instance cosetFourierCompletionMeasurable
    (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

 local instance cosetFourierCompletionBorel
    (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem localCosetIndicator_mem_localSchwartz
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hUcompact : IsCompact (U : Set (v.adicCompletion F)))
    (hUopen : IsOpen (U : Set (v.adicCompletion F)))
    (b : v.adicCompletion F) :
    localCosetIndicator F v b U ∈ localSchwartz F v := by
  let S : Set (v.adicCompletion F) := {x | x - b ∈ U}
  have heq : S = (fun x : v.adicCompletion F => b + x) '' (U : Set _) := by
    ext x
    constructor
    · intro h; exact ⟨x - b, h, by simp⟩
    · rintro ⟨z, hz, rfl⟩; simpa [S] using hz
  have hc : IsCompact S := by
    rw [heq]
    exact hUcompact.image (by fun_prop)
  have ho : IsOpen S := hUopen.preimage (by fun_prop)
  have hcl : IsClopen S := ⟨hc.isClosed, ho⟩
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant
  · apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hcl.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp [localCosetIndicator, S] at hn ⊢; exact hn)

theorem localFourierIntegral_localCosetIndicator
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hUcompact : IsCompact (U : Set (v.adicCompletion F)))
    (hUopen : IsOpen (U : Set (v.adicCompletion F)))
    (b y : v.adicCompletion F) :
    localFourierIntegral F v (localCosetIndicator F v b U) y =
      (((localNormalizedHaar F v (U : Set (v.adicCompletion F))).toReal : ℝ) : ℂ) *
        (localFiniteCharacter F v (-b * y) : ℂ) *
        localCosetIndicator F v 0 (localFiniteAnnihilator F v U) y := by
  let χ : AddChar (v.adicCompletion F) Circle :=
    { toFun := fun u => localFiniteCharacter F v (-u * y)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro u w
        simp only [neg_add, add_mul, AddChar.map_add_eq_mul] }
  have hχ : Continuous χ :=
    (continuous_localFiniteCharacter F v).comp ((continuous_id.neg).mul continuous_const)
  have horth := (compactSubgroup_character_integral
    (localNormalizedHaar F v) U hUcompact χ hχ).2
  have htrivial : (∀ u ∈ U, χ u = 1) ↔ y ∈ localFiniteAnnihilator F v U := by
    constructor
    · intro h u hu
      have ht := h (-u) (U.neg_mem hu)
      simpa [χ] using ht
    · intro h u hu
      have ht := h (-u) (U.neg_mem hu)
      simpa [χ] using ht
  have htranslate :
      (fun x : v.adicCompletion F =>
        localCosetIndicator F v b U (b + x) *
          (localFiniteCharacter F v (-(b + x) * y) : ℂ)) =
      (fun x => (localFiniteCharacter F v (-b * y) : ℂ) *
        (U : Set (v.adicCompletion F)).indicator (fun u => (χ u : ℂ)) x) := by
    funext x
    by_cases hx : x ∈ U
    · simp [localCosetIndicator_apply, hx, Set.indicator_of_mem, χ,
        neg_add, add_mul, AddChar.map_add_eq_mul]
      exact mul_comm _ _
    · simp [localCosetIndicator_apply, hx, Set.indicator_of_notMem]
  rw [localFourierIntegral_apply]
  rw [← integral_add_left_eq_self (μ := localNormalizedHaar F v)
    (fun x => localCosetIndicator F v b U x *
      (localFiniteCharacter F v (-x * y) : ℂ)) b]
  rw [htranslate, integral_const_mul, integral_indicator hUcompact.measurableSet, horth]
  by_cases hy : y ∈ localFiniteAnnihilator F v U
  · rw [if_pos (htrivial.mpr hy)]
    simp [localCosetIndicator_apply, hy, mul_comm]
  · rw [if_neg (mt htrivial.mp hy)]
    simp [localCosetIndicator_apply, hy]

theorem localFourierIntegral_localCosetIndicator_ball
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) (b y : v.adicCompletion F) :
    localFourierIntegral F v
        (localCosetIndicator F v b (finiteCompletionBall F v n)) y =
      (localBallMass F v n : ℂ) * (localFiniteCharacter F v (-b * y) : ℂ) *
        localCosetIndicator F v 0
          (finiteCompletionBall F v (-n - (localDifferentExponent F v : ℤ))) y := by
  rw [localFourierIntegral_localCosetIndicator F v (finiteCompletionBall F v n)
    (isCompact_finiteCompletionBall F v n) (isOpen_finiteCompletionBall F v n),
    localNormalizedHaar_finiteCompletionBall_toReal,
    localFiniteAnnihilator_finiteCompletionBall]

end DedekindZetaZeroFree

end
