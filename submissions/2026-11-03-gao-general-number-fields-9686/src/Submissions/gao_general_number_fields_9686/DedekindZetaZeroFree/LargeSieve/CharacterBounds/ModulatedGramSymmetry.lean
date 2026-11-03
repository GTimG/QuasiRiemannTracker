/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/CharacterBounds/ModulatedGramSymmetry.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.CharacterBounds.BandlimitedPoissonGramMajorant

@[expose] public section

namespace DedekindZetaZeroFree.ProbeAdditiveGramBounds
noncomputable section
open scoped Classical NumberField ComplexConjugate
open IsDedekindDomain NumberField

theorem trace_phase_continuous
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : (v : S) → AddChar (v.val.adicCompletion F) Circle)
    (he : ∀ v, Continuous (e v))
    (χ : SLocalProduct F S → ℂ)
    (hχ : ∀ x, χ x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ)) : Continuous χ := by
  have hfun : χ = fun x =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((∑ v : InfinitePlace F, 2 *
          (InfinitePlace.Completion.extensionEmbedding v (x.1 v)).re) : ℂ)) *
        ∏ v : S, (e v (x.2 v) : ℂ) := funext hχ
  rw [hfun]
  have harch (v : InfinitePlace F) :
      Continuous (fun x : SLocalProduct F S =>
        InfinitePlace.Completion.extensionEmbedding v (x.1 v)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  fun_prop

end
end DedekindZetaZeroFree.ProbeAdditiveGramBounds
