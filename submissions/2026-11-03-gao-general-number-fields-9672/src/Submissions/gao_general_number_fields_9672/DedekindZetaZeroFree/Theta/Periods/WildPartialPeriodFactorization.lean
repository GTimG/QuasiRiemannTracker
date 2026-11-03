/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/WildPartialPeriodFactorization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.NormalizedFiniteTensorProducts

@[expose] public section

noncomputable section

open scoped NumberField

open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPWildPartialPeriodFactorization

open KPLocalExceptionalConstruction

variable (F : Type) [Field F] [NumberField F]

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def wildPlaces : Set (HeightOneSpectrum (𝓞 F)) :=
  {q | (3 : 𝓞 F) ∈ q.asIdeal}

theorem wildPlaces_finite : (wildPlaces F).Finite := by
  have h3 : (3 : 𝓞 F) ≠ 0 := by norm_num
  simpa only [wildPlaces, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] using
    (Ideal.finite_factors (I := Ideal.span {(3 : 𝓞 F)})
      (by
        intro h
        apply h3
        exact Ideal.span_singleton_eq_bot.mp h))

abbrev WildPlace := ↥(wildPlaces F)

instance wildPlaceFintype : Fintype (WildPlace F) :=
  (wildPlaces_finite F).fintype

end DedekindZetaZeroFree.KPWildPartialPeriodFactorization

end
