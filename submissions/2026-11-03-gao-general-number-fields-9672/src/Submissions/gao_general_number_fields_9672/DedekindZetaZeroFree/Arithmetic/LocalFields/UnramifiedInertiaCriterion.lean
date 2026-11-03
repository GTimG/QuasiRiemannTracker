/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/LocalFields/UnramifiedInertiaCriterion.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

theorem unramifiedIffInertiaBot
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (p : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hw : w.asIdeal.LiesOver p.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ↔
      Ideal.inertia (E ≃ₐ[K] E) w.asIdeal = ⊥ := by

  haveI : Ring.HasFiniteQuotients (𝓞 K) := Ring.HasFiniteQuotients.of_module_finite ℤ (𝓞 K)
  haveI : IsGaloisGroup Gal(E/K) (𝓞 K) (𝓞 E) := inferInstance
  haveI : w.asIdeal.LiesOver p.asIdeal := hw

  have hcard : Nat.card (Ideal.inertia (E ≃ₐ[K] E) w.asIdeal) =
      w.asIdeal.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/K)) p.asIdeal w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal w.asIdeal Gal(E/K)]

  rw [Subgroup.eq_bot_iff_card, hcard]

  exact Ideal.ramificationIdx_eq_one_iff.symm

theorem unramifiedAtAllPrimesAboveIff
    {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsAbelianGalois K E]
    (p : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hw : w.asIdeal.LiesOver p.asIdeal) :
    (∀ w' : HeightOneSpectrum (𝓞 E), w'.asIdeal.LiesOver p.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) w'.asIdeal) ↔
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  haveI : Ring.HasFiniteQuotients (𝓞 K) := Ring.HasFiniteQuotients.of_module_finite ℤ (𝓞 K)
  haveI : IsGaloisGroup Gal(E/K) (𝓞 K) (𝓞 E) := inferInstance
  haveI : w.asIdeal.LiesOver p.asIdeal := hw
  constructor
  · intro h; exact h w hw
  · intro h w' hw'
    haveI : w'.asIdeal.LiesOver p.asIdeal := hw'

    have key : w'.asIdeal.ramificationIdx (𝓞 K) = w.asIdeal.ramificationIdx (𝓞 K) := by
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal w'.asIdeal Gal(E/K),
        ← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal w.asIdeal Gal(E/K)]
    rw [← Ideal.ramificationIdx_eq_one_iff, key, Ideal.ramificationIdx_eq_one_iff]
    exact h

end DedekindZetaZeroFree.AbelianQuotient
