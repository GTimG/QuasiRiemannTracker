/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/PrimeNormSummability.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries

@[expose] public section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain

theorem summable_exterior_prime_norm_rpow
    (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (a : ℝ) (ha : 1 < a) :
    Summable (fun p : {p : HeightOneSpectrum (RingOfIntegers F) // p ∉ S} =>
      (Ideal.absNorm p.val.asIdeal : ℝ) ^ (-a)) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  let K : Type := Shrink.{0} F
  let e : F ≃+* K := (Shrink.ringEquiv.{0} F).symm
  letI : NumberField K := NumberField.of_ringEquiv F K e
  let eO : RingOfIntegers F ≃+* RingOfIntegers K := RingOfIntegers.mapRingEquiv e
  let f : {p : HeightOneSpectrum (RingOfIntegers F) // p ∉ S} →
      NonzeroIdeal K := fun p =>
    ⟨Ideal.map eO.toRingHom p.val.asIdeal,
      (Ideal.map_eq_bot_iff_of_injective eO.injective).not.mpr p.val.ne_bot⟩
  have hmap : Function.Injective (Ideal.map eO.toRingHom) := by
    intro I J h
    apply (Ideal.comap_injective_of_surjective eO.symm eO.symm.surjective)
    rw [← Ideal.map_comap_of_equiv eO, ← Ideal.map_comap_of_equiv eO]
    simpa only [← RingEquiv.toRingHom_eq_coe] using h
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    apply HeightOneSpectrum.asIdeal_injective
    exact hmap (congrArg Subtype.val h)
  have hn (p : {p : HeightOneSpectrum (RingOfIntegers F) // p ∉ S}) :
      Ideal.absNorm (f p).val = Ideal.absNorm p.val.asIdeal := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot]
    exact (Nat.card_congr (Ideal.quotientEquiv p.val.asIdeal (f p).val eO rfl).toEquiv).symm
  have h := (ideal_norm_rpow_summable K a ha).comp_injective hf
  convert h using 1
  funext p
  simp only [Function.comp_def, idealNorm, hn]
  rfl

end DedekindZetaZeroFree
