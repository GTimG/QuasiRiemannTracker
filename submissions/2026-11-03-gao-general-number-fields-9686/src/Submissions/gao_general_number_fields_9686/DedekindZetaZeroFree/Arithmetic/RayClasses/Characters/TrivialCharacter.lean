/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/TrivialCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField
open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K]

noncomputable def trivialRayCharacter : RayClassCharacter K ⊤ := by
  classical
  refine { toFun := fun I => if I = ⊥ then 0 else 1
           map_mul' := ?_, map_top' := ?_, eq_zero_iff' := ?_, map_span' := ?_ }
  · intro I J
    simp only [Ideal.mul_eq_bot]
    split_ifs <;> simp_all
  · simp
  · intro I
    simp
  · intro α hα _ _
    simp [Ideal.span_singleton_eq_bot, hα]

theorem trivialRayCharacter_apply (I : Ideal (𝓞 K)) :
    trivialRayCharacter K I = if I = ⊥ then 0 else 1 := by
  classical
  rfl

theorem trivialRayCharacter_eq_primeArtinValue
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (p : HeightOneSpectrum (𝓞 K)) (W : HeightOneSpectrum (𝓞 L))
    (_hW : W.asIdeal.LiesOver p.asIdeal) :
    trivialRayCharacter K p.asIdeal =
      primeArtinValue (1 : ComplexDual (L ≃ₐ[K] L)) W := by
  classical
  simp [trivialRayCharacter, primeArtinValue, p.ne_bot]

end DedekindZetaZeroFree.AbelianQuotient
