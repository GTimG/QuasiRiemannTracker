/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/CharacterUnitarity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.PrincipalPowerGenerator

@[expose] public section

namespace DedekindZetaZeroFree.RayUnitary

open scoped NumberField

private theorem ray_character_map_pow
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (N : ℕ) :
    η (I ^ N) = (η I) ^ N := by
  induction N with
  | zero => simp [RayClassCharacter.map_top']
  | succ n ih =>
    rw [pow_succ, RayClassCharacter.map_mul', ih, pow_succ]

theorem ray_character_pow_eq_one
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    ∃ n : ℕ, 0 < n ∧ (η I) ^ n = 1 := by
  obtain ⟨hNpos, α, hα, hα1, hpos, hspan⟩ :=
    integral_ideal_pow_card_rayClassGroup_generator F 𝔪 h𝔪 I hI hcop
  refine ⟨Nat.card (ClassFieldTheory.RayClassGroup (RayClassBridge.narrowIdealModulus F 𝔪 h𝔪)),
    hNpos, ?_⟩
  rw [← ray_character_map_pow F 𝔪 η I]
  rw [hspan]
  exact η.map_span' α hα hα1 hpos

theorem ray_character_norm_eq_one
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    ‖η I‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := ray_character_pow_eq_one F 𝔪 h𝔪 η I hI hcop
  exact Complex.norm_eq_one_of_pow_eq_one hpow hn.ne'

theorem ray_character_eq_zero
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hbad : I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤) :
    η I = 0 :=
  (η.eq_zero_iff' I).mpr hbad

theorem ray_character_norm_le_one
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) :
    ‖η I‖ ≤ 1 := by
  by_cases hbad : I = ⊥ ∨ I ⊔ 𝔪 ≠ ⊤
  · rw [ray_character_eq_zero F 𝔪 h𝔪 η I hbad]
    simp
  · push Not at hbad
    obtain ⟨hI, hcop⟩ := hbad
    rw [ray_character_norm_eq_one F 𝔪 h𝔪 η I hI hcop]

end DedekindZetaZeroFree.RayUnitary
