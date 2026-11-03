/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/CharacterFiniteOrder.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescentUniqueness

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RayOperations

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

theorem exists_pow_eq_one {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (hm : m ≠ ⊥) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) :
    ∃ k : ℕ, 0 < k ∧ (η I) ^ k = 1 := by
  haveI : Finite (ClassFieldTheory.RayClassGroup (RayBridge.fullModulus m hm)) :=
    ClassFieldTheory.rayClassGroup_finite F (RayBridge.fullModulus m hm)
  obtain ⟨k, hkpos, hk⟩ :=
    (isOfFinOrder_of_finite (RayBridge.idealClass m hm I hI hcop)).exists_pow_eq_one
  refine ⟨k, hkpos, ?_⟩
  have h1 : (RayBridge.descendedCharacter m hm η
      (RayBridge.idealClass m hm I hI hcop)) ^ k = 1 := by
    rw [← map_pow, hk, map_one]
  have h2 : ((RayBridge.descendedCharacter m hm η
      (RayBridge.idealClass m hm I hI hcop) : ℂ)) ^ k = 1 := by
    have hc := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using hc
  rw [← RayBridge.descendedCharacter_apply_idealClass m hm η I hI hcop]
  exact h2

theorem norm_eq_one {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (hcop : I ⊔ m = ⊤) : ‖η I‖ = 1 := by
  by_cases hm : m = ⊥
  · subst hm
    have hItop : I = ⊤ := by simpa using hcop
    rw [hItop, map_top, norm_one]
  · obtain ⟨k, hkpos, hk⟩ := exists_pow_eq_one η hm hI hcop
    exact Complex.norm_eq_one_of_pow_eq_one hk hkpos.ne'

theorem norm_le_one {m : Ideal (𝓞 F)} (η : RayClassCharacter F m)
    (I : Ideal (𝓞 F)) : ‖η I‖ ≤ 1 := by
  rcases eq_or_ne (η I) 0 with h | h
  · rw [h, norm_zero]; norm_num
  · obtain ⟨hI, hcop⟩ := (ne_zero_iff η I).mp h
    rw [norm_eq_one η hI hcop]

end DedekindZetaZeroFree.LargeSieve.RayOperations
