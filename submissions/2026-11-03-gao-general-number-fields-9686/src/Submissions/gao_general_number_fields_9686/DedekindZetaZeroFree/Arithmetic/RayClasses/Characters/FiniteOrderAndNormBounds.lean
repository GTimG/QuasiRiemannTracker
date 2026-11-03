/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/FiniteOrderAndNormBounds.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

theorem rayCharacterFiniteOrder
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    ∃ n : ℕ, 0 < n ∧
      ∀ I : Ideal (𝓞 K), I ≠ ⊥ → I ⊔ m = ⊤ → χ I ^ n = 1 := by
  obtain ⟨ψ, hχ, -⟩ := rayCharacterDescent K m hm χ
  refine ⟨Nat.card (RayIdealClass K m hm), Nat.card_pos, ?_⟩
  intro I hI hcop
  have hne : rayIdealClass K m hm I ≠ none := by
    intro h
    rw [rayIdealClass_eq_none_iff] at h
    exact h.elim hI (fun h2 => h2 hcop)
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hχ I, hc]
  rw [← map_pow, pow_card_eq_one', map_one]

theorem rayCharacter_norm_le_one
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    ∀ I : Ideal (𝓞 K), ‖χ I‖ ≤ 1 := by
  obtain ⟨ψ, hχ, -⟩ := rayCharacterDescent K m hm χ
  intro I
  have hn : Nat.card (RayIdealClass K m hm) ≠ 0 := Nat.card_pos.ne'
  rw [hχ I]
  cases h : rayIdealClass K m hm I with
  | none => simp
  | some c =>
    have hpow : ψ c ^ Nat.card (RayIdealClass K m hm) = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [Complex.norm_eq_one_of_pow_eq_one hpow hn]

end DedekindZetaZeroFree.AbelianQuotient
