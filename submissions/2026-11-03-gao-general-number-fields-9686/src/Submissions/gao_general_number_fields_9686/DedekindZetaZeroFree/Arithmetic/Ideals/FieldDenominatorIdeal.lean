/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/FieldDenominatorIdeal.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

def fieldDenomIdeal (K : Type) [Field K] [NumberField K] (y : K) : Ideal (𝓞 K) where
  carrier := {d | ∃ a : 𝓞 K, (a : K) = (d : K) * y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro d₁ d₂ ⟨a₁, h₁⟩ ⟨a₂, h₂⟩
    refine ⟨a₁ + a₂, ?_⟩
    push_cast
    simp only [h₁, h₂]
    ring
  smul_mem' := by
    rintro c d ⟨a, h⟩
    refine ⟨c * a, ?_⟩
    simp only [smul_eq_mul, map_mul]
    simp only [h]
    ring

theorem fieldDenominatorIdeal
    (K : Type) [Field K] [NumberField K] (y : K) :
    ∃ D : Ideal (𝓞 K), D ≠ ⊥ ∧
      ∀ d : 𝓞 K, d ∈ D ↔ ∃ a : 𝓞 K, (a : K) = (d : K) * y := by
  refine ⟨fieldDenomIdeal K y, ?_, fun d => Iff.rfl⟩
  rw [Submodule.ne_bot_iff]
  by_cases hy : y = 0
  · refine ⟨1, ⟨0, ?_⟩, one_ne_zero⟩
    simp [hy]
  · obtain ⟨⟨n, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) y
    exact ⟨d, ⟨n, by linear_combination -hd⟩, mem_nonZeroDivisors_iff_ne_zero.mp d.2⟩

end DedekindZetaZeroFree.AbelianQuotient
