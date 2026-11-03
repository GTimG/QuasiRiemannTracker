/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/FiniteGroupCharacters/UnitNorm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupFinite

@[expose] public section

namespace DedekindZetaZeroFree.RayClassBridge.FiniteOrder

theorem norm_eq_one {G : Type*} [Group G] [Finite G]
    (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G)
  · have h : χ g ^ Nat.card G = 1 := by
      rw [← map_pow, pow_card_eq_one', map_one]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) h
  · exact Nat.ne_of_gt Nat.card_pos

end DedekindZetaZeroFree.RayClassBridge.FiniteOrder
