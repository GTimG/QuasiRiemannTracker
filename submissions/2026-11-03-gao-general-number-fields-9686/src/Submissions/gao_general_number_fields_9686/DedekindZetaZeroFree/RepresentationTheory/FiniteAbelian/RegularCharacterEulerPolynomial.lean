/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/FiniteAbelian/RegularCharacterEulerPolynomial.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.FiniteAbelian.CharacterEvaluationFibers
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Algebra.RootsOfUnityEulerPolynomial

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped BigOperators

theorem regularCharacterDeterminant
    {G : Type*} [CommGroup G] [Finite G] (g : G) (x : ℂ) :
    ∏ ρ : ComplexDual G, (1 - (ρ g : ℂ) * x) =
      (1 - x ^ orderOf g) ^ (Nat.card G / orderOf g) := by
  classical
  have hf := dualEvaluation_orderOf_pos g
  letI : NeZero (orderOf g) := ⟨Nat.ne_of_gt hf⟩
  letI : Fintype (rootsOfUnity (orderOf g) ℂ) := Fintype.ofFinite _
  let e : ComplexDual G → rootsOfUnity (orderOf g) ℂ := fun ρ =>
    ⟨ρ g, (mem_rootsOfUnity _ _).mpr (dualEvaluation_pow_orderOf g ρ)⟩
  have hcard (ζ : rootsOfUnity (orderOf g) ℂ) :
      Fintype.card {ρ : ComplexDual G // e ρ = ζ} = Nat.card G / orderOf g := by
    rw [← Nat.card_eq_fintype_card]
    have he : {ρ : ComplexDual G // e ρ = ζ} ≃ {ρ : ComplexDual G // ρ g = ζ.val} :=
      Equiv.subtypeEquivRight (fun ρ => by simp [e, Subtype.ext_iff])
    rw [Nat.card_congr he]
    exact dualEvaluationFibers g ζ.val ((mem_rootsOfUnity _ _).mp ζ.property)
  calc
    ∏ ρ : ComplexDual G, (1 - (ρ g : ℂ) * x) =
        ∏ ζ : rootsOfUnity (orderOf g) ℂ, ∏ _ρ : {ρ : ComplexDual G // e ρ = ζ},
          (1 - (ζ.val : ℂ) * x) :=
      (Fintype.prod_fiberwise' e (fun ζ => 1 - (ζ.val : ℂ) * x)).symm
    _ = ∏ ζ : rootsOfUnity (orderOf g) ℂ,
          (1 - (ζ.val : ℂ) * x) ^ (Nat.card G / orderOf g) := by
      apply Finset.prod_congr rfl
      intro ζ _
      simp only [Finset.prod_const, Finset.card_univ, hcard]
    _ = (∏ ζ : rootsOfUnity (orderOf g) ℂ, (1 - (ζ.val : ℂ) * x)) ^
          (Nat.card G / orderOf g) := Finset.prod_pow _ _ _
    _ = (1 - x ^ orderOf g) ^ (Nat.card G / orderOf g) := by
      rw [rootsEulerPolynomial (orderOf g) hf x]

end DedekindZetaZeroFree.AbelianQuotient
