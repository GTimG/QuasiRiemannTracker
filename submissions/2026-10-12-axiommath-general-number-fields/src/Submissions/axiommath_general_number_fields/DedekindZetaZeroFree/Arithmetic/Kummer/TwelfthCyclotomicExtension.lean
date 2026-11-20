/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Kummer/TwelfthCyclotomicExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

@[expose] public section

namespace DedekindZetaZeroFree

theorem cyclotomic12_context (K : Type) [Field K] [NumberField K] :
    IsGalois K (CyclotomicField 12 K) ∧
      (∀ σ τ : CyclotomicField 12 K ≃ₐ[K] CyclotomicField 12 K,
        σ * τ = τ * σ) ∧
      NumberField.IsTotallyComplex (CyclotomicField 12 K) ∧
      (∃ ζ : CyclotomicField 12 K, IsPrimitiveRoot ζ 12 ∧
        ∀ x : CyclotomicField 12 K, x ^ 12 = 1 →
          ∃ j : ℕ, j < 12 ∧ x = ζ ^ j) := by
  haveI : IsCyclotomicExtension {12} K (CyclotomicField 12 K) := inferInstance
  haveI : IsMulCommutative (CyclotomicField 12 K ≃ₐ[K] CyclotomicField 12 K) :=
    IsCyclotomicExtension.isMulCommutative {12} K (CyclotomicField 12 K)
  obtain ⟨ζ, hζ⟩ :=
    (inferInstance : IsCyclotomicExtension {12} K (CyclotomicField 12 K)).exists_isPrimitiveRoot
      (Set.mem_singleton 12) (by norm_num)
  refine ⟨IsCyclotomicExtension.isGalois (S := {12}) (K := K) (L := CyclotomicField 12 K),
    ?_, primitive12_totallyComplex (CyclotomicField 12 K) ζ hζ, ⟨ζ, hζ, ?_⟩⟩
  · intro σ τ
    exact mul_comm' σ τ
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact ⟨j, hj, hjx.symm⟩

end DedekindZetaZeroFree
