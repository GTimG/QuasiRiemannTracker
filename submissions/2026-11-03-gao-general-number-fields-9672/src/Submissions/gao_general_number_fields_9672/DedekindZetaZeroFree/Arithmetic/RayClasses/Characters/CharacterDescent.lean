/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/RayClasses/Characters/CharacterDescent.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FractionalIdealCharacterExtension
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.FractionalIdealCharacterKernel
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.PrincipalCriterion
public import Submissions.gao_general_number_fields_9672.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassGroupFinite

@[expose] public section

open scoped NumberField

namespace DedekindZetaZeroFree.AbelianQuotient

instance rayIdealClass_finite
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) : Finite (RayIdealClass K m hm) :=
  ClassFieldTheory.rayClassGroup_finite K (narrowIdealModulus K m hm)

theorem rayCharacterDescent
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    ∃ ψ : RayIdealClass K m hm →* ℂ,
      (∀ I : Ideal (𝓞 K), χ I =
        match rayIdealClass K m hm I with
        | none => 0
        | some c => ψ c) ∧
      (χ.IsPrincipal ↔ ψ = 1) := by
  classical
  obtain ⟨f, hf⟩ :
      ∃ f : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus K m hm) →* ℂˣ,
        (∀ I : Ideal (𝓞 K), I ≠ ⊥ → I ⊔ m = ⊤ →
          ∀ J : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus K m hm),
            ((J : ClassFieldTheory.NumberFieldFractionalIdealGroup K) :
              FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
              (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) →
            (f J : ℂ) = χ I) :=
    rayFractionalCharacterExtension K m hm χ
  have hker : ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
      (narrowIdealModulus K m hm) ≤ f.ker :=
    rayFractionalCharacterKernel K m hm χ f hf
  let N := ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo (narrowIdealModulus K m hm)
  let lift : RayIdealClass K m hm →* ℂˣ := QuotientGroup.lift N f hker
  let ψ : RayIdealClass K m hm →* ℂ := (Units.coeHom ℂ).comp lift
  have hψ : ∀ I : Ideal (𝓞 K), χ I =
      match rayIdealClass K m hm I with
      | none => 0
      | some c => ψ c := by
    intro I
    by_cases h : I = ⊥ ∨ I ⊔ m ≠ ⊤
    · rw [rayIdealClass_eq_none K m hm I h]
      exact (χ.eq_zero_iff' I).mpr h
    · obtain ⟨hI, hcn⟩ := not_or.mp h
      have hI : I ≠ ⊥ := hI
      have hcoprime : I ⊔ m = ⊤ := not_not.mp hcn
      rw [rayIdealClass_eq_some K m hm I hI hcoprime]
      have hJ : ((rayIdealClassRepresentative K m hm I hI hcoprime :
          ClassFieldTheory.NumberFieldFractionalIdealGroup K) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
        show ((rayIdealFractionalIdeal K I hI :
          ClassFieldTheory.NumberFieldFractionalIdealGroup K) :
            FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
          (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
        rw [rayIdealFractionalIdeal_coe]
      have hfI := hf I hI hcoprime (rayIdealClassRepresentative K m hm I hI hcoprime) hJ
      have hlift : lift (QuotientGroup.mk' N
          (rayIdealClassRepresentative K m hm I hI hcoprime)) =
          f (rayIdealClassRepresentative K m hm I hI hcoprime) := by
        dsimp only [lift]
        rw [← MonoidHom.comp_apply, QuotientGroup.lift_comp_mk']
      simp only [ψ, MonoidHom.comp_apply, Units.coeHom_apply]
      rw [hlift]
      exact hfI.symm
  exact ⟨ψ, hψ, rayCharacterPrincipalCriterion K m hm χ ψ hψ⟩

end DedekindZetaZeroFree.AbelianQuotient
