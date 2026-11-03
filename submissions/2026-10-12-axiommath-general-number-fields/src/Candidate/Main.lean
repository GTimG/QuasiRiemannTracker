module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Main
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HeckeCorollary

@[expose] public section

namespace Candidate

/-- AxiomMath’s general number-field theorem. This is deliberately the actual
native target, rather than the tracker’s different all-Dirichlet target. -/
theorem bound (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.dedekindZeta_ne_zero K

/-- AxiomMath’s finite-order Hecke corollary over every number field. -/
theorem hecke_bound
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (NumberField.RingOfIntegers K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (NumberField.RingOfIntegers K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 31 / 32 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  exact DedekindZetaZeroFree.heckeL_ne_zero K m hm χ

end Candidate
