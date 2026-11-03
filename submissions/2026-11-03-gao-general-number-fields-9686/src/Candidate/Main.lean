/-
2026-11-03 draft parameter refinement by Zhongpai Gao with AI assistance.
Original proof: Dean Cureton, Jesse Thorner and AxiomProver (Axiom Math),
with the upstream dependencies credited in Candidate.Provenance.
Native source: 829193272c1eaf223bb7228fbfb9003f414808e9.
Boundary: 4843/5000 = 0.9686 over every number field, at every height.
Native CI https://github.com/Gaozhongpai/DedekindZetaZeroFree/actions/runs/41678339238
was in progress at draft preparation; compilation and tracker admission are unverified.
The formal rational-Hecke / Dirichlet identification is supplied by the five
Bridge modules, checked in isolation on tracker pins. Whole-closure compilation,
toolchain/import-all compatibility and independent admission remain pending.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Main
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HeckeCorollary
public import Submissions.gao_general_number_fields_9686.Bridge.NativeHeckeToDirichlet

@[expose] public section

namespace Candidate

/-- The native strengthened Dedekind theorem over every number field.
This aliases the actual 4843/5000 theorem; it is not a tracker certificate. -/
theorem number_field_bound (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 4843 / 5000 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact DedekindZetaZeroFree.dedekindZeta_ne_zero K

/-- The native strengthened finite-order Hecke corollary over every number field;
nonprincipal characters include s = 1. -/
theorem hecke_bound
    (K : Type) [Field K] [NumberField K]
    (m : Ideal (NumberField.RingOfIntegers K)) (hm : m ≠ ⊥)
    (χ : DedekindZetaZeroFree.RayClassCharacter K m) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (¬ χ.IsPrincipal → Differentiable ℂ f) ∧
      (∀ s, 1 < s.re → HasSum (fun I : Ideal (NumberField.RingOfIntegers K) =>
        χ I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
      ∀ s, 4843 / 5000 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  exact DedekindZetaZeroFree.heckeL_ne_zero K m hm χ

/-- Canonical all-Dirichlet specialization of the actual native Hecke theorem.
The bridge includes odd/imprimitive characters and nonprincipal values at1. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (4843 / 5000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact TrackerBridge.dirichlet_bound_of_rat_hecke (4843 / 5000)
    (DedekindZetaZeroFree.heckeL_ne_zero ℚ) χ hs hpole

end Candidate

#print axioms Candidate.number_field_bound
#print axioms Candidate.hecke_bound
#print axioms Candidate.bound
