/-
2026-11-03 general-number-field refinement by Zhongpai Gao with AI assistance.
Original proof: Dean Cureton, Jesse Thorner and AxiomProver (Axiom Math),
with upstream dependencies credited in Candidate.Provenance.
Native extension: 1823f8b90a601a29eda3cded57796e7200f2af9f.
Independent original baseline: 09afbb4ce6570c1615d58509dc197fc9f0956b7d.
Boundary: 1209/1250 = 0.9672 over every number field, at every height.
The extension uses the original 31/32 theorem, logarithmic control, the primitive
functional equation and interpolation to strengthen both masked numerator rows.
Old baseline declarations and new scale-dependent declarations are separate.
Native CI https://github.com/Gaozhongpai/DedekindZetaZeroFree/actions/runs/41707610922
is running. Full endpoint compilation and independent admission remain pending.
The five Bridge modules supply the genuine rational-Hecke / Dirichlet identity.
Their isolated checks do not certify the full endpoint. The submitted boundary and package identifier both use 0.9672.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Main
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.HeckeCorollary
public import Submissions.gao_general_number_fields_9672.Bridge.NativeHeckeToDirichlet

@[expose] public section

namespace Candidate

/-- The native strengthened Dedekind theorem over every number field.
This aliases the actual 1209/1250 theorem; it is not a tracker certificate. -/
theorem number_field_bound (K : Type) [Field K] [NumberField K] :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
      (∀ s : ℂ, 1 < s.re → f s = NumberField.dedekindZeta K s) ∧
      ∀ s : ℂ, 1209 / 1250 < s.re → s ≠ 1 → f s ≠ 0 := by
  exact Refinement9672.DedekindZetaZeroFree.dedekindZeta_ne_zero K

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
      ∀ s, 1209 / 1250 < s.re → (s ≠ 1 ∨ ¬ χ.IsPrincipal) → f s ≠ 0 := by
  exact Refinement9672.DedekindZetaZeroFree.heckeL_ne_zero K m hm χ

/-- Canonical all-Dirichlet specialization of the actual native Hecke theorem.
The bridge includes odd/imprimitive characters and nonprincipal values at1. -/
theorem bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1209 / 1250 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact TrackerBridge.dirichlet_bound_of_rat_hecke (1209 / 1250)
    (Refinement9672.DedekindZetaZeroFree.heckeL_ne_zero ℚ) χ hs hpole

end Candidate

#print axioms Candidate.number_field_bound
#print axioms Candidate.hecke_bound
#print axioms Candidate.bound
