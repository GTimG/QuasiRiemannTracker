/-
2026-11-03 Dirichlet specialization bridge by Zhongpai Gao with AI assistance.
Apache-2.0. Original source attribution and licenses below are retained.
This module is adapted from the isolated checked NativeHeckeToDirichlet.lean proof:
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Tracker adaptation changes import paths only; all theorem bodies are unchanged.
The adapter applies to the genuine strengthened native Hecke theorem; full
native endpoint compatibility and official tracker admission remain pending.
-/
/-
Canonical Dirichlet consequence of the genuine rational specialization of the
native all-number-field Hecke theorem. Zhongpai Gao with AI assistance, 2026-11-03.
Apache-2.0. The endpoint is an explicit theorem argument so this adapter can be
checked without replaying the native proof closure. It introduces no axioms.
-/
import Submissions.gao_general_number_fields_9686.Bridge.CharacterConstruction
import Submissions.gao_general_number_fields_9686.Bridge.SeriesBridge
import Submissions.gao_general_number_fields_9686.Bridge.AnalyticBridge

open scoped NumberField

namespace TrackerBridge

/-- A proved native rational Hecke endpoint implies the canonical all-Dirichlet
statement at exactly the same boundary. All arithmetic and continuation
identifications are discharged by the preceding checked bridge modules. -/
theorem dirichlet_bound_of_rat_hecke (θ : ℝ)
    (hhecke : ∀ (m : Ideal RatIntegers) (hm : m ≠ ⊥)
      (η : DedekindZetaZeroFree.RayClassCharacter ℚ m),
      ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({1}ᶜ : Set ℂ) ∧
        (¬ η.IsPrincipal → Differentiable ℂ f) ∧
        (∀ s, 1 < s.re → HasSum (fun I : Ideal RatIntegers =>
          η I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s)) ∧
        ∀ s, θ < s.re → (s ≠ 1 ∨ ¬ η.IsPrincipal) → f s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : θ < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let η := dirichletRayCharacter χ
  obtain ⟨f, hf, hentire, hsum, hnz⟩ :=
    hhecke (Ideal.span {(q : RatIntegers)}) (rat_modulus_ne_bot q) η
  apply GaoDirichletBridge.LFunction_ne_zero_of_native_continuation
    χ θ η.IsPrincipal f ?_ hf hentire ?_ hnz hs hpole
  · intro hχ hη
    exact hχ ((dirichletRayCharacter_principal_iff χ).mp hη)
  · exact rat_hecke_continuation_eq_LFunction χ η
      (dirichletRayCharacter_span χ) f hsum

end TrackerBridge

#print axioms TrackerBridge.dirichlet_bound_of_rat_hecke
