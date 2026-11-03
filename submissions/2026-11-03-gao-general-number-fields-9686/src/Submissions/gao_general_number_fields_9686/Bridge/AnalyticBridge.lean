/-
2026-11-03 Dirichlet specialization bridge by Zhongpai Gao with AI assistance.
Apache-2.0. Original source attribution and licenses below are retained.
This module is adapted from the isolated checked AnalyticBridge.lean proof:
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Tracker adaptation changes import paths only; all theorem bodies are unchanged.
The adapter applies to the genuine strengthened native Hecke theorem; full
native endpoint compatibility and official tracker admission remain pending.
-/
/-
Copyright (c) 2026 Zhongpai Gao. All rights reserved.
Released under Apache 2.0 license.

The punctured-plane uniqueness argument below adapts Mathlib's
`DirichletCharacter.LFunction_changeLevel_aux` at revision
d13f23b723b8a846827a245b89c10fc7d3f11612 (Mathlib/NumberTheory/LSeries/
DirichletContinuation.lean), Copyright (c) 2024 David Loeffler;
authors David Loeffler and Michael Stoll, Apache 2.0.

This isolated analytic bridge does not assert the arithmetic character or
Dirichlet-series identification. Those enter as explicit hypotheses.
-/
import Mathlib

open Complex Filter
open scoped Topology

namespace GaoDirichletBridge

/-- A holomorphic continuation agreeing with the Dirichlet L-function on its
initial convergence half-plane agrees everywhere off its possible pole. -/
theorem eqOn_LFunction_of_halfPlane
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = DirichletCharacter.LFunction χ s) :
    Set.EqOn f (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  have htwo : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (hf.analyticOnNhd isOpen_compl_singleton) ?_ hpc htwo ?_
  · refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) isOpen_compl_singleton
    exact (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt
  · refine eventually_of_mem ?_ (fun s (hs : 1 < s.re) ↦ hmatch s hs)
    exact (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      (by simp : 1 < (2 : ℂ).re)

/-- In the nonprincipal case the entire continuations also agree at `s = 1`. -/
theorem eq_LFunction_of_halfPlane_of_ne_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = DirichletCharacter.LFunction χ s) :
    f = DirichletCharacter.LFunction χ := by
  exact hf.continuous.ext_on (dense_compl_singleton 1)
    (DirichletCharacter.differentiable_LFunction hχ).continuous
    (eqOn_LFunction_of_halfPlane χ f hf.differentiableOn hmatch)

/-- Transfer the exact native Hecke continuation contract to the canonical
Dirichlet statement. `P` may be instantiated with `η.IsPrincipal`; the only
character-specific input here is that nonprincipal Dirichlet characters map
to nonprincipal native characters. No primitive-character hypothesis is used. -/
theorem LFunction_ne_zero_of_native_continuation
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (θ : ℝ)
    (P : Prop) (f : ℂ → ℂ)
    (hnonprincipal : χ ≠ 1 → ¬ P)
    (hf : DifferentiableOn ℂ f ({1}ᶜ : Set ℂ))
    (hentire : ¬ P → Differentiable ℂ f)
    (hmatch : ∀ s : ℂ, 1 < s.re → f s = DirichletCharacter.LFunction χ s)
    (hnz : ∀ s : ℂ, θ < s.re → (s ≠ 1 ∨ ¬ P) → f s ≠ 0)
    {s : ℂ} (hs : θ < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  by_cases hsone : s = 1
  · have hχ : χ ≠ 1 := fun h ↦ hpole ⟨h, hsone⟩
    have hP : ¬ P := hnonprincipal hχ
    have heq := eq_LFunction_of_halfPlane_of_ne_one χ hχ f (hentire hP) hmatch
    rw [← heq]
    exact hnz s hs (.inr hP)
  · have heq := eqOn_LFunction_of_halfPlane χ f hf hmatch hsone
    rw [← heq]
    exact hnz s hs (.inl hsone)

end GaoDirichletBridge

#print axioms GaoDirichletBridge.eqOn_LFunction_of_halfPlane
#print axioms GaoDirichletBridge.eq_LFunction_of_halfPlane_of_ne_one
#print axioms GaoDirichletBridge.LFunction_ne_zero_of_native_continuation
