/-
2026-11-03 Dirichlet specialization bridge by Zhongpai Gao with AI assistance.
Apache-2.0. Original source attribution and licenses below are retained.
This module is adapted from the isolated checked SeriesBridge.lean proof:
Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Tracker adaptation changes import paths only; all theorem bodies are unchanged.
The adapter applies to the genuine strengthened native Hecke theorem; full
native endpoint compatibility and official tracker admission remain pending.
-/
/-
Rational ideal-series identification for the faithful Dirichlet / native Hecke bridge.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Uses Mathlib's L-series convergence and equivalence reindexing theorems.
The character coefficient identity is an explicit input, to be discharged by
the native character construction. The zero ideal is retained with value zero.
-/
import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.RayClasses.Character
import Submissions.gao_general_number_fields_9686.Bridge.RationalIdeals

open scoped NumberField

namespace TrackerBridge

/-- The coefficient evaluation on principal natural-number ideals determines
the value on every rational ideal, including the zero ideal. -/
theorem rat_hecke_coefficient_eq
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    {m : Ideal RatIntegers} (η : DedekindZetaZeroFree.RayClassCharacter ℚ m)
    (hcoeff : ∀ n : ℕ, η (Ideal.span {(n : RatIntegers)}) =
      if n = 0 then 0 else χ n) (I : Ideal RatIntegers) :
    η I = if Ideal.absNorm I = 0 then 0 else χ (Ideal.absNorm I) := by
  simpa only [ratIdeal_eq_span_absNorm] using hcoeff (Ideal.absNorm I)

/-- A native rational ideal-series term is exactly the corresponding Mathlib
Dirichlet-series term under the ideal norm equivalence. -/
theorem rat_hecke_term_eq
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    {m : Ideal RatIntegers} (η : DedekindZetaZeroFree.RayClassCharacter ℚ m)
    (hcoeff : ∀ n : ℕ, η (Ideal.span {(n : RatIntegers)}) =
      if n = 0 then 0 else χ n) (s : ℂ) (I : Ideal RatIntegers) :
    η I * (Ideal.absNorm I : ℂ) ^ (-s) =
      LSeries.term (fun n : ℕ ↦ χ n) s (ratIdealEquivNat I) := by
  change η I * (Ideal.absNorm I : ℂ) ^ (-s) =
    LSeries.term (fun n : ℕ ↦ χ n) s (Ideal.absNorm I)
  rw [rat_hecke_coefficient_eq χ η hcoeff I]
  by_cases hn : Ideal.absNorm I = 0
  · simp [hn]
  · simp only [ite_eq_right hn, LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-- The native ideal-indexed series of the constructed rational character
converges to the actual Mathlib Dirichlet L-function in `Re(s) > 1`. -/
theorem rat_hecke_hasSum_LFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : Ideal RatIntegers} (η : DedekindZetaZeroFree.RayClassCharacter ℚ m)
    (hcoeff : ∀ n : ℕ, η (Ideal.span {(n : RatIntegers)}) =
      if n = 0 then 0 else χ n) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal RatIntegers ↦ η I * (Ideal.absNorm I : ℂ) ^ (-s))
      (DirichletCharacter.LFunction χ s) := by
  have hnat : HasSum (LSeries.term (fun n : ℕ ↦ χ n) s)
      (DirichletCharacter.LFunction χ s) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact (χ.LSeriesSummable_of_one_lt_re hs).hasSum
  have hideal : HasSum
      (fun I : Ideal RatIntegers ↦ LSeries.term (fun n : ℕ ↦ χ n) s (ratIdealEquivNat I))
      (DirichletCharacter.LFunction χ s) :=
    (ratIdealEquivNat.hasSum_iff
      (f := LSeries.term (fun n : ℕ ↦ χ n) s)
      (a := DirichletCharacter.LFunction χ s)).mpr hnat
  exact hideal.congr_fun fun I ↦ rat_hecke_term_eq χ η hcoeff s I

/-- Uniqueness of the ideal-series sum identifies the native continuation
with Mathlib's L-function in the initial half-plane. -/
theorem rat_hecke_continuation_eq_LFunction
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : Ideal RatIntegers} (η : DedekindZetaZeroFree.RayClassCharacter ℚ m)
    (hcoeff : ∀ n : ℕ, η (Ideal.span {(n : RatIntegers)}) =
      if n = 0 then 0 else χ n)
    (f : ℂ → ℂ)
    (hsum : ∀ s : ℂ, 1 < s.re →
      HasSum (fun I : Ideal RatIntegers ↦ η I * (Ideal.absNorm I : ℂ) ^ (-s)) (f s))
    (s : ℂ) (hs : 1 < s.re) :
    f s = DirichletCharacter.LFunction χ s := by
  exact (hsum s hs).unique (rat_hecke_hasSum_LFunction χ η hcoeff hs)

end TrackerBridge

#print axioms TrackerBridge.rat_hecke_coefficient_eq
#print axioms TrackerBridge.rat_hecke_term_eq
#print axioms TrackerBridge.rat_hecke_hasSum_LFunction
#print axioms TrackerBridge.rat_hecke_continuation_eq_LFunction
