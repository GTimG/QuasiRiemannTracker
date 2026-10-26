/- Strict monotonicity and continuity of a rational expression along its first coordinate, from a
kernel test on its fraction `N/D`: the side conditions and `D` have strict signs on a box and
`N' D - N D'` is positive there, where `'` is the derivative in the first coordinate.
Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.RatExpr
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace Cycle63.Certificate

section Derivative

variable {R : Type} (C : Coeffs R)

/-- The derivative in the first coordinate of the polynomial `c₀ + x₀ (c₁ + x₀ (…))`:
`(c + x₀ P)' = P + x₀ P'`. -/
def pderiv : List R → List R
  | [] => []
  | _ :: p => padd C p (C.ofRat 0 :: pderiv p)

theorem tailPt_update_zero (x : ℕ → ℝ) (t : ℝ) : tailPt (Function.update x 0 t) = tailPt x := by
  funext i
  simp [tailPt]

theorem hasDerivAt_peval (x : ℕ → ℝ) : ∀ p : List R,
    HasDerivAt (fun t => peval C p (Function.update x 0 t)) (peval C (pderiv C p) x) (x 0)
  | [] => by
    simp only [peval, pderiv]
    exact hasDerivAt_const (x 0) (0 : ℝ)
  | a :: p => by
    have hfun : (fun t => peval C (a :: p) (Function.update x 0 t)) =
        fun t => C.eval a (tailPt x) + t * peval C p (Function.update x 0 t) := by
      funext t
      rw [peval_cons, tailPt_update_zero, Function.update_self]
    rw [hfun]
    have hd := ((hasDerivAt_id (x 0)).mul (hasDerivAt_peval x p)).const_add (C.eval a (tailPt x))
    simp only [id, Function.update_eq_self, one_mul] at hd
    convert hd using 1
    all_goals first
      | (funext t; simp only [Pi.mul_apply, id])
      | (show peval C (padd C p (C.ofRat 0 :: pderiv C p)) x = _
         rw [peval_padd, peval_cons, C.eval_ofRat]
         push_cast
         ring)

end Derivative

namespace RatExpr

/-- The numerator `N' D - N D'` of the derivative of the fraction `N/D` in the first coordinate,
for polynomials in `k + 1` variables. -/
def fracDerivNum (k : ℕ) (f : Frac (PolyN (k + 1))) : PolyN (k + 1) :=
  padd (coeffsN k) (pmul (coeffsN k) (pderiv (coeffsN k) f.num) f.den)
    (psmul (coeffsN k) (-1) (pmul (coeffsN k) f.num (pderiv (coeffsN k) f.den)))

/-- The kernel test of strict monotonicity along the first coordinate on a box: increasing when
`increasing` is true, decreasing otherwise. -/
def monoTest (k : ℕ) (increasing : Bool) (e : RatExpr) (box : List (ℚ × ℚ)) (d : ℕ) : Bool :=
  let f := e.toFrac (coeffsN (k + 1))
  e.varsLt (coeffsN (k + 1)).nvars &&
    (distinctSides (coeffsN (k + 1)) f.sides).all (fun s => signOn (coeffsN (k + 1)) s box d) &&
    signOn (coeffsN (k + 1)) f.den box d &&
    posOnSplit (coeffsN (k + 1))
      (bif increasing then fracDerivNum k f else (coeffsN (k + 1)).smul (-1) (fracDerivNum k f)) box d

theorem eval_fracDerivNum (k : ℕ) (f : Frac (PolyN (k + 1))) (x : ℕ → ℝ) :
    (coeffsN (k + 1)).eval (fracDerivNum k f) x =
      peval (coeffsN k) (pderiv (coeffsN k) f.num) x * peval (coeffsN k) f.den x -
        peval (coeffsN k) f.num x * peval (coeffsN k) (pderiv (coeffsN k) f.den) x := by
  show peval (coeffsN k) (fracDerivNum k f) x = _
  simp only [fracDerivNum, peval_padd, peval_psmul]
  erw [peval_pmul, peval_pmul]
  push_cast
  ring

/-- Strict monotonicity and continuity along the first coordinate on `[a, b]` from the kernel
test. -/
theorem monotone_of_monoTest (k : ℕ) (increasing : Bool) (e : RatExpr) (box : List (ℚ × ℚ))
    (d : ℕ) (h : monoTest k increasing e box d = true) (x : ℕ → ℝ) (a b : ℝ)
    (hbox : ∀ t ∈ Set.Icc a b, InBox box (Function.update x 0 t)) :
    (increasing = true → StrictMonoOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b)) ∧
      (increasing = false →
        StrictAntiOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b)) ∧
      ContinuousOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b) := by
  simp only [monoTest, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hv, hs⟩, hden⟩, hpos⟩ := h
  set f := e.toFrac (coeffsN (k + 1)) with hf
  let N : ℝ → ℝ := fun t => peval (coeffsN k) f.num (Function.update x 0 t)
  let D : ℝ → ℝ := fun t => peval (coeffsN k) f.den (Function.update x 0 t)
  -- On the segment the expression is `N/D` and `D` does not vanish.
  have hD : ∀ t ∈ Set.Icc a b, D t ≠ 0 := fun t ht =>
    signOn_sound (coeffsN (k + 1)) f.den box d hden _ (hbox t ht)
  have hexpr : ∀ t ∈ Set.Icc a b, e.denote (Function.update x 0 t) = N t / D t := by
    intro t ht
    have hs' : ∀ s ∈ f.sides, (coeffsN (k + 1)).eval s (Function.update x 0 t) ≠ 0 := by
      intro s hsm
      rcases distinctSides_cover (coeffsN (k + 1)) _ _ s hsm with h1 | ⟨s', hs'', heq⟩
      · rw [h1]; exact one_ne_zero
      · rw [heq]; exact signOn_sound (coeffsN (k + 1)) s' box d (hs s' hs'') _ (hbox t ht)
    exact toFrac_sound (coeffsN (k + 1)) e _ hv hs' (hD t ht)
  -- The quotient has derivative `(N' D - N D')/D²` at every point of the segment.
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => N s / D s)
      ((peval (coeffsN k) (pderiv (coeffsN k) f.num) (Function.update x 0 t) * D t -
        N t * peval (coeffsN k) (pderiv (coeffsN k) f.den) (Function.update x 0 t)) / D t ^ 2) t := by
    intro t ht
    have hN := hasDerivAt_peval (coeffsN k) (Function.update x 0 t) f.num
    have hDd := hasDerivAt_peval (coeffsN k) (Function.update x 0 t) f.den
    simp only [Function.update_idem, Function.update_self] at hN hDd
    exact hN.div hDd (hD t ht)
  have hsign : ∀ t ∈ Set.Icc a b, (bif increasing then 1 else -1 : ℝ) *
      ((peval (coeffsN k) (pderiv (coeffsN k) f.num) (Function.update x 0 t) * D t -
        N t * peval (coeffsN k) (pderiv (coeffsN k) f.den) (Function.update x 0 t)) / D t ^ 2) > 0 := by
    intro t ht
    have hp := posOnSplit_sound (coeffsN (k + 1)) _ box d hpos _ (hbox t ht)
    have hD2 : 0 < D t ^ 2 := by positivity [hD t ht]
    cases increasing
    · simp only [Bool.cond_false, (coeffsN (k + 1)).eval_smul, eval_fracDerivNum] at hp
      push_cast at hp
      simp only [Bool.cond_false]
      rw [neg_one_mul, ← neg_div]
      exact div_pos (by linarith) hD2
    · simp only [Bool.cond_true, eval_fracDerivNum] at hp
      simp only [Bool.cond_true, one_mul]
      exact div_pos hp hD2
  have hcont : ContinuousOn (fun s => N s / D s) (Set.Icc a b) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  refine ⟨?_, ?_, hcont.congr fun t ht => hexpr t ht⟩
  · intro hinc
    subst hinc
    have hmono : StrictMonoOn (fun s => N s / D s) (Set.Icc a b) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
      intro t ht
      have ht' := interior_subset ht
      rw [(hderiv t ht').deriv]
      simpa using hsign t ht'
    exact hmono.congr fun t ht => (hexpr t ht).symm
  · intro hdec
    subst hdec
    have hanti : StrictAntiOn (fun s => N s / D s) (Set.Icc a b) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont
      intro t ht
      have ht' := interior_subset ht
      rw [(hderiv t ht').deriv]
      have := hsign t ht'
      simp only [Bool.cond_false, neg_one_mul] at this
      linarith
    exact hanti.congr fun t ht => (hexpr t ht).symm

end RatExpr

end Cycle63.Certificate
