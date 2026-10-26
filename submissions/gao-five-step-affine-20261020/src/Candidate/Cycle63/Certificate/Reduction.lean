/- Equality on a box of a rational expression with another one: their fractions with all
denominators multiplied out have equal cross products on a grid of rational points, so everywhere
by the combinatorial Nullstellensatz, and every divisor agrees in the same way with a quotient of
polynomials with strict signs on the box. Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.RatExpr
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Combinatorics.Nullstellensatz

set_option autoImplicit false

namespace Cycle63.Certificate

namespace RatExpr

open MvPolynomial

/-! ### The fraction with all denominators multiplied out -/

/-- Its integer numerator and denominator at an integer point, a constant `c` contributing
`c.num/c.den`. -/
def fracAt (pt : ℕ → ℤ) : RatExpr → ℤ × ℤ
  | const c => (c.num, c.den)
  | var i => (pt i, 1)
  | add a b =>
    match fracAt pt a, fracAt pt b with
    | (n₁, d₁), (n₂, d₂) => (n₁ * d₂ + n₂ * d₁, d₁ * d₂)
  | sub a b =>
    match fracAt pt a, fracAt pt b with
    | (n₁, d₁), (n₂, d₂) => (n₁ * d₂ - n₂ * d₁, d₁ * d₂)
  | mul a b =>
    match fracAt pt a, fracAt pt b with
    | (n₁, d₁), (n₂, d₂) => (n₁ * n₂, d₁ * d₂)
  | div a b =>
    match fracAt pt a, fracAt pt b with
    | (n₁, d₁), (n₂, d₂) => (n₁ * d₂, d₁ * n₂)
  | neg a =>
    match fracAt pt a with
    | (n₁, d₁) => (-n₁, d₁)
  | pow a k =>
    match fracAt pt a with
    | (n₁, d₁) => (n₁ ^ k, d₁ ^ k)

/-- Bounds of the degrees in the variable `i` of its numerator and denominator. -/
def fracDeg (i : ℕ) : RatExpr → ℕ × ℕ
  | const _ => (0, 0)
  | var j => (if j = i then 1 else 0, 0)
  | add a b => (max ((fracDeg i a).1 + (fracDeg i b).2) ((fracDeg i b).1 + (fracDeg i a).2),
      (fracDeg i a).2 + (fracDeg i b).2)
  | sub a b => (max ((fracDeg i a).1 + (fracDeg i b).2) ((fracDeg i b).1 + (fracDeg i a).2),
      (fracDeg i a).2 + (fracDeg i b).2)
  | mul a b => ((fracDeg i a).1 + (fracDeg i b).1, (fracDeg i a).2 + (fracDeg i b).2)
  | div a b => ((fracDeg i a).1 + (fracDeg i b).2, (fracDeg i a).2 + (fracDeg i b).1)
  | neg a => fracDeg i a
  | pow a k => (k * (fracDeg i a).1, k * (fracDeg i a).2)

/-- Its numerator and denominator at a real point. -/
noncomputable def fracReal (x : ℕ → ℝ) : RatExpr → ℝ × ℝ
  | const c => ((c.num : ℝ), (c.den : ℝ))
  | var i => (x i, 1)
  | add a b => ((fracReal x a).1 * (fracReal x b).2 + (fracReal x b).1 * (fracReal x a).2,
      (fracReal x a).2 * (fracReal x b).2)
  | sub a b => ((fracReal x a).1 * (fracReal x b).2 - (fracReal x b).1 * (fracReal x a).2,
      (fracReal x a).2 * (fracReal x b).2)
  | mul a b => ((fracReal x a).1 * (fracReal x b).1, (fracReal x a).2 * (fracReal x b).2)
  | div a b => ((fracReal x a).1 * (fracReal x b).2, (fracReal x a).2 * (fracReal x b).1)
  | neg a => (-(fracReal x a).1, (fracReal x a).2)
  | pow a k => ((fracReal x a).1 ^ k, (fracReal x a).2 ^ k)

/-- Its numerator and denominator as polynomials in the first `n` variables. -/
noncomputable def fracPoly (n : ℕ) : RatExpr → MvPolynomial (Fin n) ℚ × MvPolynomial (Fin n) ℚ
  | const c => (C (c.num : ℚ), C (c.den : ℚ))
  | var i => (if h : i < n then X ⟨i, h⟩ else 0, 1)
  | add a b => ((fracPoly n a).1 * (fracPoly n b).2 + (fracPoly n b).1 * (fracPoly n a).2,
      (fracPoly n a).2 * (fracPoly n b).2)
  | sub a b => ((fracPoly n a).1 * (fracPoly n b).2 - (fracPoly n b).1 * (fracPoly n a).2,
      (fracPoly n a).2 * (fracPoly n b).2)
  | mul a b => ((fracPoly n a).1 * (fracPoly n b).1, (fracPoly n a).2 * (fracPoly n b).2)
  | div a b => ((fracPoly n a).1 * (fracPoly n b).2, (fracPoly n a).2 * (fracPoly n b).1)
  | neg a => (-(fracPoly n a).1, (fracPoly n a).2)
  | pow a k => ((fracPoly n a).1 ^ k, (fracPoly n a).2 ^ k)

/-- Every divisor of the expression is nonzero at the point. -/
def DivisorsNonzero (x : ℕ → ℝ) : RatExpr → Prop
  | const _ => True
  | var _ => True
  | add a b => DivisorsNonzero x a ∧ DivisorsNonzero x b
  | sub a b => DivisorsNonzero x a ∧ DivisorsNonzero x b
  | mul a b => DivisorsNonzero x a ∧ DivisorsNonzero x b
  | div a b => DivisorsNonzero x a ∧ DivisorsNonzero x b ∧ b.denote x ≠ 0
  | neg a => DivisorsNonzero x a
  | pow a _ => DivisorsNonzero x a

/-- Where no divisor vanishes, the denominator does not vanish and the expression is the
quotient. -/
theorem fracReal_spec (x : ℕ → ℝ) : ∀ e : RatExpr, DivisorsNonzero x e →
    (fracReal x e).2 ≠ 0 ∧ e.denote x = (fracReal x e).1 / (fracReal x e).2
  | const c, _ => by
    refine ⟨by simp [fracReal, c.den_nz], ?_⟩
    simp only [fracReal, denote]
    exact Rat.cast_def c
  | var i, _ => by simp [fracReal, denote]
  | add a b, h => by
    obtain ⟨ha, hb⟩ := h
    obtain ⟨da, ea⟩ := fracReal_spec x a ha
    obtain ⟨db, eb⟩ := fracReal_spec x b hb
    refine ⟨mul_ne_zero da db, ?_⟩
    simp only [denote, fracReal, ea, eb]
    field_simp
  | sub a b, h => by
    obtain ⟨ha, hb⟩ := h
    obtain ⟨da, ea⟩ := fracReal_spec x a ha
    obtain ⟨db, eb⟩ := fracReal_spec x b hb
    refine ⟨mul_ne_zero da db, ?_⟩
    simp only [denote, fracReal, ea, eb]
    field_simp
  | mul a b, h => by
    obtain ⟨ha, hb⟩ := h
    obtain ⟨da, ea⟩ := fracReal_spec x a ha
    obtain ⟨db, eb⟩ := fracReal_spec x b hb
    refine ⟨mul_ne_zero da db, ?_⟩
    simp only [denote, fracReal, ea, eb]
    field_simp
  | div a b, h => by
    obtain ⟨ha, hb, hne⟩ := h
    obtain ⟨da, ea⟩ := fracReal_spec x a ha
    obtain ⟨db, eb⟩ := fracReal_spec x b hb
    have nb : (fracReal x b).1 ≠ 0 := by
      intro h0
      rw [eb, h0, zero_div] at hne
      exact hne rfl
    refine ⟨mul_ne_zero da nb, ?_⟩
    simp only [denote, fracReal, ea, eb]
    field_simp
  | neg a, h => by
    obtain ⟨da, ea⟩ := fracReal_spec x a h
    refine ⟨da, ?_⟩
    simp only [denote, fracReal, ea]
    ring
  | pow a k, h => by
    obtain ⟨da, ea⟩ := fracReal_spec x a h
    refine ⟨pow_ne_zero k da, ?_⟩
    simp only [denote, fracReal, ea, div_pow]

/-- The real evaluation of the polynomials is the fraction at the real point. -/
theorem aeval_fracPoly (n : ℕ) (x : ℕ → ℝ) : ∀ e : RatExpr, e.varsLt n = true →
    aeval (fun i : Fin n => x i) (fracPoly n e).1 = (fracReal x e).1 ∧
      aeval (fun i : Fin n => x i) (fracPoly n e).2 = (fracReal x e).2
  | const c, _ => by simp [fracPoly, fracReal]
  | var i, h => by
    simp only [varsLt, decide_eq_true_eq] at h
    simp [fracPoly, fracReal, h]
  | add a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h.1
    obtain ⟨nb, db⟩ := aeval_fracPoly n x b h.2
    simp [fracPoly, fracReal, na, da, nb, db]
  | sub a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h.1
    obtain ⟨nb, db⟩ := aeval_fracPoly n x b h.2
    simp [fracPoly, fracReal, na, da, nb, db]
  | mul a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h.1
    obtain ⟨nb, db⟩ := aeval_fracPoly n x b h.2
    simp [fracPoly, fracReal, na, da, nb, db]
  | div a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h.1
    obtain ⟨nb, db⟩ := aeval_fracPoly n x b h.2
    simp [fracPoly, fracReal, na, da, nb, db]
  | neg a, h => by
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h
    simp [fracPoly, fracReal, na, da]
  | pow a k, h => by
    obtain ⟨na, da⟩ := aeval_fracPoly n x a h
    simp [fracPoly, fracReal, na, da]

/-- The evaluation of the polynomials at an integer point is the computed fraction there. -/
theorem eval_fracPoly (n : ℕ) (pt : ℕ → ℤ) : ∀ e : RatExpr, e.varsLt n = true →
    eval (fun i : Fin n => (pt i : ℚ)) (fracPoly n e).1 = (fracAt pt e).1 ∧
      eval (fun i : Fin n => (pt i : ℚ)) (fracPoly n e).2 = (fracAt pt e).2
  | const c, _ => by simp [fracPoly, fracAt]
  | var i, h => by
    simp only [varsLt, decide_eq_true_eq] at h
    simp [fracPoly, fracAt, h]
  | add a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h.1
    obtain ⟨nb, db⟩ := eval_fracPoly n pt b h.2
    simp only [fracPoly, fracAt, map_add, map_mul, na, da, nb, db, Int.cast_add, Int.cast_mul, and_self]
  | sub a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h.1
    obtain ⟨nb, db⟩ := eval_fracPoly n pt b h.2
    simp only [fracPoly, fracAt, map_sub, map_mul, na, da, nb, db, Int.cast_sub, Int.cast_mul, and_self]
  | mul a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h.1
    obtain ⟨nb, db⟩ := eval_fracPoly n pt b h.2
    simp only [fracPoly, fracAt, map_mul, na, da, nb, db, Int.cast_mul, and_self]
  | div a b, h => by
    simp only [varsLt, Bool.and_eq_true] at h
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h.1
    obtain ⟨nb, db⟩ := eval_fracPoly n pt b h.2
    simp only [fracPoly, fracAt, map_mul, na, da, nb, db, Int.cast_mul, and_self]
  | neg a, h => by
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h
    simp only [fracPoly, fracAt, map_neg, na, da, Int.cast_neg, and_self]
  | pow a k, h => by
    obtain ⟨na, da⟩ := eval_fracPoly n pt a h
    simp only [fracPoly, fracAt, map_pow, na, da, Int.cast_pow, and_self]

/-- The degrees of the polynomials are within the computed bounds. -/
theorem degreeOf_fracPoly (n : ℕ) (i : Fin n) : ∀ e : RatExpr,
    degreeOf i (fracPoly n e).1 ≤ (fracDeg i e).1 ∧ degreeOf i (fracPoly n e).2 ≤ (fracDeg i e).2
  | const c => ⟨(degreeOf_C _ _).le, (degreeOf_C _ _).le⟩
  | var j => by
    classical
    by_cases hj : j < n
    · simp only [fracPoly, fracDeg, hj, dite_true, degreeOf_one, le_refl, and_true]
      rw [degreeOf_X]
      by_cases hij : i = ⟨j, hj⟩
      · subst hij; simp
      · have : j ≠ i := fun h => hij (Fin.ext h.symm)
        simp [hij, this]
    · simp [fracPoly, fracDeg, hj, degreeOf_zero, degreeOf_one]
  | add a b => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    obtain ⟨nb, db⟩ := degreeOf_fracPoly n i b
    simp only [fracPoly, fracDeg]
    constructor
    · refine (degreeOf_add_le _ _ _).trans (max_le_max ?_ ?_)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add na db)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add nb da)
    · exact (degreeOf_mul_le _ _ _).trans (add_le_add da db)
  | sub a b => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    obtain ⟨nb, db⟩ := degreeOf_fracPoly n i b
    simp only [fracPoly, fracDeg]
    constructor
    · refine (degreeOf_sub_le _ _ _).trans (max_le_max ?_ ?_)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add na db)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add nb da)
    · exact (degreeOf_mul_le _ _ _).trans (add_le_add da db)
  | mul a b => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    obtain ⟨nb, db⟩ := degreeOf_fracPoly n i b
    exact ⟨(degreeOf_mul_le _ _ _).trans (add_le_add na nb),
      (degreeOf_mul_le _ _ _).trans (add_le_add da db)⟩
  | div a b => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    obtain ⟨nb, db⟩ := degreeOf_fracPoly n i b
    exact ⟨(degreeOf_mul_le _ _ _).trans (add_le_add na db),
      (degreeOf_mul_le _ _ _).trans (add_le_add da nb)⟩
  | neg a => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    exact ⟨(degreeOf_neg _ _).le.trans na, da⟩
  | pow a k => by
    obtain ⟨na, da⟩ := degreeOf_fracPoly n i a
    exact ⟨(degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left k na),
      (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_left k da)⟩

/-! ### The identity on a grid -/

/-- The points of the grid `S₀ × S₁ × ⋯`, as lists of coordinates. -/
def gridPoints : List (List ℤ) → List (List ℤ)
  | [] => [[]]
  | s :: rest => s.flatMap fun c => (gridPoints rest).map (c :: ·)

/-- The point whose `i`-th coordinate is the `i`-th entry of the list. -/
def ptOfListZ (g : List ℤ) : ℕ → ℤ := fun i => g.getD i 0

/-- The cross products of the fractions of the two expressions agree at every point of the
grid. -/
def agreeOnGrid (e₁ e₂ : RatExpr) (grid : List (List ℤ)) : Bool :=
  (gridPoints grid).all fun g =>
    match fracAt (ptOfListZ g) e₁, fracAt (ptOfListZ g) e₂ with
    | (n₁, d₁), (n₂, d₂) => n₁ * d₂ == n₂ * d₁

theorem agreeOnGrid_append (e₁ e₂ : RatExpr) (s t : List ℤ) (rest : List (List ℤ)) :
    agreeOnGrid e₁ e₂ ((s ++ t) :: rest) =
      (agreeOnGrid e₁ e₂ (s :: rest) && agreeOnGrid e₁ e₂ (t :: rest)) := by
  simp [agreeOnGrid, gridPoints, List.flatMap_append, List.all_append]

/-- The degree bound in the variable `i` of the cross difference of the two fractions. -/
def crossDeg (e₁ e₂ : RatExpr) (i : ℕ) : ℕ :=
  max ((fracDeg i e₁).1 + (fracDeg i e₂).2) ((fracDeg i e₂).1 + (fracDeg i e₁).2)

/-- The side conditions of the identity: both expressions in the variables of the grid, each list
of the grid without repetitions and longer than the degree bound of its variable. -/
def gridAdmissible (e₁ e₂ : RatExpr) (grid : List (List ℤ)) : Bool :=
  e₁.varsLt grid.length && e₂.varsLt grid.length &&
    (List.range grid.length).all fun i =>
      (grid.getD i []).Nodup && decide (crossDeg e₁ e₂ i < (grid.getD i []).length)

theorem mem_gridPoints : ∀ (grid : List (List ℤ)) (g : List ℤ),
    g ∈ gridPoints grid ↔ g.length = grid.length ∧ ∀ i < grid.length, g.getD i 0 ∈ grid.getD i []
  | [], g => by
    simp only [gridPoints, List.mem_singleton, List.length_nil, not_lt_zero, false_imp_iff,
      implies_true, and_true]
    exact ⟨fun h => by simp [h], fun h => List.eq_nil_of_length_eq_zero h⟩
  | s :: rest, g => by
    simp only [gridPoints, List.mem_flatMap, List.mem_map, List.length_cons]
    constructor
    · rintro ⟨c, hc, g', hg', rfl⟩
      rw [mem_gridPoints rest g'] at hg'
      refine ⟨by simp [hg'.1], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hc
      | succ k => simpa using hg'.2 k (by omega)
    · rintro ⟨hlen, hall⟩
      cases g with
      | nil => simp at hlen
      | cons c g' =>
        refine ⟨c, by simpa using hall 0 (by omega), g', ?_, rfl⟩
        rw [mem_gridPoints rest g']
        refine ⟨by simpa using hlen, fun i hi => ?_⟩
        simpa using hall (i + 1) (by omega)

/-- Two expressions whose cross products agree on an admissible grid have equal cross products of
their fractions as polynomials, so at every real point. -/
theorem cross_eq_of_agreeOnGrid (e₁ e₂ : RatExpr) (grid : List (List ℤ))
    (hadm : gridAdmissible e₁ e₂ grid = true) (hagree : agreeOnGrid e₁ e₂ grid = true)
    (x : ℕ → ℝ) :
    (fracReal x e₁).1 * (fracReal x e₂).2 = (fracReal x e₂).1 * (fracReal x e₁).2 := by
  set n := grid.length with hn
  simp only [gridAdmissible, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at hadm
  obtain ⟨⟨hv₁, hv₂⟩, hgrid⟩ := hadm
  set F : MvPolynomial (Fin n) ℚ :=
    (fracPoly n e₁).1 * (fracPoly n e₂).2 - (fracPoly n e₂).1 * (fracPoly n e₁).2 with hF
  have hzero : F = 0 := by
    apply eq_zero_of_eval_zero_at_prod_finset F
      (fun i => ((grid.getD i []).map (Int.cast : ℤ → ℚ)).toFinset)
    · intro i
      obtain ⟨hnd, hlen⟩ := hgrid i i.isLt
      rw [List.toFinset_card_of_nodup (hnd.map Int.cast_injective), List.length_map]
      refine lt_of_le_of_lt ?_ hlen
      obtain ⟨n₁, d₁⟩ := degreeOf_fracPoly n i e₁
      obtain ⟨n₂, d₂⟩ := degreeOf_fracPoly n i e₂
      refine (degreeOf_sub_le _ _ _).trans (max_le_max ?_ ?_)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add n₁ d₂)
      · exact (degreeOf_mul_le _ _ _).trans (add_le_add n₂ d₁)
    · intro y hy
      have hpre : ∀ i : Fin n, ∃ z ∈ grid.getD i [], (z : ℚ) = y i := by
        intro i
        have := hy i
        simpa only [List.mem_toFinset, List.mem_map] using this
      choose z hz hzy using hpre
      let g : List ℤ := List.ofFn z
      have hg : g ∈ gridPoints grid := by
        rw [mem_gridPoints]
        refine ⟨by simp [g, hn], fun i hi => ?_⟩
        have hi' : i < n := hi
        simpa [g, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi'] using hz ⟨i, hi'⟩
      simp only [agreeOnGrid, List.all_eq_true] at hagree
      have hpt := hagree g hg
      have hy' : (fun i : Fin n => ((ptOfListZ g i : ℤ) : ℚ)) = y := by
        funext i
        rw [← hzy i]
        simp [ptOfListZ, g, List.getD_eq_getElem?_getD]
      obtain ⟨a₁, b₁⟩ := eval_fracPoly n (ptOfListZ g) e₁ hv₁
      obtain ⟨a₂, b₂⟩ := eval_fracPoly n (ptOfListZ g) e₂ hv₂
      rw [hy'] at a₁ b₁ a₂ b₂
      have hcross : (fracAt (ptOfListZ g) e₁).1 * (fracAt (ptOfListZ g) e₂).2 =
          (fracAt (ptOfListZ g) e₂).1 * (fracAt (ptOfListZ g) e₁).2 := by
        revert hpt
        generalize fracAt (ptOfListZ g) e₁ = f₁
        generalize fracAt (ptOfListZ g) e₂ = f₂
        obtain ⟨n₁, d₁⟩ := f₁
        obtain ⟨n₂, d₂⟩ := f₂
        simp
      simp only [hF, map_sub, map_mul, a₁, b₁, a₂, b₂]
      rw [← Int.cast_mul, ← Int.cast_mul, hcross, sub_self]
  have hreal := congrArg (aeval (fun i : Fin n => x i)) hzero
  obtain ⟨a₁, b₁⟩ := aeval_fracPoly n x e₁ hv₁
  obtain ⟨a₂, b₂⟩ := aeval_fracPoly n x e₂ hv₂
  simp only [hF, map_sub, map_mul, map_zero, a₁, b₁, a₂, b₂] at hreal
  linarith

/-- Two expressions whose cross products agree on an admissible grid are equal at every point
where neither has a vanishing divisor. -/
theorem denote_eq_of_agreeOnGrid (e₁ e₂ : RatExpr) (grid : List (List ℤ))
    (hadm : gridAdmissible e₁ e₂ grid = true) (hagree : agreeOnGrid e₁ e₂ grid = true)
    (x : ℕ → ℝ) (h₁ : DivisorsNonzero x e₁) (h₂ : DivisorsNonzero x e₂) :
    e₁.denote x = e₂.denote x := by
  obtain ⟨d₁, v₁⟩ := fracReal_spec x e₁ h₁
  obtain ⟨d₂, v₂⟩ := fracReal_spec x e₂ h₂
  have hc := cross_eq_of_agreeOnGrid e₁ e₂ grid hadm hagree x
  rw [v₁, v₂, div_eq_div_iff d₁ d₂, hc]

/-! ### Divisors certified by their reduced fractions -/

deriving instance DecidableEq for RatExpr

/-- The divisors of the expression, the second arguments of its quotients, innermost first. -/
def divisors : RatExpr → List RatExpr
  | const _ => []
  | var _ => []
  | add a b => divisors a ++ divisors b
  | sub a b => divisors a ++ divisors b
  | mul a b => divisors a ++ divisors b
  | div a b => divisors a ++ divisors b ++ [b]
  | neg a => divisors a
  | pow a _ => divisors a

theorem divisorsNonzero_of_forall (x : ℕ → ℝ) : ∀ e : RatExpr,
    (∀ b ∈ divisors e, b.denote x ≠ 0) → DivisorsNonzero x e
  | const _, _ => trivial
  | var _, _ => trivial
  | add a b, h => ⟨divisorsNonzero_of_forall x a fun c hc => h c (by simp [divisors, hc]),
      divisorsNonzero_of_forall x b fun c hc => h c (by simp [divisors, hc])⟩
  | sub a b, h => ⟨divisorsNonzero_of_forall x a fun c hc => h c (by simp [divisors, hc]),
      divisorsNonzero_of_forall x b fun c hc => h c (by simp [divisors, hc])⟩
  | mul a b, h => ⟨divisorsNonzero_of_forall x a fun c hc => h c (by simp [divisors, hc]),
      divisorsNonzero_of_forall x b fun c hc => h c (by simp [divisors, hc])⟩
  | div a b, h => ⟨divisorsNonzero_of_forall x a fun c hc => h c (by simp [divisors, hc]),
      divisorsNonzero_of_forall x b fun c hc => h c (by simp [divisors, hc]),
      h b (by simp [divisors])⟩
  | neg a, h => divisorsNonzero_of_forall x a h
  | pow a _, h => divisorsNonzero_of_forall x a h

section DivisionFree

variable {R : Type} (C : Coeffs R)

/-- An expression without quotients has no side conditions and the denominator `1`. -/
theorem toFrac_of_divisors_nil (x : ℕ → ℝ) : ∀ e : RatExpr, divisors e = [] →
    (e.toFrac C).sides = [] ∧ C.eval (e.toFrac C).den x = 1
  | const c, _ => by simp [toFrac, C.eval_ofRat]
  | var i, _ => by simp [toFrac, C.eval_ofRat]
  | add a b, h => by
    simp only [divisors, List.append_eq_nil_iff] at h
    obtain ⟨sa, da⟩ := toFrac_of_divisors_nil x a h.1
    obtain ⟨sb, db⟩ := toFrac_of_divisors_nil x b h.2
    simp only [toFrac, fracAdd]
    cases C.beq (a.toFrac C).den (b.toFrac C).den <;> simp [sa, sb, da, db, C.eval_mul]
  | sub a b, h => by
    simp only [divisors, List.append_eq_nil_iff] at h
    obtain ⟨sa, da⟩ := toFrac_of_divisors_nil x a h.1
    obtain ⟨sb, db⟩ := toFrac_of_divisors_nil x b h.2
    simp only [toFrac, fracSub]
    cases C.beq (a.toFrac C).den (b.toFrac C).den <;> simp [sa, sb, da, db, C.eval_mul]
  | mul a b, h => by
    simp only [divisors, List.append_eq_nil_iff] at h
    obtain ⟨sa, da⟩ := toFrac_of_divisors_nil x a h.1
    obtain ⟨sb, db⟩ := toFrac_of_divisors_nil x b h.2
    simp [toFrac, fracMul, sa, sb, da, db, C.eval_mul]
  | div a b, h => by simp [divisors] at h
  | neg a, h => by
    obtain ⟨sa, da⟩ := toFrac_of_divisors_nil x a h
    simp [toFrac, sa, da]
  | pow a n, h => by
    obtain ⟨sa, da⟩ := toFrac_of_divisors_nil x a h
    simp [toFrac, sa, eval_cpow, da]

/-- An expression without quotients is its numerator polynomial. -/
theorem denote_of_divisors_nil (x : ℕ → ℝ) (e : RatExpr) (hv : e.varsLt C.nvars = true)
    (h : divisors e = []) : e.denote x = C.eval (e.toFrac C).num x := by
  obtain ⟨hs, hd⟩ := toFrac_of_divisors_nil C x e h
  rw [toFrac_sound C e x hv (by simp [hs]) (by rw [hd]; exact one_ne_zero), hd, div_one]

end DivisionFree

/-- The grid on which the identity of two expressions in `n` variables is checked: one more point
than the degree bound in each variable. -/
def gridOf (e₁ e₂ : RatExpr) (n : ℕ) : List (List ℤ) :=
  (List.range n).map fun i => (List.range (crossDeg e₁ e₂ i + 1)).map fun j => (j : ℤ)

/-- A polynomial expression with a strict sign on the box, by the sign test of `S`. -/
def polySign (k : ℕ) (S : Coeffs (PolyN (k + 1))) (d : ℕ) (box : List (ℚ × ℚ)) (P : RatExpr) :
    Bool :=
  (divisors P).isEmpty && P.varsLt (k + 1) && signOn S (P.toFrac (coeffsN (k + 1))).num box d

theorem ne_zero_of_polySign (k : ℕ) (S : Coeffs (PolyN (k + 1)))
    (hS : ∀ r x, S.eval r x = (coeffsN (k + 1)).eval r x) (d : ℕ) (box : List (ℚ × ℚ))
    (P : RatExpr) (h : polySign k S d box P = true) (x : ℕ → ℝ) (hx : InBox box x) :
    divisors P = [] ∧ P.denote x ≠ 0 := by
  simp only [polySign, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨hnil, hv⟩, hs⟩ := h
  refine ⟨hnil, ?_⟩
  rw [denote_of_divisors_nil (coeffsN (k + 1)) x P (by rw [coeffsN_nvars]; exact hv) hnil, ← hS]
  exact signOn_sound S _ box d hs x hx

/-- One step of the divisor certificate: the divisor `b` agrees with `P/Q` on the grid, its own
divisors are among the known ones, and `P` and `Q` are polynomials with strict signs on the box. -/
def divisorStep (k : ℕ) (S : Coeffs (PolyN (k + 1))) (d : ℕ) (box : List (ℚ × ℚ))
    (known : List RatExpr) (b P Q : RatExpr) : Bool :=
  (divisors b).all (known.contains ·) && polySign k S d box P && polySign k S d box Q &&
    gridAdmissible b (div P Q) (gridOf b (div P Q) (k + 1)) &&
    agreeOnGrid b (div P Q) (gridOf b (div P Q) (k + 1))

/-- The divisor certificate: each step uses the divisors certified before it. -/
def divisorChain (k : ℕ) (S : Coeffs (PolyN (k + 1))) (d : ℕ) (box : List (ℚ × ℚ)) :
    List RatExpr → List (RatExpr × RatExpr × RatExpr) → Bool
  | _, [] => true
  | known, (b, P, Q) :: rest =>
    divisorStep k S d box known b P Q && divisorChain k S d box (b :: known) rest

theorem ne_zero_of_divisorStep (k : ℕ) (S : Coeffs (PolyN (k + 1)))
    (hS : ∀ r x, S.eval r x = (coeffsN (k + 1)).eval r x) (d : ℕ) (box : List (ℚ × ℚ))
    (known : List RatExpr) (b P Q : RatExpr) (h : divisorStep k S d box known b P Q = true)
    (x : ℕ → ℝ) (hx : InBox box x)
    (hknown : ∀ c ∈ known, c.denote x ≠ 0) : b.denote x ≠ 0 := by
  simp only [divisorStep, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨hcov, hP⟩, hQ⟩, hadm⟩, hagree⟩ := h
  obtain ⟨hPnil, hP0⟩ := ne_zero_of_polySign k S hS d box P hP x hx
  obtain ⟨hQnil, hQ0⟩ := ne_zero_of_polySign k S hS d box Q hQ x hx
  have hb : DivisorsNonzero x b := divisorsNonzero_of_forall x b fun c hc => hknown c (hcov c hc)
  have hPQ : DivisorsNonzero x (div P Q) :=
    ⟨divisorsNonzero_of_forall x P (by simp [hPnil]), divisorsNonzero_of_forall x Q (by simp [hQnil]),
      hQ0⟩
  rw [denote_eq_of_agreeOnGrid b (div P Q) _ hadm hagree x hb hPQ, denote]
  exact div_ne_zero hP0 hQ0

theorem ne_zero_of_divisorChain (k : ℕ) (S : Coeffs (PolyN (k + 1)))
    (hS : ∀ r x, S.eval r x = (coeffsN (k + 1)).eval r x) (d : ℕ) (box : List (ℚ × ℚ))
    (x : ℕ → ℝ) (hx : InBox box x) :
    ∀ (known : List RatExpr) (certs : List (RatExpr × RatExpr × RatExpr)),
      divisorChain k S d box known certs = true → (∀ c ∈ known, c.denote x ≠ 0) →
        ∀ c ∈ certs.map (·.1) ++ known, c.denote x ≠ 0
  | known, [], _, hknown => by simpa using hknown
  | known, (b, P, Q) :: rest, h, hknown => by
    simp only [divisorChain, Bool.and_eq_true] at h
    have hb := ne_zero_of_divisorStep k S hS d box known b P Q h.1 x hx hknown
    have hall := ne_zero_of_divisorChain k S hS d box x hx (b :: known) rest h.2 (by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hknown c hc)
    intro c hc
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc
    · exact hb
    · exact hall c (List.mem_append_left _ hc)
    · exact hall c (List.mem_append_right _ (List.mem_cons_of_mem _ hc))

/-- No divisor of the expression vanishes on the box when all of them are certified. -/
def divisorsCertified (k : ℕ) (S : Coeffs (PolyN (k + 1))) (d : ℕ) (box : List (ℚ × ℚ))
    (e : RatExpr) (certs : List (RatExpr × RatExpr × RatExpr)) : Bool :=
  divisorChain k S d box [] certs && (divisors e).all ((certs.map (·.1)).contains ·)

theorem divisorsNonzero_of_certified (k : ℕ) (S : Coeffs (PolyN (k + 1)))
    (hS : ∀ r x, S.eval r x = (coeffsN (k + 1)).eval r x) (d : ℕ) (box : List (ℚ × ℚ))
    (e : RatExpr) (certs : List (RatExpr × RatExpr × RatExpr))
    (h : divisorsCertified k S d box e certs = true) (x : ℕ → ℝ) (hx : InBox box x) :
    DivisorsNonzero x e := by
  simp only [divisorsCertified, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  have hall := ne_zero_of_divisorChain k S hS d box x hx [] certs h.1 (by simp)
  exact divisorsNonzero_of_forall x e fun c hc => hall c (by simpa using h.2 c hc)

end RatExpr

end Cycle63.Certificate
