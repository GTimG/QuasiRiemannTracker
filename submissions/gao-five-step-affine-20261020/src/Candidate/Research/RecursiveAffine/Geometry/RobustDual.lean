import Mathlib

/- Exact rational affine certificates and their real robust consumers.
All arithmetic certificates are ordinary kernel proofs. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Geometry
noncomputable section
open scoped BigOperators

abbrev Affine (n : ℕ) := Fin (n+1) → ℚ

def constant {n : ℕ} (q : ℚ) : Affine n := fun i => if i.val = 0 then q else 0

def eval {n : ℕ} (a : Affine n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (a i : ℝ) * Fin.cases 1 x i

theorem eval_constant {n : ℕ} (q : ℚ) (x : Fin n → ℝ) :
    eval (constant q) x = (q : ℝ) := by
  simp [eval, constant, Fin.sum_univ_succ]

theorem eval_add {n : ℕ} (a b : Affine n) (x : Fin n → ℝ) :
    eval (fun i => a i + b i) x = eval a x + eval b x := by
  simp [eval, Rat.cast_add, add_mul, Finset.sum_add_distrib]

theorem eval_weighted {n k : ℕ} (w : Fin k → ℚ) (a : Fin k → Affine n) (x : Fin n → ℝ) :
    eval (fun i => ∑ j, w j * a j i) x = ∑ j, (w j : ℝ) * eval (a j) x := by
  simp only [eval, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A real finite dual bound remains valid if each constraint is at least
`-E`. The full multiplier mass, rather than a count of constraints, pays the
perturbation. No sign of E is needed. -/
theorem robust_dual_bound {k : ℕ} (w c : Fin k → ℝ) (margin E objective : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hc : ∀ j, -E ≤ c j)
    (hid : objective = margin + ∑ j, w j * c j) :
    margin - E * (∑ j, w j) ≤ objective := by
  have hs : (∑ j, w j * (-E)) ≤ ∑ j, w j * c j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hc j) (hw j))
  rw [← Finset.sum_mul] at hs
  nlinarith only [hs, hid]

/-- The exact certificate data. The rows are precisely the selected native
constraints; prefix/exclusion admissibility is recorded by each instance. -/
structure Certificate (n k : ℕ) where
  objective : Affine n
  rows : Fin k → Affine n
  weights : Fin k → ℚ
  margin : ℚ
  weights_nonneg : ∀ j, 0 ≤ weights j
  coordinate_identity : ∀ i,
    objective i = constant margin i + ∑ j, weights j * rows j i
  margin_gt : (157 / 100000000000 : ℚ) < margin
  mass_lt : (∑ j, weights j) < 1489

theorem Certificate.real_identity {n k : ℕ} (C : Certificate n k) (x : Fin n → ℝ) :
    eval C.objective x = (C.margin : ℝ) + ∑ j, (C.weights j : ℝ) * eval (C.rows j) x := by
  have hform : C.objective = fun i => constant C.margin i + ∑ j, C.weights j * C.rows j i :=
    funext C.coordinate_identity
  rw [hform, eval_add, eval_constant, eval_weighted]

theorem Certificate.bound_of_constraint_error {n k : ℕ} (C : Certificate n k)
    (x : Fin n → ℝ) (E : ℝ) (hc : ∀ j, -E ≤ eval (C.rows j) x) :
    (C.margin : ℝ) - E * (∑ j, (C.weights j : ℝ)) ≤ eval C.objective x := by
  apply robust_dual_bound _ _ _ _ _ _ hc (C.real_identity x)
  intro j
  exact_mod_cast C.weights_nonneg j

/-- Every specific certificate has margin greater than 1.57e-9 and total
dual weight less than 1489. Constraint error at most 1e-15 leaves this
strictly positive uniform reserve. -/
theorem Certificate.uniform_robust_lower {n k : ℕ} (C : Certificate n k)
    (x : Fin n → ℝ) (E : ℝ) (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (C.rows j) x) :
    (1568511 / 1000000000000000 : ℝ) < eval C.objective x := by
  have hmargin : (157 / 100000000000 : ℝ) < (C.margin : ℝ) := by
    have hcast : (((157 / 100000000000 : ℚ) : ℝ)) < (C.margin : ℝ) :=
      Rat.cast_lt.mpr C.margin_gt
    norm_num at hcast
    exact hcast
  have hmass : (∑ j, (C.weights j : ℝ)) ≤ 1489 := by
    exact_mod_cast C.mass_lt.le
  have hmass0 : 0 ≤ ∑ j, (C.weights j : ℝ) := by
    apply Finset.sum_nonneg
    intro j _
    exact_mod_cast C.weights_nonneg j
  have herror : E * (∑ j, (C.weights j : ℝ)) ≤ (1 / 1000000000000000 : ℝ) * 1489 :=
    (mul_le_mul_of_nonneg_right hE hmass0).trans
      (mul_le_mul_of_nonneg_left hmass (by norm_num))
  have hb := C.bound_of_constraint_error x E hc
  linarith only [hmargin, herror, hb]

theorem Certificate.positive_of_constraint_error {n k : ℕ} (C : Certificate n k)
    (x : Fin n → ℝ) (E : ℝ) (hE : E ≤ 1 / 1000000000000000)
    (hc : ∀ j, -E ≤ eval (C.rows j) x) :
    0 < eval C.objective x :=
  lt_trans (by norm_num) (C.uniform_robust_lower x E hE hc)

end
end OAI.SevenEighths.Cycle153Geometry

#print axioms OAI.SevenEighths.Cycle153Geometry.Certificate.uniform_robust_lower
