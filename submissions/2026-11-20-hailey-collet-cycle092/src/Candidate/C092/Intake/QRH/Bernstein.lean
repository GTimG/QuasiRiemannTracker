/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Sound tensor Bernstein lower bounds on closed rectangles

The univariate partition of unity is obtained by evaluating Mathlib's binomial
identity `bernsteinPolynomial.sum`. Products of these nonnegative weights give a
two-dimensional partition of unity. A lower bound for every coefficient therefore
bounds the entire polynomial, including all edges of the rectangle.

The degrees are arbitrary natural numbers. A coefficient array uses precisely
the entries `0 ≤ i ≤ n`, `0 ≤ j ≤ m`; entries outside that finite array are ignored.
This module provides no manuscript-specific coefficient array, conversion
certificate, interval endpoints, or acceptance assertion.
-/

namespace QRH.Bernstein

noncomputable section

open scoped BigOperators

/-- A convex weighted sum is bounded below by any common lower bound of its coefficients. -/
theorem weighted_lower_bound {ι : Type*} (s : Finset ι) (w c : ι → ℝ) (M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : (∑ i ∈ s, w i) = 1)
    (hc : ∀ i ∈ s, M ≤ c i) : M ≤ ∑ i ∈ s, w i * c i := by
  calc
    M = ∑ i ∈ s, w i * M := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ i ∈ s, w i * c i :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hc i hi) (hw i hi)

/-- The real Bernstein basis value `choose(n,i) * x^i * (1-x)^(n-i)`. -/
def basis (n i : ℕ) (x : ℝ) : ℝ :=
  (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i)

/-- The explicit basis value agrees with evaluation of Mathlib's Bernstein polynomial. -/
theorem basis_eq_eval (n i : ℕ) (x : ℝ) :
    basis n i x = (bernsteinPolynomial ℝ n i).eval x := by
  simp [basis, bernsteinPolynomial]

/-- All Bernstein basis weights are nonnegative on the closed unit interval. -/
theorem basis_nonneg (n i : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ basis n i x := by
  unfold basis
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

/-- The binomial theorem makes Bernstein weights a partition of unity at every real point. -/
theorem basis_sum (n : ℕ) (x : ℝ) :
    (∑ i ∈ Finset.range (n + 1), basis n i x) = 1 := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
  simpa [basis_eq_eval, Polynomial.eval_finsetSum] using h

/-- A tensor basis weight for an `(n+1)` by `(m+1)` coefficient array. -/
def tensorBasis (n m i j : ℕ) (x y : ℝ) : ℝ := basis n i x * basis m j y

/-- Tensor basis weights are nonnegative on the closed unit square. -/
theorem tensorBasis_nonneg (n m i j : ℕ) {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ tensorBasis n m i j x y :=
  mul_nonneg (basis_nonneg n i hx0 hx1) (basis_nonneg m j hy0 hy1)

/-- Products of the two univariate Bernstein bases also form a partition of unity. -/
theorem tensorBasis_sum (n m : ℕ) (x y : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (m + 1), tensorBasis n m i j x y) = 1 := by
  simp only [tensorBasis, ← Finset.mul_sum, basis_sum, mul_one]

/-- Evaluate the tensor Bernstein expansion of a finite `(n+1)` by `(m+1)` array. -/
def value (n m : ℕ) (coeff : ℕ → ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    ∑ j ∈ Finset.range (m + 1), tensorBasis n m i j x y * coeff i j

/-- A lower bound for every tensor coefficient bounds the expansion on the closed unit square. -/
theorem value_lower_bound (n m : ℕ) (coeff : ℕ → ℕ → ℝ) (M : ℝ)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1), M ≤ coeff i j) :
    M ≤ value n m coeff x y := by
  have hrow : ∀ i ∈ Finset.range (n + 1),
      M ≤ ∑ j ∈ Finset.range (m + 1), basis m j y * coeff i j := by
    intro i hi
    exact weighted_lower_bound _ _ _ M (fun j _ => basis_nonneg m j hy0 hy1)
      (basis_sum m y) (hc i hi)
  have h := weighted_lower_bound (Finset.range (n + 1)) (fun i => basis n i x)
    (fun i => ∑ j ∈ Finset.range (m + 1), basis m j y * coeff i j) M
    (fun i _ => basis_nonneg n i hx0 hx1) (basis_sum n x) hrow
  simpa [value, tensorBasis, Finset.mul_sum, mul_assoc] using h

/-- The actual bivariate polynomial encoded as an outer polynomial in `x` with coefficients in `y`. -/
def polynomial (n m : ℕ) (coeff : ℕ → ℕ → ℝ) : Polynomial (Polynomial ℝ) :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
    bernsteinPolynomial (Polynomial ℝ) n i *
      Polynomial.C (bernsteinPolynomial ℝ m j * Polynomial.C (coeff i j))

/-- Evaluate an outer polynomial in `x`, then its polynomial-in-`y` coefficients. -/
def eval (p : Polynomial (Polynomial ℝ)) (x y : ℝ) : ℝ :=
  Polynomial.eval y (Polynomial.eval (Polynomial.C x) p)

/-- Evaluation of the genuine bivariate polynomial equals its tensor Bernstein expansion. -/
theorem polynomial_eval (n m : ℕ) (coeff : ℕ → ℕ → ℝ) (x y : ℝ) :
    eval (polynomial n m coeff) x y = value n m coeff x y := by
  simp [eval, polynomial, value, tensorBasis, basis, bernsteinPolynomial,
    Polynomial.eval_finsetSum, mul_assoc]

/-- Coefficient lower bounds imply a lower bound for the associated bivariate polynomial. -/
theorem polynomial_lower_bound (n m : ℕ) (coeff : ℕ → ℕ → ℝ) (M : ℝ)
    {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1), M ≤ coeff i j) :
    M ≤ eval (polynomial n m coeff) x y := by
  rw [polynomial_eval]
  exact value_lower_bound n m coeff M hx0 hx1 hy0 hy1 hc

/-- Affine normalization of a real coordinate from `[lo,hi]` to `[0,1]`. -/
def coordinate (lo hi x : ℝ) : ℝ := (x - lo) / (hi - lo)

/-- Affine normalization preserves membership in the corresponding closed intervals. -/
theorem coordinate_mem_unit {lo hi x : ℝ} (hlt : lo < hi)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    0 ≤ coordinate lo hi x ∧ coordinate lo hi x ≤ 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hlt.le)
  · apply (div_le_one (sub_pos.mpr hlt)).mpr
    linarith

/-- Normalize both coordinates before evaluating the tensor polynomial on a physical box. -/
def boxValue (n m : ℕ) (coeff : ℕ → ℕ → ℝ)
    (uLo uHi vLo vHi x y : ℝ) : ℝ :=
  value n m coeff (coordinate uLo uHi x) (coordinate vLo vHi y)

/-- Tensor coefficient bounds certify all points of a closed, nondegenerate physical rectangle. -/
theorem boxValue_lower_bound (n m : ℕ) (coeff : ℕ → ℕ → ℝ) (M : ℝ)
    {uLo uHi vLo vHi x y : ℝ} (hu : uLo < uHi) (hv : vLo < vHi)
    (hxu : uLo ≤ x) (hxu' : x ≤ uHi) (hyv : vLo ≤ y) (hyv' : y ≤ vHi)
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1), M ≤ coeff i j) :
    M ≤ boxValue n m coeff uLo uHi vLo vHi x y := by
  have hx := coordinate_mem_unit hu hxu hxu'
  have hy := coordinate_mem_unit hv hyv hyv'
  exact value_lower_bound n m coeff M hx.1 hx.2 hy.1 hy.2 hc

/--
A verified exact Bernstein expansion transfers coefficient bounds to the target
function throughout its closed rectangle. The expansion identity is an explicit
obligation, so an unrelated coefficient table cannot certify the target function.
-/
theorem lower_bound_of_expansion (f : ℝ → ℝ → ℝ) (n m : ℕ)
    (coeff : ℕ → ℕ → ℝ) (M uLo uHi vLo vHi : ℝ)
    (hu : uLo < uHi) (hv : vLo < vHi)
    (hexp : ∀ x y, uLo ≤ x → x ≤ uHi → vLo ≤ y → y ≤ vHi →
      f x y = boxValue n m coeff uLo uHi vLo vHi x y)
    (hc : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1), M ≤ coeff i j)
    {x y : ℝ} (hxu : uLo ≤ x) (hxu' : x ≤ uHi) (hyv : vLo ≤ y) (hyv' : y ≤ vHi) :
    M ≤ f x y := by
  rw [hexp x y hxu hxu' hyv hyv']
  exact boxValue_lower_bound n m coeff M hu hv hxu hxu' hyv hyv' hc

end

/-- Execute the finite rational lower-bound checks for an `(n+1)` by `(m+1)` coefficient array. -/
def coefficientsCheck (n m : ℕ) (coeff : ℕ → ℕ → ℚ) (M : ℚ) : Bool :=
  (List.range (n + 1)).all fun i =>
    (List.range (m + 1)).all fun j => decide (M ≤ coeff i j)

/-- Acceptance of the finite rational checker proves each coefficient bound in its index range. -/
theorem coefficientsCheck_sound (n m : ℕ) (coeff : ℕ → ℕ → ℚ) (M : ℚ)
    (hcheck : coefficientsCheck n m coeff M = true)
    (i : ℕ) (hi : i ∈ Finset.range (n + 1))
    (j : ℕ) (hj : j ∈ Finset.range (m + 1)) : M ≤ coeff i j := by
  have hi' : i ∈ List.range (n + 1) := List.mem_range.mpr (Finset.mem_range.mp hi)
  have hj' : j ∈ List.range (m + 1) := List.mem_range.mpr (Finset.mem_range.mp hj)
  have hrow := (List.all_eq_true.mp hcheck) i hi'
  exact of_decide_eq_true ((List.all_eq_true.mp hrow) j hj')

/-- A checked rational coefficient array bounds its real tensor polynomial on a closed rectangle. -/
theorem checked_boxValue_lower_bound (n m : ℕ) (coeff : ℕ → ℕ → ℚ) (M : ℚ)
    (hcheck : coefficientsCheck n m coeff M = true)
    {uLo uHi vLo vHi x y : ℝ} (hu : uLo < uHi) (hv : vLo < vHi)
    (hxu : uLo ≤ x) (hxu' : x ≤ uHi) (hyv : vLo ≤ y) (hyv' : y ≤ vHi) :
    (M : ℝ) ≤ boxValue n m (fun i j => (coeff i j : ℝ)) uLo uHi vLo vHi x y := by
  apply boxValue_lower_bound n m _ (M : ℝ) hu hv hxu hxu' hyv hyv'
  intro i hi j hj
  exact_mod_cast coefficientsCheck_sound n m coeff M hcheck i hi j hj

end QRH.Bernstein
