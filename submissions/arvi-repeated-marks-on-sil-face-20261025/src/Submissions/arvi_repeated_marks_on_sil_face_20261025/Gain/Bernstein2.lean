import Mathlib.Tactic

/-!
# Bicubic Bernstein positivity on a box, with a computable rational checker.
-/

set_option autoImplicit false
namespace QRH.RepeatedMarks
open Finset BigOperators

/-- Cubic Bernstein basis on `[0,1]`. -/
noncomputable def bb3 (k : Fin 4) (u : ℝ) : ℝ :=
  ((3:ℕ).choose (k:ℕ) : ℝ) * u^(k:ℕ) * (1-u)^(3-(k:ℕ))

theorem bb3_nonneg (k : Fin 4) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ bb3 k u := by
  unfold bb3; have : 0 ≤ 1 - u := by linarith
  positivity

theorem bb3_sum (u : ℝ) : ∑ k : Fin 4, bb3 k u = 1 := by
  simp [Fin.sum_univ_four, bb3, Nat.choose]; ring

theorem pos_of_bern3 (β : Fin 4 → ℝ) (hβ : ∀ k, 0 < β k) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 < ∑ k : Fin 4, β k * bb3 k u := by
  obtain ⟨k0, hpos⟩ : ∃ k, 0 < bb3 k u := by
    by_contra hcon
    push Not at hcon
    have : ∑ k : Fin 4, bb3 k u ≤ 0 := sum_nonpos (fun k _ => hcon k)
    linarith [bb3_sum u]
  calc (0:ℝ) < β k0 * bb3 k0 u := mul_pos (hβ k0) hpos
    _ ≤ ∑ k : Fin 4, β k * bb3 k u :=
        single_le_sum (fun k _ => mul_nonneg (hβ k).le (bb3_nonneg k h0 h1)) (mem_univ k0)

theorem pos_of_bern33 (β : Fin 4 → Fin 4 → ℝ) (hβ : ∀ i j, 0 < β i j)
    {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < ∑ i : Fin 4, ∑ j : Fin 4, β i j * bb3 i u * bb3 j v := by
  have h : ∀ i, 0 < ∑ j : Fin 4, β i j * bb3 j v := fun i => pos_of_bern3 (β i) (hβ i) hv0 hv1
  have := pos_of_bern3 (fun i => ∑ j : Fin 4, β i j * bb3 j v) h hu0 hu1
  convert this using 1
  apply sum_congr rfl; intro i _
  rw [sum_mul]; apply sum_congr rfl; intro j _; ring

/-! ## Computable transforms over a field -/

section transforms
variable {K : Type*} [Field K]

/-- Power coefficients after `x = a + s u`. -/
def shift3 (c : Fin 4 → K) (a s : K) : Fin 4 → K :=
  ![c 0 + c 1*a + c 2*a^2 + c 3*a^3,
    s*(c 1 + 2*c 2*a + 3*c 3*a^2),
    s^2*(c 2 + 3*c 3*a),
    s^3*c 3]

/-- Cubic Bernstein coefficients from power coefficients on `[0,1]`. -/
def bern3 (e : Fin 4 → K) : Fin 4 → K :=
  ![e 0, e 0 + e 1/3, e 0 + 2*e 1/3 + e 2/3, e 0 + e 1 + e 2 + e 3]

/-- Bicubic Bernstein coefficients of `∑ c i j x^i y^j` on `[a,a+s] × [b,b+t]`. -/
def bern33 (c : Fin 4 → Fin 4 → K) (a s b t : K) : Fin 4 → Fin 4 → K :=
  fun I J => bern3 (fun j => bern3 (fun i => shift3 (fun i' => shift3 (c i') b t j) a s i) I) J

end transforms

theorem cubic_eval_bern (c : Fin 4 → ℝ) (a s u : ℝ) :
    ∑ i : Fin 4, c i * (a + s*u)^(i:ℕ) = ∑ k : Fin 4, bern3 (shift3 c a s) k * bb3 k u := by
  simp [Fin.sum_univ_four, shift3, bern3, bb3, Nat.choose]
  ring

theorem bicubic_eval_bern (c : Fin 4 → Fin 4 → ℝ) (a s b t u v : ℝ) :
    ∑ i : Fin 4, ∑ j : Fin 4, c i j * (a + s*u)^(i:ℕ) * (b + t*v)^(j:ℕ) =
      ∑ I : Fin 4, ∑ J : Fin 4, bern33 c a s b t I J * bb3 I u * bb3 J v := by
  simp [Fin.sum_univ_four, shift3, bern3, bern33, bb3, Nat.choose]
  ring

/-- **Soundness**: positive bicubic Bernstein coefficients give positivity on the box. -/
theorem bicubic_pos (c : Fin 4 → Fin 4 → ℝ) {a s b t x y : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hx0 : a ≤ x) (hx1 : x ≤ a + s) (hy0 : b ≤ y) (hy1 : y ≤ b + t)
    (hβ : ∀ I J, 0 < bern33 c a s b t I J) :
    0 < ∑ i : Fin 4, ∑ j : Fin 4, c i j * x^(i:ℕ) * y^(j:ℕ) := by
  set u := (x - a)/s
  set v := (y - b)/t
  have hxu : x = a + s*u := by simp only [u]; field_simp; ring
  have hyv : y = b + t*v := by simp only [v]; field_simp; ring
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hs.le
  have hu1 : u ≤ 1 := (div_le_one hs).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg (by linarith) ht.le
  have hv1 : v ≤ 1 := (div_le_one ht).mpr (by linarith)
  rw [hxu, hyv, bicubic_eval_bern]
  exact pos_of_bern33 _ hβ hu0 hu1 hv0 hv1

/-- Cast compatibility: rational Bernstein coefficients map to real ones. -/
theorem bern33_cast (c : Fin 4 → Fin 4 → ℚ) (a s b t : ℚ) (I J : Fin 4) :
    ((bern33 c a s b t I J : ℚ) : ℝ) =
      bern33 (fun i j => (c i j : ℝ)) (a:ℝ) (s:ℝ) (b:ℝ) (t:ℝ) I J := by
  fin_cases I <;> fin_cases J <;> simp [bern33, bern3, shift3] <;> push_cast <;> ring


/-! ## Recursive bisection certificates -/

inductive Split where
  | leaf : Split
  | nu : Split → Split → Split
  | p : Split → Split → Split
  deriving Repr

/-- All sixteen bicubic Bernstein coefficients are positive. -/
def leafOK (c : Fin 4 → Fin 4 → ℚ) (a s b t : ℚ) : Bool :=
  decide (∀ I J : Fin 4, 0 < bern33 c a s b t I J)

/-- Check positivity on `[a,a+s] × [b,b+t]` following a bisection tree. -/
def checkBox (c : Fin 4 → Fin 4 → ℚ) : Split → ℚ → ℚ → ℚ → ℚ → Bool
  | .leaf, a, s, b, t => leafOK c a s b t
  | .nu l r, a, s, b, t => checkBox c l a (s/2) b t && checkBox c r (a + s/2) (s/2) b t
  | .p l r, a, s, b, t => checkBox c l a s b (t/2) && checkBox c r a s (b + t/2) (t/2)

theorem checkBox_sound (c : Fin 4 → Fin 4 → ℚ) (T : Split) :
    ∀ (a s b t : ℚ), 0 < s → 0 < t → checkBox c T a s b t = true →
      ∀ x y : ℝ, (a:ℝ) ≤ x → x ≤ (a:ℝ) + s → (b:ℝ) ≤ y → y ≤ (b:ℝ) + t →
        0 < ∑ i : Fin 4, ∑ j : Fin 4, (c i j : ℝ) * x^(i:ℕ) * y^(j:ℕ) := by
  induction T with
  | leaf =>
    intro a s b t hs ht hc x y hx0 hx1 hy0 hy1
    simp only [checkBox, leafOK, decide_eq_true_eq] at hc
    apply bicubic_pos (fun i j => (c i j : ℝ)) (a := (a:ℝ)) (s := (s:ℝ)) (b := (b:ℝ)) (t := (t:ℝ))
      (by exact_mod_cast hs) (by exact_mod_cast ht) hx0 hx1 hy0 hy1
    intro I J
    rw [← bern33_cast]
    exact_mod_cast hc I J
  | nu l r ihl ihr =>
    intro a s b t hs ht hc x y hx0 hx1 hy0 hy1
    simp only [checkBox, Bool.and_eq_true] at hc
    rcases le_total x ((a:ℝ) + (s:ℝ)/2) with hx | hx
    · exact ihl a (s/2) b t (by linarith) ht hc.1 x y hx0 (by push_cast; linarith) hy0 hy1
    · exact ihr (a + s/2) (s/2) b t (by linarith) ht hc.2 x y (by push_cast; linarith)
        (by push_cast; linarith) hy0 hy1
  | p l r ihl ihr =>
    intro a s b t hs ht hc x y hx0 hx1 hy0 hy1
    simp only [checkBox, Bool.and_eq_true] at hc
    rcases le_total y ((b:ℝ) + (t:ℝ)/2) with hy | hy
    · exact ihl a s b (t/2) hs (by linarith) hc.1 x y hx0 hx1 hy0 (by push_cast; linarith)
    · exact ihr a s (b + t/2) (t/2) hs (by linarith) hc.2 x y hx0 hx1 (by push_cast; linarith)
        (by push_cast; linarith)

/-- Example: `(x - 1/2)^2 + y^2 + 1/10 > 0` on `[0,1]^2`, checked by `decide`. -/
def exPoly : Fin 4 → Fin 4 → ℚ :=
  ![![1/4 + 1/10, 0, 1, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0]]
example : checkBox exPoly (.nu .leaf .leaf) 0 1 0 1 = true := by decide +kernel

end QRH.RepeatedMarks
