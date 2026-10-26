import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Polynomial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Lemmas
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Positivity of polynomials on boxes by product-form Bernstein coefficients, computed and checked
inside Lean. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Certificate

/-- An entry of a list at an index below its length belongs to the list. -/
theorem getD_mem_of_lt {α : Type} (d : α) : ∀ (l : List α) {j : ℕ}, j < l.length → l.getD j d ∈ l
  | [], j, hj => absurd hj (Nat.not_lt_zero j)
  | a :: l, 0, _ => List.mem_cons_self
  | a :: l, j + 1, hj => by
    simp only [List.getD_cons_succ]
    exact List.mem_cons_of_mem a (getD_mem_of_lt d l (by simpa using hj))

/-- The product-form Bernstein identity of degree `n` on an interval of width `w`, for the
coefficients `c` of a polynomial in `u` of degree at most `n`. -/
theorem bernstein_identity (n : ℕ) (c : ℕ → ℝ) (u w : ℝ) (hw : w ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), c k * u ^ k =
      ∑ i ∈ Finset.range (n + 1),
        (∑ k ∈ Finset.range (i + 1), (Nat.choose (n - k) (i - k) : ℝ) / w ^ (n - k) * c k) *
          (u ^ i * (w - u) ^ (n - i)) := by
  -- Exchange the two sums: `i` runs over `[k, n]` for each `k`.
  have hswap : ∑ i ∈ Finset.range (n + 1),
      (∑ k ∈ Finset.range (i + 1), (Nat.choose (n - k) (i - k) : ℝ) / w ^ (n - k) * c k) *
        (u ^ i * (w - u) ^ (n - i)) =
      ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.Ico k (n + 1),
        (Nat.choose (n - k) (i - k) : ℝ) / w ^ (n - k) * c k * (u ^ i * (w - u) ^ (n - i)) := by
    simp only [Finset.sum_mul, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1)
      (fun k i => (Nat.choose (n - k) (i - k) : ℝ) / w ^ (n - k) * c k *
        (u ^ i * (w - u) ^ (n - i)))).symm
  rw [hswap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- Reindex `i = k + j` and apply the binomial theorem to `(u + (w - u))^(n - k)`.
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - k = (n - k) + 1 by omega]
  have hbin : (u + (w - u)) ^ (n - k) =
      ∑ j ∈ Finset.range (n - k + 1), u ^ j * (w - u) ^ (n - k - j) * (Nat.choose (n - k) j : ℝ) :=
    add_pow u (w - u) (n - k)
  have hw' : w ^ (n - k) ≠ 0 := pow_ne_zero _ hw
  have hterm : ∀ j ∈ Finset.range (n - k + 1),
      (Nat.choose (n - k) (k + j - k) : ℝ) / w ^ (n - k) * c k *
        (u ^ (k + j) * (w - u) ^ (n - (k + j))) =
      c k * u ^ k / w ^ (n - k) * (u ^ j * (w - u) ^ (n - k - j) * (Nat.choose (n - k) j : ℝ)) := by
    intro j _
    rw [show k + j - k = j by omega, show n - (k + j) = n - k - j by omega, pow_add]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← hbin, show u + (w - u) = w by ring]
  field_simp

section Bernstein

variable {R : Type} (C : Coeffs R)

/-- Taylor shift: the coefficients of `p (lo + u)` in `u`. -/
def taylorShift (lo : ℚ) (p : List R) : List R :=
  p.foldr (fun a acc => padd C [a] (padd C (psmul C lo acc) (C.ofRat 0 :: acc))) []

/-- The point with its first coordinate moved by `-lo`. -/
def shiftPt (lo : ℚ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => if i = 0 then x 0 - lo else x i

theorem tailPt_shiftPt (lo : ℚ) (x : ℕ → ℝ) : tailPt (shiftPt lo x) = tailPt x := by
  funext i
  simp [tailPt, shiftPt]

theorem length_padd : ∀ (p q : List R), (padd C p q).length = max p.length q.length
  | [], q => by simp [padd]
  | a :: p, [] => by simp [padd]
  | a :: p, b :: q => by simp [padd, length_padd p q, Nat.succ_max_succ]

theorem length_taylorShift (lo : ℚ) : ∀ p : List R, (taylorShift C lo p).length = p.length
  | [] => rfl
  | a :: p => by
    have ih := length_taylorShift lo p
    show (padd C [a] (padd C (psmul C lo (taylorShift C lo p))
      (C.ofRat 0 :: taylorShift C lo p))).length = p.length + 1
    simp only [length_padd, psmul, List.length_map, List.length_cons, List.length_nil, ih]
    omega

theorem peval_taylorShift (lo : ℚ) : ∀ (p : List R) (x : ℕ → ℝ),
    peval C (taylorShift C lo p) (shiftPt lo x) = peval C p x
  | [], x => rfl
  | a :: p, x => by
    have ih := peval_taylorShift lo p x
    show peval C (padd C [a] (padd C (psmul C lo (taylorShift C lo p))
      (C.ofRat 0 :: taylorShift C lo p))) (shiftPt lo x) = peval C (a :: p) x
    rw [peval_padd, peval_padd, peval_psmul, peval_cons, peval_cons, peval_cons, peval_nil, ih,
      C.eval_ofRat, tailPt_shiftPt]
    simp only [shiftPt]
    push_cast
    ring

/-- The value of a coefficient list as the sum of its terms. -/
theorem peval_eq_sum : ∀ (p : List R) (x : ℕ → ℝ),
    peval C p x = ∑ k ∈ Finset.range p.length, C.eval (p.getD k (C.ofRat 0)) (tailPt x) * x 0 ^ k
  | [], x => by simp [peval]
  | a :: p, x => by
    rw [peval_cons, peval_eq_sum p x, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- Product-form Bernstein coefficients `g` of `p` on `[lo, hi]`, with
`p = Σ_i g_i (X - lo)^i (hi - X)^(n - i)` and `n + 1 = p.length`:
`g_i = Σ_{k ≤ i} C(n - k, i - k) d_k / (hi - lo)^(n - k)` for the Taylor coefficients `d` of `p` at
`lo` (`bernstein_identity`). -/
def bernCoeffs (lo hi : ℚ) (p : List R) : List R :=
  let n := p.length - 1
  let d := taylorShift C lo p
  let e := (List.range (n + 1)).map fun k => C.smul (1 / (hi - lo) ^ (n - k)) (d.getD k (C.ofRat 0))
  (List.range (n + 1)).map fun i =>
    (List.range (i + 1)).foldr
      (fun k acc => C.add (C.smul (Nat.choose (n - k) (i - k) : ℚ) (e.getD k (C.ofRat 0))) acc)
      (C.ofRat 0)

theorem length_bernCoeffs (lo hi : ℚ) (p : List R) :
    (bernCoeffs C lo hi p).length = p.length - 1 + 1 := by
  simp [bernCoeffs]

theorem eval_foldr_add_smul (f : ℕ → ℚ) (v : ℕ → R) (y : ℕ → ℝ) : ∀ l : List ℕ,
    C.eval (l.foldr (fun k acc => C.add (C.smul (f k) (v k)) acc) (C.ofRat 0)) y =
      (l.map fun k => (f k : ℝ) * C.eval (v k) y).sum
  | [] => by simp [C.eval_ofRat]
  | k :: l => by
    simp only [List.foldr_cons, C.eval_add, C.eval_smul, List.map_cons, List.sum_cons]
    rw [eval_foldr_add_smul f v y l]

theorem sum_range_map (f : ℕ → ℝ) : ∀ m : ℕ,
    ((List.range m).map f).sum = ∑ k ∈ Finset.range m, f k
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_map f m, Finset.sum_range_succ]
    simp

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {m k : ℕ} (hk : k < m) :
    ((List.range m).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The value of the `i`-th coefficient, as the sum of `bernstein_identity`. -/
theorem eval_bernCoeffs (lo hi : ℚ) (p : List R) (y : ℕ → ℝ) {i : ℕ} (hi' : i < p.length - 1 + 1) :
    C.eval ((bernCoeffs C lo hi p).getD i (C.ofRat 0)) y =
      ∑ k ∈ Finset.range (i + 1), (Nat.choose (p.length - 1 - k) (i - k) : ℝ) /
        ((hi : ℝ) - lo) ^ (p.length - 1 - k) *
          C.eval ((taylorShift C lo p).getD k (C.ofRat 0)) y := by
  unfold bernCoeffs
  simp only
  rw [getD_range_map _ _ hi', eval_foldr_add_smul, sum_range_map]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < p.length - 1 + 1 := by
    have := Finset.mem_range.mp hk; omega
  rw [getD_range_map _ _ hk', C.eval_smul]
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
  ring

/-- Positivity test on a box whose first interval is the range of the polynomial variable: every
product-form Bernstein coefficient is positive on the rest of the box. -/
def polyPosOn (p : List R) : List (ℚ × ℚ) → Bool
  | [] => false
  | I :: box => decide (I.1 < I.2) && (bernCoeffs C I.1 I.2 p).all (fun g => C.posOn g box)

theorem polyPosOn_sound (p : List R) (box : List (ℚ × ℚ)) (h : polyPosOn C p box = true)
    (x : ℕ → ℝ) (hx : InBox box x) : 0 < peval C p x := by
  cases box with
  | nil => simp [polyPosOn] at h
  | cons I box =>
    simp only [polyPosOn, Bool.and_eq_true] at h
    obtain ⟨hlt, hpos⟩ := h
    have hlt : I.1 < I.2 := of_decide_eq_true hlt
    have hpos := List.all_eq_true.mp hpos
    obtain ⟨hlo, hhi, hrest⟩ := hx
    set n := p.length - 1 with hn
    set u : ℝ := x 0 - I.1 with hu
    set w : ℝ := (I.2 : ℝ) - I.1 with hw
    have hwpos : 0 < w := by rw [hw]; exact_mod_cast sub_pos.mpr hlt
    set c : ℕ → ℝ := fun k => C.eval ((taylorShift C I.1 p).getD k (C.ofRat 0)) (tailPt x) with hc
    -- The value of `p` as the Taylor sum at `lo`, then in product-form Bernstein form.
    have hsum : peval C p x = ∑ k ∈ Finset.range (n + 1), c k * u ^ k := by
      rw [← peval_taylorShift C I.1 p x, peval_eq_sum, tailPt_shiftPt, length_taylorShift]
      have hlen : p.length ≤ n + 1 := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hlen]
      have hrest' : ∑ k ∈ Finset.Ico p.length (n + 1), c k * u ^ k = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk' : p.length ≤ k := (Finset.mem_Ico.mp hk).1
        have hnil : (taylorShift C I.1 p).getD k (C.ofRat 0) = C.ofRat 0 := by
          exact List.getD_eq_default _ _ (by rw [length_taylorShift]; exact hk')
        simp only [hc, hnil, C.eval_ofRat, Rat.cast_zero, zero_mul]
      rw [hrest', add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hc, shiftPt, hu]
    rw [hsum, bernstein_identity n c u w hwpos.ne']
    -- Every Bernstein coefficient is positive, every basis value is nonnegative, and the first or
    -- the last basis value is positive.
    have hcoef : ∀ i ∈ Finset.range (n + 1),
        0 < ∑ k ∈ Finset.range (i + 1), (Nat.choose (n - k) (i - k) : ℝ) / w ^ (n - k) * c k := by
      intro i hi'
      have hi'' : i < p.length - 1 + 1 := Finset.mem_range.mp hi'
      have hg := C.posOn_sound _ box (hpos _ (getD_mem_of_lt (C.ofRat 0) _
        (by rw [length_bernCoeffs]; exact hi''))) (tailPt x) hrest
      rw [eval_bernCoeffs C I.1 I.2 p (tailPt x) hi''] at hg
      exact hg
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have huw : u ≤ w := by rw [hu, hw]; linarith
    apply Finset.sum_pos'
    · intro i hi'
      exact mul_nonneg (hcoef i hi').le (mul_nonneg (pow_nonneg hu0 _) (pow_nonneg (by linarith) _))
    · rcases lt_or_eq_of_le huw with hlt' | heq
      · refine ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), mul_pos (hcoef 0 (by simp)) ?_⟩
        simp only [pow_zero, one_mul, Nat.sub_zero]
        exact pow_pos (by linarith) _
      · refine ⟨n, Finset.self_mem_range_succ n, mul_pos (hcoef n (Finset.self_mem_range_succ n)) ?_⟩
        rw [Nat.sub_self, pow_zero, mul_one, heq]
        exact pow_pos hwpos _

end Bernstein

/-- Polynomials whose coefficients lie in `R`, in one more variable. -/
def Coeffs.poly {R : Type} (C : Coeffs R) : Coeffs (List R) where
  nvars := C.nvars + 1
  add := padd C
  mul := pmul C
  smul := psmul C
  ofRat := fun c => [C.ofRat c]
  var := fun i => if i = 0 then [C.ofRat 0, C.ofRat 1] else [C.var (i - 1)]
  isZero := fun p => p.all C.isZero
  beq := pbeq C
  posOn := polyPosOn C
  eval := peval C
  eval_add := peval_padd C
  eval_mul := peval_pmul C
  eval_smul := peval_psmul C
  eval_ofRat := by intro c x; simp [peval, C.eval_ofRat]
  eval_var := by
    intro i hi x
    by_cases h : i = 0
    · subst h; simp [peval, C.eval_ofRat]
    · simp only [h, ite_false, peval, mul_zero, add_zero]
      rw [C.eval_var (i - 1) (by omega)]
      simp only [tailPt]
      congr 1
      omega
  isZero_sound := fun p h x => peval_zero_of_all_isZero C p h x
  beq_sound := pbeq_sound C
  posOn_sound := polyPosOn_sound C

/-- Polynomials in `k` variables with rational coefficients. -/
def PolyN : ℕ → Type
  | 0 => ℚ
  | k + 1 => List (PolyN k)

/-- Coefficient arithmetic of polynomials in `k` variables. -/
def coeffsN : (k : ℕ) → Coeffs (PolyN k)
  | 0 => ratCoeffs
  | k + 1 => (coeffsN k).poly

theorem coeffsN_nvars : ∀ k : ℕ, (coeffsN k).nvars = k
  | 0 => rfl
  | k + 1 => by
    show (coeffsN k).nvars + 1 = k + 1
    rw [coeffsN_nvars k]

/-- The two halves of a box split at the midpoint of its `i`-th interval. -/
def splitBox : List (ℚ × ℚ) → ℕ → List (ℚ × ℚ) × List (ℚ × ℚ)
  | [], _ => ([], [])
  | I :: box, 0 => ((I.1, (I.1 + I.2) / 2) :: box, ((I.1 + I.2) / 2, I.2) :: box)
  | I :: box, i + 1 => (I :: (splitBox box i).1, I :: (splitBox box i).2)

theorem inBox_splitBox : ∀ (box : List (ℚ × ℚ)) (i : ℕ) (x : ℕ → ℝ), InBox box x →
    InBox (splitBox box i).1 x ∨ InBox (splitBox box i).2 x
  | [], _, _, _ => Or.inl trivial
  | I :: box, 0, x, ⟨hlo, hhi, hrest⟩ => by
    rcases le_total (x 0) (((I.1 + I.2) / 2 : ℚ) : ℝ) with h | h
    · exact Or.inl ⟨hlo, h, hrest⟩
    · exact Or.inr ⟨h, hhi, hrest⟩
  | I :: box, i + 1, x, ⟨hlo, hhi, hrest⟩ => by
    rcases inBox_splitBox box i (tailPt x) hrest with h | h
    · exact Or.inl ⟨hlo, hhi, h⟩
    · exact Or.inr ⟨hlo, hhi, h⟩

/-- The index of a widest interval of a box (the first one among equals). -/
def widestIndex : List (ℚ × ℚ) → ℕ
  | [] => 0
  | I :: box =>
    match box with
    | [] => 0
    | J :: rest =>
      let k := widestIndex (J :: rest)
      bif decide ((I.2 - I.1) < ((J :: rest).getD k (0, 0)).2 - ((J :: rest).getD k (0, 0)).1)
      then k + 1 else 0

/-- Positivity test with bisection: the direct test, or both halves after splitting a widest
interval, down to depth `d`. -/
def posOnSplit {R : Type} (C : Coeffs R) (p : R) : List (ℚ × ℚ) → ℕ → Bool
  | box, 0 => C.posOn p box
  | box, d + 1 => C.posOn p box ||
      (posOnSplit C p (splitBox box (widestIndex box)).1 d &&
        posOnSplit C p (splitBox box (widestIndex box)).2 d)

/-- The bisection test passes on a box when it passes on both halves; the two halves can then be
checked separately. -/
theorem posOnSplit_of_halves {R : Type} (C : Coeffs R) (p : R) (box : List (ℚ × ℚ)) (d : ℕ)
    (h₁ : posOnSplit C p (splitBox box (widestIndex box)).1 d = true)
    (h₂ : posOnSplit C p (splitBox box (widestIndex box)).2 d = true) :
    posOnSplit C p box (d + 1) = true := by
  simp only [posOnSplit, h₁, h₂, Bool.and_self, Bool.or_true]

theorem posOnSplit_sound {R : Type} (C : Coeffs R) (p : R) : ∀ (box : List (ℚ × ℚ)) (d : ℕ),
    posOnSplit C p box d = true → ∀ x, InBox box x → 0 < C.eval p x
  | box, 0, h, x, hx => C.posOn_sound p box h x hx
  | box, d + 1, h, x, hx => by
    simp only [posOnSplit, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h1, h2⟩
    · exact C.posOn_sound p box h x hx
    · rcases inBox_splitBox box (widestIndex box) x hx with hl | hr
      · exact posOnSplit_sound C p _ d h1 x hl
      · exact posOnSplit_sound C p _ d h2 x hr

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
