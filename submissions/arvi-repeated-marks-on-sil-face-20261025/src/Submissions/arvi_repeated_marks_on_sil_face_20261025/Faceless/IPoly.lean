import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Poly
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Kronecker

/-!
# Integer polynomials and the integer Taylor test on dyadic intervals

The kernel evaluates integer arithmetic much faster than rational arithmetic (no normalization),
so positivity certificates run on integer polynomials. A rational polynomial `p` is first scaled
by a common denominator `D` (`toI`, checked by `isIntMul`). On the dyadic interval
`[k/2^e, (k+1)/2^e]` the test uses `Q(t) = 2^{eN} p((k + t)/2^e)`, an integer polynomial in
`t ∈ [0, 1]`: if `Σ_{i≥2} |Q_i| < min Q₀ (Q₀ + Q₁)` then `p > 0` on the interval.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless

abbrev IPoly := List ℤ

namespace IPoly

def eval : IPoly → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => (c : ℚ) + x * eval cs x

def add : IPoly → IPoly → IPoly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ℤ) (p : IPoly) : IPoly := p.map (c * ·)

@[simp] theorem eval_nil (x : ℚ) : eval [] x = 0 := rfl
@[simp] theorem eval_cons (c : ℤ) (cs : IPoly) (x : ℚ) : eval (c :: cs) x = c + x * eval cs x := rfl

@[simp] theorem eval_add (p q : IPoly) (x : ℚ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

@[simp] theorem eval_smul (c : ℤ) (p : IPoly) (x : ℚ) : eval (smul c p) x = c * eval p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-! ## The integer Taylor test on `t ∈ [0, 1]` -/

def absSum : IPoly → ℤ
  | [] => 0
  | c :: cs => |c| + absSum cs

theorem absSum_nonneg (p : IPoly) : 0 ≤ absSum p := by
  induction p with
  | nil => simp [absSum]
  | cons c p ih => simp only [absSum]; positivity

theorem abs_eval_le (p : IPoly) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |eval p t| ≤ (absSum p : ℚ) := by
  induction p with
  | nil => simp [absSum]
  | cons c p ih =>
    simp only [eval_cons, absSum]
    push_cast
    have hs : (0:ℚ) ≤ absSum p := by exact_mod_cast absSum_nonneg p
    calc |(c:ℚ) + t * eval p t| ≤ |(c:ℚ)| + |t * eval p t| := abs_add_le _ _
      _ = |(c:ℚ)| + t * |eval p t| := by rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ |(c:ℚ)| + (absSum p : ℚ) := by
          have := mul_le_mul ht1 ih (abs_nonneg _) zero_le_one
          linarith

/-- `Q > 0` on `[0, 1]`: `Σ_{i≥2} |Q_i| < min Q₀ (Q₀ + Q₁)`. -/
def tm1 : IPoly → Bool
  | [] => false
  | [c₀] => decide (0 < c₀)
  | c₀ :: c₁ :: cs => decide (absSum cs < min c₀ (c₀ + c₁))

theorem tm1_sound (Q : IPoly) (hc : tm1 Q = true) (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < eval Q t := by
  match Q, hc with
  | [c₀], hc =>
    simp only [tm1, decide_eq_true_eq] at hc
    simpa using (by exact_mod_cast hc : (0:ℚ) < c₀)
  | c₀ :: c₁ :: cs, hc =>
    simp only [tm1, decide_eq_true_eq] at hc
    have hb := abs_eval_le cs ht0 ht1
    have hmin : ((absSum cs : ℤ) : ℚ) < min (c₀ : ℚ) ((c₀ : ℚ) + c₁) := by exact_mod_cast hc
    have hlin : min (c₀:ℚ) ((c₀:ℚ) + c₁) ≤ c₀ + c₁ * t := by
      rcases le_total 0 (c₁:ℚ) with h1 | h1
      · exact (min_le_left _ _).trans (by nlinarith)
      · exact (min_le_right _ _).trans (by nlinarith)
    have hsq : t ^ 2 * |eval cs t| ≤ (absSum cs : ℚ) := by
      have : t ^ 2 ≤ 1 := by nlinarith
      calc t ^ 2 * |eval cs t| ≤ 1 * |eval cs t| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ ≤ (absSum cs : ℚ) := by simpa using hb
    have hlow : -(t ^ 2 * |eval cs t|) ≤ t ^ 2 * eval cs t := by
      have := neg_abs_le (eval cs t)
      nlinarith [sq_nonneg t]
    simp only [eval_cons]
    nlinarith

/-! ## Signed polynomials as packed pairs, and the Kronecker test

An integer polynomial is the difference of its positive and negative parts, two polynomials with
natural coefficients. Each part is packed with `Kronecker.pack`, and read back with
`Kronecker.unpack` (`eval_subD_unpack`, `subD_unpack_pack`). The Kronecker test reads the
coefficients of `t ↦ 2^{e n} p((k + t)/2^e)` off as base-`X` digits of one packed value
(`Kronecker.unpack_shift`), with `X` above the coefficient sums so that no digit carries. -/

open Faceless.Kronecker

/-- The positive part: `q = posPart q − negPart q`. -/
def posPart (q : IPoly) : List ℕ := q.map Int.toNat

/-- The negative part: `q = posPart q − negPart q`. -/
def negPart (q : IPoly) : List ℕ := q.map fun c => (-c).toNat

@[simp] theorem length_posPart (q : IPoly) : (posPart q).length = q.length := by simp [posPart]

@[simp] theorem length_negPart (q : IPoly) : (negPart q).length = q.length := by simp [negPart]

theorem eval_eq_parts (q : IPoly) (x : ℚ) :
    eval q x = evalQ (posPart q) x - evalQ (negPart q) x := by
  induction q with
  | nil => simp [posPart, negPart, evalQ]
  | cons c q ih =>
    simp only [posPart, negPart] at ih
    simp only [posPart, negPart, eval_cons, List.map_cons, evalQ, ih]
    have h := Int.toNat_sub_toNat_neg c
    have : (c : ℚ) = ((c.toNat : ℕ) : ℚ) - (((-c).toNat : ℕ) : ℚ) := by exact_mod_cast h.symm
    rw [this]; ring

/-- The difference `A − B` of two natural coefficient lists. -/
def subD (A B : List ℕ) : IPoly := List.zipWith (fun (a b : ℕ) => (a:ℤ) - (b:ℤ)) A B

theorem eval_subD (A B : List ℕ) (hl : A.length = B.length) (t : ℚ) :
    eval (subD A B) t = evalQ A t - evalQ B t := by
  induction A generalizing B with
  | nil => cases B with
    | nil => simp [subD, evalQ]
    | cons _ _ => simp at hl
  | cons a A ih => cases B with
    | nil => simp at hl
    | cons b B =>
      simp only [subD, List.zipWith_cons_cons, eval_cons, evalQ] at ih ⊢
      rw [ih B (by simpa using hl)]; push_cast; ring

theorem subD_parts (q : IPoly) : subD (posPart q) (negPart q) = q := by
  induction q with
  | nil => rfl
  | cons c q ih =>
    simp only [subD, posPart, negPart, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih, Int.toNat_sub_toNat_neg]

/-- Signed unpacking: `A − B` from `A(X)` and `B(X)`, once both coefficient sums are below `X`. -/
theorem eval_subD_unpack {X L : ℕ} {A B : List ℕ} (hA : pack 1 A < X) (hB : pack 1 B < X)
    (hAL : A.length ≤ L) (hBL : B.length ≤ L) (y : ℚ) :
    eval (subD (unpack X L (pack X A)) (unpack X L (pack X B))) y = evalQ A y - evalQ B y := by
  rw [eval_subD _ _ (by simp), evalQ_unpack_pack A hA hAL, evalQ_unpack_pack B hB hBL]

/-- Signed `unpack_pack`: an integer polynomial is recovered from its two packed parts. -/
theorem subD_unpack_pack {X : ℕ} (q : IPoly) (hp : pack 1 (posPart q) < X)
    (hn : pack 1 (negPart q) < X) :
    subD (unpack X q.length (pack X (posPart q))) (unpack X q.length (pack X (negPart q))) = q := by
  rw [unpack_pack_of_one_lt _ hp (by simp), unpack_pack_of_one_lt _ hn (by simp)]
  simp only [length_posPart, length_negPart, Nat.sub_self, List.replicate_zero, List.append_nil]
  exact subD_parts q

/-- The test `tm1` of `t ↦ 2^{e(n−1)} p((k + t)/2^e)`, `n = p.length`, i.e. positivity of `p` on
`[k/2^e, (k+1)/2^e]`, by Kronecker substitution: the shifted coefficients of each part are the
base-`X` digits of one packed value (`Kronecker.unpack_shift`). -/
def tm1K (p : IPoly) (k e : ℕ) : Bool :=
  let Rp := scaleN e (posPart p)
  let Rm := scaleN e (negPart p)
  let X := max (pack (k + 1) Rp) (pack (k + 1) Rm) + 1
  tm1 (subD (unpack X p.length (pack (k + X) Rp)) (unpack X p.length (pack (k + X) Rm)))

theorem tm1K_sound (p : IPoly) (k e : ℕ) (hc : tm1K p k e = true) (y : ℚ)
    (hy0 : (k:ℚ) / 2 ^ e ≤ y) (hy1 : y ≤ ((k:ℚ) + 1) / 2 ^ e) : 0 < eval p y := by
  have h2 : (0:ℚ) < 2 ^ e := by positivity
  set t := y * 2 ^ e - k with ht
  have ht0 : 0 ≤ t := by rw [div_le_iff₀ h2] at hy0; linarith
  have ht1 : t ≤ 1 := by rw [le_div_iff₀ h2] at hy1; linarith
  simp only [tm1K] at hc
  set Rp := scaleN e (posPart p) with hRp
  set Rm := scaleN e (negPart p) with hRm
  set X := max (pack (k + 1) Rp) (pack (k + 1) Rm) + 1 with hX
  have hQ := tm1_sound _ hc t ht0 ht1
  rw [eval_subD _ _ (by simp),
    evalQ_unpack_shift Rp k p.length X (by simp [hRp]) (by omega) t,
    evalQ_unpack_shift Rm k p.length X (by simp [hRm]) (by omega) t,
    hRp, hRm, evalQ_scaleN, evalQ_scaleN, length_posPart, length_negPart] at hQ
  have hy : ((k:ℕ):ℚ) + t = y * 2 ^ e := by rw [ht]; ring
  rw [hy, mul_div_cancel_right₀ _ h2.ne', ← mul_sub, ← eval_eq_parts] at hQ
  exact pos_of_mul_pos_right hQ (by positivity)

/-- Positivity on `[k₀/2^{e₀}, 1]` over contiguous dyadic intervals `(k, e)`. -/
def posOn (p : IPoly) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | k₀, e₀, [] => decide (k₀ = 2 ^ e₀)
  | k₀, e₀, (k, e) :: rest =>
      decide (k₀ * 2 ^ e = k * 2 ^ e₀) && tm1K p k e && posOn p (k + 1) e rest

theorem posOn_sound (p : IPoly) : ∀ (k₀ e₀ : ℕ) (l : List (ℕ × ℕ)), posOn p k₀ e₀ l = true →
    ∀ y : ℚ, (k₀:ℚ) / 2 ^ e₀ ≤ y → y ≤ 1 → l ≠ [] → 0 < eval p y := by
  intro k₀ e₀ l
  induction l generalizing k₀ e₀ with
  | nil => intro _ y _ _ h; exact absurd rfl h
  | cons ke rest ih =>
    obtain ⟨k, e⟩ := ke
    intro hc y hy0 hy1 _
    simp only [posOn, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hk, htm⟩, hrest⟩ := hc
    have h2 : (0:ℚ) < 2 ^ e := by positivity
    have h20 : (0:ℚ) < 2 ^ e₀ := by positivity
    have hstart : (k₀:ℚ) / 2 ^ e₀ = (k:ℚ) / 2 ^ e := by
      rw [div_eq_div_iff h20.ne' h2.ne']; exact_mod_cast hk
    rw [hstart] at hy0
    cases rest with
    | nil =>
      simp only [posOn, decide_eq_true_eq] at hrest
      have h1 : ((k:ℚ) + 1) / 2 ^ e = 1 := by
        rw [div_eq_one_iff_eq h2.ne']; exact_mod_cast hrest
      exact tm1K_sound p k e htm y hy0 (by rw [h1]; exact hy1)
    | cons ke' rest' =>
      rcases le_total y (((k:ℚ) + 1) / 2 ^ e) with hy | hy
      · exact tm1K_sound p k e htm y hy0 hy
      · exact ih (k + 1) e hrest y (by push_cast; exact hy) hy1 (by simp)

/-! ## From rational polynomials -/

/-- `D · p` with integer coefficients (valid when `isIntMul p D`). -/
def ofPoly (p : Poly) (D : ℕ) : IPoly := p.map (fun c : ℚ => (c * (D:ℚ)).num)
def isIntMul (p : Poly) (D : ℕ) : Bool := p.all (fun c : ℚ => (c * (D:ℚ)).den == 1)

theorem eval_ofPoly (p : Poly) (D : ℕ) (h : isIntMul p D = true) (x : ℚ) :
    eval (ofPoly p D) x = D * Poly.eval p x := by
  induction p with
  | nil => simp [ofPoly]
  | cons c cs ih =>
    simp only [isIntMul, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, hcs⟩ := h
    simp only [ofPoly, List.map_cons, eval_cons, Poly.eval_cons] at ih ⊢
    rw [ih hcs, Rat.coe_int_num_of_den_eq_one hc]
    ring

/-- A common denominator. -/
def lcmDen (p : Poly) : ℕ := p.foldr (fun (c : ℚ) acc => Nat.lcm c.den acc) 1

end IPoly

end QRH.RepeatedMarks.Faceless
