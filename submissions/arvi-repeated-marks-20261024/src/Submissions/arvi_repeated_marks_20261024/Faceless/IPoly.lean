import Submissions.arvi_repeated_marks_20261024.Faceless.Poly

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

def mul : IPoly → IPoly → IPoly
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- The coefficients of `t ↦ p (k + t)`. -/
def shift (p : IPoly) (k : ℤ) : IPoly := p.foldr (fun c acc => add [c] (mul [k, 1] acc)) []

/-- `x ↦ 2^{e n} p(x / 2^e)` with `n + 1 = length p` (coefficient `i` times `2^{e(n-i)}`). -/
def scale (e : ℕ) : IPoly → IPoly
  | [] => []
  | c :: cs => (c * ((2 ^ (e * cs.length) : ℕ) : ℤ)) :: scale e cs

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

@[simp] theorem eval_mul (p q : IPoly) (x : ℚ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

@[simp] theorem eval_shift (p : IPoly) (k : ℤ) (t : ℚ) : eval (shift p k) t = eval p (k + t) := by
  induction p with
  | nil => simp [shift]
  | cons c p ih =>
    have : shift (c :: p) k = add [c] (mul [k, 1] (shift p k)) := rfl
    rw [this, eval_add, eval_mul, ih]
    simp

theorem eval_scale (e : ℕ) (p : IPoly) (x : ℚ) :
    eval (scale e p) x = 2 ^ (e * (p.length - 1)) * eval p (x / 2 ^ e) := by
  have h2 : (2:ℚ) ^ e ≠ 0 := by positivity
  induction p with
  | nil => simp [scale]
  | cons c cs ih =>
    simp only [scale, eval_cons, ih, List.length_cons, Nat.add_sub_cancel]
    push_cast
    rcases cs with _ | ⟨d, ds⟩
    · simp
    · simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show e * (ds.length + 1) = e * ds.length + e by ring, pow_add]
      field_simp

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

/-- The test on the dyadic interval `[k/2^e, (k+1)/2^e]`. -/
def tm1On (p : IPoly) (k e : ℕ) : Bool := tm1 (shift (scale e p) k)

theorem tm1On_sound (p : IPoly) (k e : ℕ) (hc : tm1On p k e = true) (y : ℚ)
    (hy0 : (k:ℚ) / 2 ^ e ≤ y) (hy1 : y ≤ ((k:ℚ) + 1) / 2 ^ e) : 0 < eval p y := by
  have h2 : (0:ℚ) < 2 ^ e := by positivity
  set t := y * 2 ^ e - k with ht
  have ht0 : 0 ≤ t := by rw [div_le_iff₀ h2] at hy0; linarith
  have ht1 : t ≤ 1 := by rw [le_div_iff₀ h2] at hy1; linarith
  have hQ := tm1_sound _ hc t ht0 ht1
  rw [eval_shift, eval_scale] at hQ
  have hy : ((k:ℤ):ℚ) + t = y * 2 ^ e := by rw [ht]; push_cast; ring
  rw [hy, mul_div_cancel_right₀ _ h2.ne'] at hQ
  exact pos_of_mul_pos_right hQ (by positivity)

/-! ## The Kronecker test: one shift is a few big-number operations

The coefficients of `t ↦ 2^{e n} p((k + t)/2^e)` are read off as base-`X` digits of one Horner value,
separately for the positive and negative parts of `p`; `X` exceeds the coefficient sums, so no digit
carries. -/

namespace NP

def evalN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, x => c + x * evalN cs x

def evalQ : List ℕ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => (c : ℚ) + x * evalQ cs x

def addN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addN p q

def smulN (c : ℕ) (p : List ℕ) : List ℕ := p.map (c * ·)

def mulN : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => addN (smulN a (b :: q)) (0 :: mulN p (b :: q))

/-- The Taylor shift (used in proofs only). -/
def shiftN (p : List ℕ) (k : ℕ) : List ℕ := p.foldr (fun c acc => addN [c] (mulN [k, 1] acc)) []

def scaleN (e : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => (c * 2 ^ (e * cs.length)) :: scaleN e cs

/-- `n` base-`X` digits of `V`. -/
def digits (X : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, V => V % X :: digits X n (V / X)

theorem evalN_addN (p q : List ℕ) (x : ℕ) : evalN (addN p q) x = evalN p x + evalN q x := by
  induction p generalizing q with
  | nil => simp [addN, evalN]
  | cons a p ih => cases q with
    | nil => simp [addN, evalN]
    | cons b q => simp [addN, evalN, ih]; ring

theorem evalN_smulN (c : ℕ) (p : List ℕ) (x : ℕ) : evalN (smulN c p) x = c * evalN p x := by
  induction p with
  | nil => simp [smulN, evalN]
  | cons a p ih => simp only [smulN, List.map_cons, evalN] at ih ⊢; rw [ih]; ring

theorem evalN_mulN (p q : List ℕ) (x : ℕ) : evalN (mulN p q) x = evalN p x * evalN q x := by
  induction p with
  | nil => simp [mulN, evalN]
  | cons a p ih =>
    cases q with
    | nil => simp [mulN, evalN]
    | cons b q => simp only [mulN] at ih ⊢; simp [evalN, evalN_addN, evalN_smulN, ih]; ring

theorem evalN_shiftN (p : List ℕ) (k x : ℕ) : evalN (shiftN p k) x = evalN p (k + x) := by
  induction p with
  | nil => simp [shiftN, evalN]
  | cons c p ih =>
    have : shiftN (c :: p) k = addN [c] (mulN [k, 1] (shiftN p k)) := rfl
    rw [this, evalN_addN, evalN_mulN, ih]; simp [evalN]

theorem evalQ_addN (p q : List ℕ) (x : ℚ) : evalQ (addN p q) x = evalQ p x + evalQ q x := by
  induction p generalizing q with
  | nil => simp [addN, evalQ]
  | cons a p ih => cases q with
    | nil => simp [addN, evalQ]
    | cons b q => simp [addN, evalQ, ih]; ring

theorem evalQ_smulN (c : ℕ) (p : List ℕ) (x : ℚ) : evalQ (smulN c p) x = c * evalQ p x := by
  induction p with
  | nil => simp [smulN, evalQ]
  | cons a p ih => simp only [smulN, List.map_cons, evalQ] at ih ⊢; rw [ih]; push_cast; ring

theorem evalQ_mulN (p q : List ℕ) (x : ℚ) : evalQ (mulN p q) x = evalQ p x * evalQ q x := by
  induction p with
  | nil => simp [mulN, evalQ]
  | cons a p ih =>
    cases q with
    | nil => simp [mulN, evalQ]
    | cons b q => simp only [mulN] at ih ⊢; simp [evalQ, evalQ_addN, evalQ_smulN, ih]; ring

theorem evalQ_shiftN (p : List ℕ) (k : ℕ) (t : ℚ) : evalQ (shiftN p k) t = evalQ p (k + t) := by
  induction p with
  | nil => simp [shiftN, evalQ]
  | cons c p ih =>
    have : shiftN (c :: p) k = addN [c] (mulN [k, 1] (shiftN p k)) := rfl
    rw [this, evalQ_addN, evalQ_mulN, ih]; simp [evalQ]

theorem evalQ_scaleN (e : ℕ) (p : List ℕ) (x : ℚ) :
    evalQ (scaleN e p) x = 2 ^ (e * (p.length - 1)) * evalQ p (x / 2 ^ e) := by
  have h2 : (2:ℚ) ^ e ≠ 0 := by positivity
  induction p with
  | nil => simp [scaleN, evalQ]
  | cons c cs ih =>
    simp only [scaleN, evalQ, ih, List.length_cons, Nat.add_sub_cancel]
    push_cast
    rcases cs with _ | ⟨d, ds⟩
    · simp [evalQ]
    · simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show e * (ds.length + 1) = e * ds.length + e by ring, pow_add]
      field_simp

theorem length_addN (p q : List ℕ) : (addN p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [addN]
  | cons a p ih => cases q with
    | nil => simp [addN]
    | cons b q => simp [addN, ih, Nat.succ_max_succ]

theorem length_smulN (c : ℕ) (p : List ℕ) : (smulN c p).length = p.length := by simp [smulN]

theorem length_mulN_le (p q : List ℕ) : (mulN p q).length ≤ p.length + q.length - 1 := by
  induction p with
  | nil => simp [mulN]
  | cons a p ih =>
    cases q with
    | nil => simp [mulN]
    | cons b q =>
      simp only [mulN, length_addN, length_smulN, List.length_cons] at ih ⊢
      omega

theorem length_shiftN (p : List ℕ) (k : ℕ) : (shiftN p k).length ≤ p.length := by
  induction p with
  | nil => simp [shiftN]
  | cons c p ih =>
    have : shiftN (c :: p) k = addN [c] (mulN [k, 1] (shiftN p k)) := rfl
    rw [this, length_addN]
    have := length_mulN_le [k, 1] (shiftN p k)
    simp only [List.length_cons, List.length_nil] at this ⊢
    omega

theorem le_evalN_one (L : List ℕ) : ∀ c ∈ L, c ≤ evalN L 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp [evalN]
    · have := ih c hc; simp [evalN]; omega

/-- Digits of `evalN L X` when every entry is below `X`; trailing zeros pad up to `n`. -/
theorem digits_evalN (X : ℕ) (hX : 0 < X) (L : List ℕ) (hL : ∀ c ∈ L, c < X) (n : ℕ)
    (hn : L.length ≤ n) : ∀ i < n, (digits X n (evalN L X)).getD i 0 = L.getD i 0 := by
  induction n generalizing L with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    cases L with
    | nil =>
      have h0 : ∀ m V, V = 0 → ∀ j, (digits X m V).getD j 0 = 0 := by
        intro m
        induction m with
        | zero => intro V _ j; simp [digits]
        | succ m ihm =>
          intro V hV j; subst hV
          cases j with
          | zero => simp [digits]
          | succ j => simpa [digits] using ihm 0 rfl j
      simp only [evalN]; rw [h0 _ 0 rfl]; simp
    | cons a L =>
      have ha : a < X := hL a (by simp)
      have hmod : evalN (a :: L) X % X = a := by
        simp only [evalN]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      have hdiv : evalN (a :: L) X / X = evalN L X := by
        simp only [evalN]; rw [Nat.add_mul_div_left _ _ hX, Nat.div_eq_of_lt ha, zero_add]
      cases i with
      | zero => simp [digits, hmod]
      | succ i =>
        simp only [digits, List.getD_cons_succ, hdiv]
        exact ih L (fun c hc => hL c (by simp [hc])) (by simp at hn; omega) i (by omega)

end NP

/-- The test of `tm1On` by Kronecker substitution. -/
def tm1K (p : IPoly) (k e : ℕ) : Bool :=
  let Rp := NP.scaleN e (p.map Int.toNat)
  let Rm := NP.scaleN e (p.map fun c => (-c).toNat)
  let X := max (NP.evalN Rp (k + 1)) (NP.evalN Rm (k + 1)) + 1
  let dp := NP.digits X p.length (NP.evalN Rp (k + X))
  let dm := NP.digits X p.length (NP.evalN Rm (k + X))
  tm1 (List.zipWith (fun (a b : ℕ) => (a:ℤ) - (b:ℤ)) dp dm)

theorem eval_eq_parts (p : IPoly) (x : ℚ) :
    eval p x = NP.evalQ (p.map Int.toNat) x - NP.evalQ (p.map fun c => (-c).toNat) x := by
  induction p with
  | nil => simp [NP.evalQ]
  | cons c p ih =>
    simp only [eval_cons, List.map_cons, NP.evalQ, ih]
    have h := Int.toNat_sub_toNat_neg c
    have : (c : ℚ) = ((c.toNat : ℕ) : ℚ) - (((-c).toNat : ℕ) : ℚ) := by exact_mod_cast h.symm
    rw [this]; ring

theorem eval_zipWith_sub (A B : List ℕ) (hl : A.length = B.length) (t : ℚ) :
    eval (List.zipWith (fun (a b : ℕ) => (a:ℤ) - (b:ℤ)) A B) t = NP.evalQ A t - NP.evalQ B t := by
  induction A generalizing B with
  | nil => cases B with
    | nil => simp [NP.evalQ]
    | cons _ _ => simp at hl
  | cons a A ih => cases B with
    | nil => simp at hl
    | cons b B =>
      simp only [List.zipWith_cons_cons, eval_cons, NP.evalQ]
      rw [ih B (by simpa using hl)]; push_cast; ring

/-- The digits recovered by `tm1K` are the shifted coefficients. -/
theorem digits_shift (R : List ℕ) (k n : ℕ) (hn : R.length ≤ n) (X : ℕ)
    (hX : NP.evalN R (k + 1) < X) :
    ∀ i < n, (NP.digits X n (NP.evalN R (k + X))).getD i 0 = (NP.shiftN R k).getD i 0 := by
  have hX0 : 0 < X := lt_of_le_of_lt (Nat.zero_le _) hX
  rw [← NP.evalN_shiftN]
  apply NP.digits_evalN X hX0
  · intro c hc
    have := NP.le_evalN_one _ c hc
    rw [NP.evalN_shiftN] at this
    omega
  · exact (NP.length_shiftN R k).trans hn

theorem list_eq_of_getD {A B : List ℕ} (n : ℕ) (hA : A.length = n) (hB : B.length ≤ n)
    (h : ∀ i < n, A.getD i 0 = B.getD i 0) (t : ℚ) : NP.evalQ A t = NP.evalQ B t := by
  induction n generalizing A B with
  | zero =>
    have : A = [] := List.length_eq_zero_iff.mp hA
    have : B = [] := List.length_eq_zero_iff.mp (by omega)
    subst_vars; rfl
  | succ n ih =>
    cases A with
    | nil => simp at hA
    | cons a A =>
      cases B with
      | nil =>
        have h0 : ∀ i < n + 1, (a :: A).getD i 0 = 0 := fun i hi => by simpa using h i hi
        have hz : ∀ i < n, A.getD i 0 = ([] : List ℕ).getD i 0 := by
          intro i hi; simpa using h0 (i + 1) (by omega)
        have := ih (B := []) (by simpa using hA) (by simp) hz
        have ha : a = 0 := by simpa using h0 0 (by omega)
        simp [NP.evalQ, this, ha]
      | cons b B =>
        have hab : a = b := by simpa using h 0 (by omega)
        have := ih (A := A) (B := B) (by simpa using hA) (by simp at hB; omega)
          (fun i hi => by simpa using h (i + 1) (by omega))
        simp [NP.evalQ, this, hab]

theorem tm1K_sound (p : IPoly) (k e : ℕ) (hc : tm1K p k e = true) (y : ℚ)
    (hy0 : (k:ℚ) / 2 ^ e ≤ y) (hy1 : y ≤ ((k:ℚ) + 1) / 2 ^ e) : 0 < eval p y := by
  have h2 : (0:ℚ) < 2 ^ e := by positivity
  set t := y * 2 ^ e - k with ht
  have ht0 : 0 ≤ t := by rw [div_le_iff₀ h2] at hy0; linarith
  have ht1 : t ≤ 1 := by rw [le_div_iff₀ h2] at hy1; linarith
  simp only [tm1K] at hc
  set Rp := NP.scaleN e (p.map Int.toNat) with hRp
  set Rm := NP.scaleN e (p.map fun c => (-c).toNat) with hRm
  set X := max (NP.evalN Rp (k + 1)) (NP.evalN Rm (k + 1)) + 1 with hX
  have hlp : Rp.length = p.length := by
    have : ∀ (e : ℕ) (L : List ℕ), (NP.scaleN e L).length = L.length := by
      intro e L; induction L with
      | nil => rfl
      | cons a L ih => simp [NP.scaleN, ih]
    rw [hRp, this]; simp
  have hlm : Rm.length = p.length := by
    have : ∀ (e : ℕ) (L : List ℕ), (NP.scaleN e L).length = L.length := by
      intro e L; induction L with
      | nil => rfl
      | cons a L ih => simp [NP.scaleN, ih]
    rw [hRm, this]; simp
  have hdl : ∀ (V : ℕ), (NP.digits X p.length V).length = p.length := by
    intro V
    have : ∀ n V, (NP.digits X n V).length = n := by
      intro n; induction n with
      | zero => intro V; rfl
      | succ n ih => intro V; simp [NP.digits, ih]
    exact this _ V
  have hQ := tm1_sound _ hc t ht0 ht1
  rw [eval_zipWith_sub _ _ (by rw [hdl, hdl])] at hQ
  rw [list_eq_of_getD p.length (hdl _) ((NP.length_shiftN Rp k).trans hlp.le)
      (digits_shift Rp k p.length hlp.le X (by omega)) t,
    list_eq_of_getD p.length (hdl _) ((NP.length_shiftN Rm k).trans hlm.le)
      (digits_shift Rm k p.length hlm.le X (by omega)) t] at hQ
  rw [NP.evalQ_shiftN, NP.evalQ_shiftN, hRp, hRm, NP.evalQ_scaleN, NP.evalQ_scaleN] at hQ
  have hy : ((k:ℕ):ℚ) + t = y * 2 ^ e := by rw [ht]; ring
  rw [hy, mul_div_cancel_right₀ _ h2.ne'] at hQ
  simp only [List.length_map] at hQ
  rw [← mul_sub, ← eval_eq_parts] at hQ
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
