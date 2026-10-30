import Mathlib.Tactic

/-!
# Bivariate rational polynomials, real evaluation, and a reflective Bernstein box test

`Q1` is a polynomial in `p` (rational coefficients, lowest degree first) and `Q2` a polynomial in
`δ` whose coefficients are `Q1`s. All operations are computable, so the kernel evaluates them
(`decide +kernel`), and `ev` (evaluation at real `δ, p`) commutes with every operation.

The box test does not trust any Bernstein theory. `bernCheck P a b c e` computes, inside the kernel,
a candidate certificate `P = m + Σ g_ij (δ-a)^i (b-δ)^(n-i) (p-c)^j (e-p)^(m-j)` (the tensor
Bernstein coefficients of `P` on `[a,b] × [c,e]`, shifted by their minimum `m`) and then *checks*
the polynomial identity, `m > 0` and `g_ij ≥ 0` (`checkCert`). Only `checkCert_sound` is proved.
`posBox` adds dyadic subdivision (with fuel); the kernel computes the subdivision itself.
-/

set_option autoImplicit false

namespace QRH.ArviReturnTuning

/-- A polynomial in `p` with rational coefficients, lowest degree first. -/
abbrev Q1 := List ℚ

namespace Q1

def add : Q1 → Q1 → Q1
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: add p q

def smul (c : ℚ) (p : Q1) : Q1 := p.map (c * ·)

def mul : Q1 → Q1 → Q1
  | [], _ => []
  | a :: p, q => add (smul a q) (0 :: mul p q)

/-- Evaluation at a real point. -/
def ev : Q1 → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * ev cs x

@[simp] theorem ev_nil (x : ℝ) : ev [] x = 0 := rfl
@[simp] theorem ev_cons (c : ℚ) (cs : Q1) (x : ℝ) : ev (c :: cs) x = (c : ℝ) + x * ev cs x := rfl

theorem ev_add (p q : Q1) (x : ℝ) : ev (add p q) x = ev p x + ev q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp only [add, ev_cons, ih]; push_cast; ring

theorem ev_smul (c : ℚ) (p : Q1) (x : ℝ) : ev (smul c p) x = (c : ℝ) * ev p x := by
  induction p with
  | nil => simp [smul]
  | cons a p ih =>
    simp only [smul, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem ev_mul (p q : Q1) (x : ℝ) : ev (mul p q) x = ev p x * ev q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    simp only [mul, ev_add, ev_smul, ev_cons, ih]
    push_cast; ring

/-- Every coefficient is zero. -/
def isZero (p : Q1) : Bool := p.all (· == 0)

theorem ev_of_isZero (p : Q1) (h : isZero p = true) (x : ℝ) : ev p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [ev_cons, ih h.2, h.1]; simp

/-- `t ↦ q (c + s t)`. -/
def subst (q : Q1) (c s : ℚ) : Q1 := q.foldr (fun k acc => add [k] (mul [c, s] acc)) []

end Q1

/-- A polynomial in `δ` whose coefficients are polynomials in `p`. -/
abbrev Q2 := List Q1

namespace Q2

def add : Q2 → Q2 → Q2
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => Q1.add a b :: add p q

def smul (c : ℚ) (P : Q2) : Q2 := P.map (Q1.smul c)

/-- Multiplication by a polynomial in `p` alone. -/
def mulQ1 (a : Q1) (P : Q2) : Q2 := P.map (Q1.mul a)

def mul : Q2 → Q2 → Q2
  | [], _ => []
  | a :: p, q => add (mulQ1 a q) ([] :: mul p q)

def sub (P Q : Q2) : Q2 := add P (smul (-1) Q)

def pow (P : Q2) : ℕ → Q2
  | 0 => [[1]]
  | n + 1 => mul P (pow P n)

/-- The constant `c`. -/
def C (c : ℚ) : Q2 := [[c]]
/-- The variable `δ`. -/
def X : Q2 := [[], [1]]
/-- The variable `p`. -/
def Y : Q2 := [[0, 1]]

/-- Evaluation at real `δ, p`. -/
def ev : Q2 → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | c :: cs, d, p => Q1.ev c p + d * ev cs d p

@[simp] theorem ev_nil (d p : ℝ) : ev [] d p = 0 := rfl
@[simp] theorem ev_cons (c : Q1) (cs : Q2) (d p : ℝ) : ev (c :: cs) d p = Q1.ev c p + d * ev cs d p :=
  rfl

theorem ev_add (P Q : Q2) (d p : ℝ) : ev (add P Q) d p = ev P d p + ev Q d p := by
  induction P generalizing Q with
  | nil => simp [add]
  | cons a P ih =>
    cases Q with
    | nil => simp [add]
    | cons b Q => simp only [add, ev_cons, Q1.ev_add, ih]; ring

theorem ev_smul (c : ℚ) (P : Q2) (d p : ℝ) : ev (smul c P) d p = (c : ℝ) * ev P d p := by
  induction P with
  | nil => simp [smul]
  | cons a P ih =>
    simp only [smul, List.map_cons, ev_cons, Q1.ev_smul] at ih ⊢
    rw [ih]; ring

theorem ev_mulQ1 (a : Q1) (P : Q2) (d p : ℝ) : ev (mulQ1 a P) d p = Q1.ev a p * ev P d p := by
  induction P with
  | nil => simp [mulQ1]
  | cons b P ih =>
    simp only [mulQ1, List.map_cons, ev_cons, Q1.ev_mul] at ih ⊢
    rw [ih]; ring

theorem ev_mul (P Q : Q2) (d p : ℝ) : ev (mul P Q) d p = ev P d p * ev Q d p := by
  induction P with
  | nil => simp [mul]
  | cons a P ih =>
    simp only [mul, ev_add, ev_mulQ1, ev_cons, Q1.ev_nil, ih]
    ring

theorem ev_sub (P Q : Q2) (d p : ℝ) : ev (sub P Q) d p = ev P d p - ev Q d p := by
  simp only [sub, ev_add, ev_smul]; push_cast; ring

theorem ev_pow (P : Q2) (n : ℕ) (d p : ℝ) : ev (pow P n) d p = ev P d p ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow, ev_mul, ih]; ring

@[simp] theorem ev_C (c : ℚ) (d p : ℝ) : ev (C c) d p = (c : ℝ) := by simp [C]
@[simp] theorem ev_X (d p : ℝ) : ev X d p = d := by simp [X]
@[simp] theorem ev_Y (d p : ℝ) : ev Y d p = p := by simp [Y]

/-- Every coefficient is zero. -/
def isZero (P : Q2) : Bool := P.all Q1.isZero

theorem ev_of_isZero (P : Q2) (h : isZero P = true) (d p : ℝ) : ev P d p = 0 := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    simp only [isZero, List.all_cons, Bool.and_eq_true] at h
    rw [ev_cons, ih h.2, Q1.ev_of_isZero a h.1]; ring

/-- The coefficient of `δ^i p^j`. -/
def coef (P : Q2) (i j : ℕ) : ℚ := (P.getD i []).getD j 0

/-- `P (a + s u, c + t w)` as a polynomial in `(u, w)`. -/
def subst (P : Q2) (a s c t : ℚ) : Q2 :=
  P.foldr (fun Pi acc => add [Q1.subst Pi c t] (mul [[a], [s]] acc)) []

end Q2

/-! ### The certificate identity and its soundness -/

namespace Q1

def pow (p : Q1) : ℕ → Q1
  | 0 => [1]
  | n + 1 => mul p (pow p n)

theorem ev_pow (p : Q1) (n : ℕ) (x : ℝ) : ev (pow p n) x = ev p x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow, ev_mul, ih]; ring

end Q1

/-- The univariate Bernstein factor `(x - a)^i (b - x)^(n - i)`. -/
def bpoly (a b : ℚ) (n i : ℕ) : Q1 := Q1.mul (Q1.pow [-a, 1] i) (Q1.pow [b, -1] (n - i))

theorem ev_bpoly (a b : ℚ) (n i : ℕ) (x : ℝ) :
    Q1.ev (bpoly a b n i) x = (x - a) ^ i * (b - x) ^ (n - i) := by
  simp only [bpoly, Q1.ev_mul, Q1.ev_pow, Q1.ev_cons, Q1.ev_nil]
  push_cast; ring

theorem ev_bpoly_nonneg (a b : ℚ) (n i : ℕ) {x : ℝ} (h0 : (a : ℝ) ≤ x) (h1 : x ≤ b) :
    0 ≤ Q1.ev (bpoly a b n i) x := by
  rw [ev_bpoly]
  have h2 : 0 ≤ x - a := by linarith
  have h3 : 0 ≤ (b : ℝ) - x := by linarith
  positivity

/-- `u(δ) · v(p)` as a `Q2`. -/
def outer (u v : Q1) : Q2 := u.map (fun k => Q1.smul k v)

theorem ev_outer (u v : Q1) (d p : ℝ) : Q2.ev (outer u v) d p = Q1.ev u d * Q1.ev v p := by
  induction u with
  | nil => simp [outer]
  | cons k u ih =>
    simp only [outer, List.map_cons, Q2.ev_cons, Q1.ev_cons, Q1.ev_smul] at ih ⊢
    rw [ih]; ring

/-- `Σ_J g_J (p-c)^J (e-p)^(m-J)` over a list of `(g_J, J)`. -/
def innerSum (c e : ℚ) (m : ℕ) : List (ℚ × ℕ) → Q1
  | [] => []
  | (g, j) :: l => Q1.add (Q1.smul g (bpoly c e m j)) (innerSum c e m l)

theorem innerSum_nonneg (c e : ℚ) (m : ℕ) (l : List (ℚ × ℕ))
    (hl : l.all (fun t => decide (0 ≤ t.1)) = true) {p : ℝ} (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ e) :
    0 ≤ Q1.ev (innerSum c e m l) p := by
  induction l with
  | nil => simp [innerSum]
  | cons t l ih =>
    obtain ⟨g, j⟩ := t
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [innerSum, Q1.ev_add, Q1.ev_smul]
    have hg : (0 : ℝ) ≤ g := by exact_mod_cast hl.1
    exact add_nonneg (mul_nonneg hg (ev_bpoly_nonneg c e m j hp0 hp1)) (ih hl.2)

/-- The coefficients are nonnegative. -/
def certNonneg (l : List (ℕ × List (ℚ × ℕ))) : Bool :=
  l.all fun r => r.2.all fun t => decide (0 ≤ t.1)

/-- `Σ_I (δ-a)^I (b-δ)^(n-I) · innerSum_I(p)`. -/
def certSum (a b c e : ℚ) (n m : ℕ) : List (ℕ × List (ℚ × ℕ)) → Q2
  | [] => []
  | (i, r) :: l => Q2.add (outer (bpoly a b n i) (innerSum c e m r)) (certSum a b c e n m l)

theorem certSum_nonneg (a b c e : ℚ) (n m : ℕ) (l : List (ℕ × List (ℚ × ℕ)))
    (hl : certNonneg l = true) {d p : ℝ} (hd0 : (a : ℝ) ≤ d) (hd1 : d ≤ b)
    (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ e) : 0 ≤ Q2.ev (certSum a b c e n m l) d p := by
  induction l with
  | nil => simp [certSum]
  | cons t l ih =>
    obtain ⟨i, r⟩ := t
    simp only [certNonneg, List.all_cons, Bool.and_eq_true] at hl
    simp only [certSum, Q2.ev_add, ev_outer]
    exact add_nonneg (mul_nonneg (ev_bpoly_nonneg a b n i hd0 hd1)
      (innerSum_nonneg c e m r hl.1 hp0 hp1)) (ih hl.2)

/-- The certificate check: `m > 0`, every coefficient `≥ 0`, and `P - (m + Σ ...) = 0` coefficientwise. -/
def checkCert (P : Q2) (a b c e : ℚ) (n m : ℕ) (mn : ℚ) (l : List (ℕ × List (ℚ × ℕ))) : Bool :=
  decide (0 < mn) && certNonneg l &&
    Q2.isZero (Q2.sub P (Q2.add (Q2.C mn) (certSum a b c e n m l)))

theorem checkCert_sound (P : Q2) (a b c e : ℚ) (n m : ℕ) (mn : ℚ) (l : List (ℕ × List (ℚ × ℕ)))
    (h : checkCert P a b c e n m mn l = true) {d p : ℝ} (hd0 : (a : ℝ) ≤ d) (hd1 : d ≤ b)
    (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ e) : 0 < Q2.ev P d p := by
  simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hm, hl⟩, hz⟩ := h
  have h0 := Q2.ev_of_isZero _ hz d p
  rw [Q2.ev_sub, Q2.ev_add, Q2.ev_C] at h0
  have hs := certSum_nonneg a b c e n m l hl hd0 hd1 hp0 hp1
  have hm' : (0 : ℝ) < mn := by exact_mod_cast hm
  linarith

/-! ### Computing the candidate certificate (not trusted) -/

/-- Degrees used for the Bernstein form: the lengths of the coefficient lists. -/
def degD (P : Q2) : ℕ := P.length - 1
def degP (P : Q2) : ℕ := (P.foldr (fun r acc => max r.length acc) 0) - 1

/-- Adjacent sums `[a₀+a₁, a₁+a₂, …]`. -/
def adjSum : List ℚ → List ℚ
  | a :: b :: l => (a + b) :: adjSum (b :: l)
  | _ => []

/-- The binomial transform `β_I = Σ_{i ≤ I} C(I,i) c_i`, `I < k`, by repeated adjacent sums. -/
def binomT : ℕ → List ℚ → List ℚ
  | 0, _ => []
  | k + 1, l => l.headD 0 :: binomT k (adjSum l)

/-- `[c_i / C(n,i)]_{i ≤ n}` (missing coefficients are zero). -/
def scaleBinom (n : ℕ) (c : List ℚ) : List ℚ :=
  (List.range (n + 1)).map fun i => c.getD i 0 / (n.choose i : ℚ)

/-- Univariate Bernstein coefficients of degree `n` from monomial coefficients on `[0,1]`. -/
def bern1 (n : ℕ) (c : List ℚ) : List ℚ := binomT (n + 1) (scaleBinom n c)

/-- Transpose of a list of rows (rows padded with zeros to length `m + 1`). -/
def cols (m : ℕ) (rows : List (List ℚ)) : List (List ℚ) :=
  (List.range (m + 1)).map fun j => rows.map fun r => r.getD j 0

/-- The tensor Bernstein coefficients `β_IJ` (rows `I ≤ n`, entries `J ≤ m`) of `q(u, w)` on `[0,1]²`. -/
def bern2 (q : Q2) (n m : ℕ) : List (List ℚ) :=
  let rowsW := (List.range (n + 1)).map fun i => bern1 m (q.getD i [])
  let colsU := (cols m rowsW).map (bern1 n)
  cols n colsU

/-- The candidate certificate `(m, [(I, [(g_IJ, J)])])` of `P` on `[a,b] × [c,e]`. -/
def bernCert (P : Q2) (a b c e : ℚ) : ℚ × List (ℕ × List (ℚ × ℕ)) :=
  let n := degD P
  let m := degP P
  let β := bern2 (Q2.subst P a (b - a) c (e - c)) n m
  let all := β.flatten
  let mn := all.foldr min (all.headD 0)
  let W := (b - a) ^ n * (e - c) ^ m
  (mn, (List.range (n + 1)).map fun I => (I, (List.range (m + 1)).map fun J =>
    (((β.getD I []).getD J 0 - mn) * (n.choose I : ℚ) * (m.choose J : ℚ) / W, J)))

/-- One-box Bernstein test with a kernel-computed certificate. -/
def bernCheck (P : Q2) (a b c e : ℚ) : Bool :=
  match bernCert P a b c e with
  | (mn, l) => checkCert P a b c e (degD P) (degP P) mn l

theorem bernCheck_sound (P : Q2) (a b c e : ℚ) (h : bernCheck P a b c e = true) {d p : ℝ}
    (hd0 : (a : ℝ) ≤ d) (hd1 : d ≤ b) (hp0 : (c : ℝ) ≤ p) (hp1 : p ≤ e) : 0 < Q2.ev P d p := by
  unfold bernCheck at h
  exact checkCert_sound P a b c e _ _ _ _ h hd0 hd1 hp0 hp1

/-! ### Subdivision -/

/-- Split the longer side (in units of the root box `3/4 × 1/2`) at its midpoint, up to `k` times. -/
def posBox (P : Q2) : ℕ → ℚ → ℚ → ℚ → ℚ → Bool
  | 0, a, b, c, e => bernCheck P a b c e
  | k + 1, a, b, c, e =>
    bernCheck P a b c e ||
      (if 3 * (e - c) ≤ 2 * (b - a) then
        posBox P k a ((a + b) / 2) c e && posBox P k ((a + b) / 2) b c e
      else posBox P k a b c ((c + e) / 2) && posBox P k a b ((c + e) / 2) e)

theorem posBox_sound (P : Q2) (k : ℕ) :
    ∀ (a b c e : ℚ), posBox P k a b c e = true → ∀ {d p : ℝ}, (a : ℝ) ≤ d → d ≤ b → (c : ℝ) ≤ p →
      p ≤ e → 0 < Q2.ev P d p := by
  induction k with
  | zero => intro a b c e h d p hd0 hd1 hp0 hp1; exact bernCheck_sound P a b c e h hd0 hd1 hp0 hp1
  | succ k ih =>
    intro a b c e h d p hd0 hd1 hp0 hp1
    simp only [posBox, Bool.or_eq_true] at h
    rcases h with h | h
    · exact bernCheck_sound P a b c e h hd0 hd1 hp0 hp1
    · split_ifs at h with hs
      · simp only [Bool.and_eq_true] at h
        rcases le_total d (((a + b) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hm hp0 hp1
        · exact ih _ _ _ _ h.2 hm hd1 hp0 hp1
      · simp only [Bool.and_eq_true] at h
        rcases le_total p (((c + e) / 2 : ℚ) : ℝ) with hm | hm
        · exact ih _ _ _ _ h.1 hd0 hd1 hp0 hm
        · exact ih _ _ _ _ h.2 hd0 hd1 hm hp1

end QRH.ArviReturnTuning
