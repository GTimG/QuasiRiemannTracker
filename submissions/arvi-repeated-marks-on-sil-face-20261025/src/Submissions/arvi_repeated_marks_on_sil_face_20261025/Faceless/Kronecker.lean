import Mathlib.Tactic

/-!
# Kronecker packing of polynomials with natural coefficients

A polynomial with natural coefficients is its coefficient list `p = [p₀, …, p_{L−1}]`, lowest
degree first. Kronecker substitution packs it into one number,

  `pack X p = p₀ + p₁·X + ⋯ + p_{L−1}·X^{L−1}`,

and `unpack X L V` reads back the `L` lowest base-`X` digits of `V`.

* **Isomorphism.** When every coefficient is below `X`, the two maps are inverse to each other
  (`unpack_pack`, `pack_unpack`). They identify the coefficient lists of length `L` with entries
  below `X` and the numbers below `X^L` (`equiv`).
* **Arithmetic.** `pack X` turns addition, scaling and multiplication of polynomials into the
  same operations on numbers (`pack_addN`, `pack_smulN`, `pack_mulN`). So one big-number product
  replaces a whole polynomial product.
* **No carries.** Every coefficient is at most the coefficient sum `pack 1 p = p(1)`
  (`le_pack_one`). So `p(1) < X` is the condition under which the digits are the coefficients
  (`unpack_pack_of_le`). This is what the certificates check.
* **Change of base.** The Taylor shift `t ↦ p(k + t)` packs at base `Y` to the same number as `p`
  at base `k + Y` (`pack_shiftN`). So the shifted coefficients are the base-`Y` digits of
  `pack (k + Y) p` (`unpack_shift`): a shift costs no polynomial arithmetic at all.

`evalQ` evaluates a coefficient list at a rational point. It gives the lists their meaning in the
certificates.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless.Kronecker

/-! ## Packing and unpacking -/

/-- `p(X)`, by Horner's rule. -/
def pack (X : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + X * pack X cs

/-- The `L` lowest base-`X` digits of `V`, lowest first. -/
def unpack (X : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, V => V % X :: unpack X L (V / X)

@[simp] theorem pack_nil (X : ℕ) : pack X [] = 0 := rfl

@[simp] theorem pack_cons (X c : ℕ) (cs : List ℕ) : pack X (c :: cs) = c + X * pack X cs := rfl

@[simp] theorem length_unpack (X L V : ℕ) : (unpack X L V).length = L := by
  induction L generalizing V with
  | zero => rfl
  | succ L ih => simp [unpack, ih]

/-- Digits are below the base. -/
theorem unpack_lt {X : ℕ} (hX : 0 < X) (L V : ℕ) : ∀ c ∈ unpack X L V, c < X := by
  induction L generalizing V with
  | zero => simp [unpack]
  | succ L ih =>
    intro c hc
    simp only [unpack, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Nat.mod_lt _ hX
    · exact ih _ c hc

/-- A list of digits packs below `X^L`. -/
theorem pack_lt {X : ℕ} (p : List ℕ) (hp : ∀ c ∈ p, c < X) : pack X p < X ^ p.length := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    have hc : c < X := hp c (by simp)
    have hcs : pack X cs + 1 ≤ X ^ cs.length := ih (fun d hd => hp d (by simp [hd]))
    calc pack X (c :: cs) = c + X * pack X cs := rfl
      _ < X + X * pack X cs := by omega
      _ = X * (pack X cs + 1) := by ring
      _ ≤ X * X ^ cs.length := Nat.mul_le_mul_left X hcs
      _ = X ^ (c :: cs).length := by rw [List.length_cons, pow_succ']

/-- Unpacking inverts packing when every coefficient is below the base. -/
theorem unpack_pack {X : ℕ} (p : List ℕ) (hp : ∀ c ∈ p, c < X) :
    unpack X p.length (pack X p) = p := by
  induction p with
  | nil => rfl
  | cons c cs ih =>
    have hc : c < X := hp c (by simp)
    have hX : 0 < X := lt_of_le_of_lt (Nat.zero_le _) hc
    simp only [List.length_cons, unpack, pack_cons]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.add_mul_div_left _ _ hX,
      Nat.div_eq_of_lt hc, zero_add, ih (fun d hd => hp d (by simp [hd]))]

/-- Packing inverts unpacking, up to the digits beyond the `L`-th. -/
theorem pack_unpack (X L V : ℕ) : pack X (unpack X L V) = V % X ^ L := by
  induction L generalizing V with
  | zero => simp [unpack, Nat.mod_one]
  | succ L ih => rw [unpack, pack_cons, ih, pow_succ', Nat.mod_mul]

theorem pack_unpack_of_lt {X L V : ℕ} (hV : V < X ^ L) : pack X (unpack X L V) = V := by
  rw [pack_unpack, Nat.mod_eq_of_lt hV]

/-- Kronecker substitution is a bijection between the coefficient lists of length `L` with entries
below `X` and the numbers below `X^L`. -/
def equiv (X L : ℕ) (hX : 0 < X) :
    {p : List ℕ // p.length = L ∧ ∀ c ∈ p, c < X} ≃ Fin (X ^ L) where
  toFun p := ⟨pack X p.1, by have h := pack_lt p.1 p.2.2; rwa [p.2.1] at h⟩
  invFun V := ⟨unpack X L V, length_unpack X L V, unpack_lt hX L V⟩
  left_inv p := by
    obtain ⟨p, hl, hp⟩ := p
    subst hl
    exact Subtype.ext (unpack_pack p hp)
  right_inv V := Fin.ext (pack_unpack_of_lt V.2)

@[simp] theorem pack_append_zeros (X : ℕ) (p : List ℕ) (n : ℕ) :
    pack X (p ++ List.replicate n 0) = pack X p := by
  induction p with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.nil_append, List.replicate_succ, pack_cons] at ih ⊢; simp [ih]
  | cons a p ih => simp [ih]

/-- With `L` at least the length, unpacking returns the coefficients padded by zeros. -/
theorem unpack_pack_of_le {X L : ℕ} (hX : 0 < X) (p : List ℕ) (hp : ∀ c ∈ p, c < X)
    (hL : p.length ≤ L) : unpack X L (pack X p) = p ++ List.replicate (L - p.length) 0 := by
  have hl : (p ++ List.replicate (L - p.length) 0).length = L := by simp; omega
  have h := unpack_pack (X := X) (p ++ List.replicate (L - p.length) 0) (by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hp c hc
    · rw [List.eq_of_mem_replicate hc]; exact hX)
  rwa [hl, pack_append_zeros] at h

/-- Every coefficient is at most the coefficient sum `p(1)`. -/
theorem le_pack_one (p : List ℕ) : ∀ c ∈ p, c ≤ pack 1 p := by
  induction p with
  | nil => simp
  | cons a p ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have := ih c hc; simp; omega

/-- The no-carry criterion: digits are coefficients once the coefficient sum is below the base. -/
theorem unpack_pack_of_one_lt {X L : ℕ} (p : List ℕ) (hp : pack 1 p < X) (hL : p.length ≤ L) :
    unpack X L (pack X p) = p ++ List.replicate (L - p.length) 0 :=
  unpack_pack_of_le (lt_of_le_of_lt (Nat.zero_le _) hp) p
    (fun c hc => lt_of_le_of_lt (le_pack_one p c hc) hp) hL

theorem pack_mono (p : List ℕ) {x x' : ℕ} (hx : x ≤ x') : pack x p ≤ pack x' p := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [pack_cons]; exact Nat.add_le_add_left (Nat.mul_le_mul hx ih) a

/-! ## Arithmetic -/

def addN : List ℕ → List ℕ → List ℕ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: addN p q

def smulN (c : ℕ) (p : List ℕ) : List ℕ := p.map (c * ·)

def mulN : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, b :: q => addN (smulN a (b :: q)) (0 :: mulN p (b :: q))

theorem pack_addN (X : ℕ) (p q : List ℕ) : pack X (addN p q) = pack X p + pack X q := by
  induction p generalizing q with
  | nil => simp [addN]
  | cons a p ih => cases q with
    | nil => simp [addN]
    | cons b q => simp [addN, ih]; ring

theorem pack_smulN (X c : ℕ) (p : List ℕ) : pack X (smulN c p) = c * pack X p := by
  induction p with
  | nil => simp [smulN]
  | cons a p ih => simp only [smulN, List.map_cons, pack_cons] at ih ⊢; rw [ih]; ring

theorem pack_mulN (X : ℕ) (p q : List ℕ) : pack X (mulN p q) = pack X p * pack X q := by
  induction p with
  | nil => simp [mulN]
  | cons a p ih =>
    cases q with
    | nil => simp [mulN]
    | cons b q => simp only [mulN] at ih ⊢; simp [pack_addN, pack_smulN, ih]; ring

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

/-! ## Rational values -/

/-- `p(y)` at a rational point. -/
def evalQ : List ℕ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => (c : ℚ) + x * evalQ cs x

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

@[simp] theorem evalQ_append_zeros (p : List ℕ) (n : ℕ) (x : ℚ) :
    evalQ (p ++ List.replicate n 0) x = evalQ p x := by
  induction p with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.nil_append, List.replicate_succ, evalQ] at ih ⊢; simp [ih]
  | cons a p ih => simp [evalQ, ih]

/-- The rational value of digits read back without carries. -/
theorem evalQ_unpack_pack {X L : ℕ} (p : List ℕ) (hp : pack 1 p < X) (hL : p.length ≤ L)
    (y : ℚ) : evalQ (unpack X L (pack X p)) y = evalQ p y := by
  rw [unpack_pack_of_one_lt p hp hL, evalQ_append_zeros]

/-! ## Change of base -/

/-- The Taylor shift `t ↦ p(k + t)` (used in proofs only). -/
def shiftN (p : List ℕ) (k : ℕ) : List ℕ := p.foldr (fun c acc => addN [c] (mulN [k, 1] acc)) []

/-- `t ↦ 2^{e(L−1)} p(t/2^e)` with `L = p.length`: coefficient `i` times `2^{e(L−1−i)}`. -/
def scaleN (e : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => (c * 2 ^ (e * cs.length)) :: scaleN e cs

theorem shiftN_cons (c : ℕ) (p : List ℕ) (k : ℕ) :
    shiftN (c :: p) k = addN [c] (mulN [k, 1] (shiftN p k)) := rfl

/-- A Taylor shift is a change of base. -/
theorem pack_shiftN (p : List ℕ) (k x : ℕ) : pack x (shiftN p k) = pack (k + x) p := by
  induction p with
  | nil => rfl
  | cons c p ih => rw [shiftN_cons, pack_addN, pack_mulN, ih]; simp

theorem evalQ_shiftN (p : List ℕ) (k : ℕ) (t : ℚ) : evalQ (shiftN p k) t = evalQ p (k + t) := by
  induction p with
  | nil => rfl
  | cons c p ih => rw [shiftN_cons, evalQ_addN, evalQ_mulN, ih]; simp [evalQ]

theorem length_shiftN (p : List ℕ) (k : ℕ) : (shiftN p k).length ≤ p.length := by
  induction p with
  | nil => simp [shiftN]
  | cons c p ih =>
    rw [shiftN_cons, length_addN]
    have := length_mulN_le [k, 1] (shiftN p k)
    simp only [List.length_cons, List.length_nil] at this ⊢
    omega

@[simp] theorem length_scaleN (e : ℕ) (p : List ℕ) : (scaleN e p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [scaleN, ih]

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

/-- The scaled polynomial at `2^e x`. -/
theorem pack_scaleN (e x : ℕ) (p : List ℕ) :
    pack (2 ^ e * x) (scaleN e p) = 2 ^ (e * (p.length - 1)) * pack x p := by
  induction p with
  | nil => simp [scaleN]
  | cons c cs ih =>
    simp only [scaleN, pack_cons, ih, List.length_cons, Nat.add_sub_cancel]
    rcases cs with _ | ⟨d, ds⟩
    · simp
    · simp only [List.length_cons, Nat.add_sub_cancel]
      rw [show e * (ds.length + 1) = e * ds.length + e by ring, pow_add]; ring

theorem pack_scaleN_le (e k : ℕ) (p : List ℕ) (hk : k + 1 ≤ 2 ^ e) :
    pack (k + 1) (scaleN e p) ≤ 2 ^ (e * (p.length - 1)) * pack 1 p :=
  calc pack (k + 1) (scaleN e p) ≤ pack (2 ^ e * 1) (scaleN e p) := pack_mono _ (by simpa using hk)
    _ = _ := pack_scaleN e 1 p

/-- The coefficients of `t ↦ p(k + t)` are the base-`Y` digits of `p(k + Y)`, once their sum
`p(k + 1)` is below `Y`. -/
theorem unpack_shift (p : List ℕ) (k L Y : ℕ) (hL : p.length ≤ L) (hY : pack (k + 1) p < Y) :
    unpack Y L (pack (k + Y) p) = shiftN p k ++ List.replicate (L - (shiftN p k).length) 0 := by
  rw [← pack_shiftN]
  exact unpack_pack_of_one_lt _ (by rwa [pack_shiftN]) ((length_shiftN p k).trans hL)

theorem evalQ_unpack_shift (p : List ℕ) (k L Y : ℕ) (hL : p.length ≤ L)
    (hY : pack (k + 1) p < Y) (t : ℚ) : evalQ (unpack Y L (pack (k + Y) p)) t = evalQ p (k + t) := by
  rw [unpack_shift p k L Y hL hY, evalQ_append_zeros, evalQ_shiftN]

end QRH.RepeatedMarks.Faceless.Kronecker
