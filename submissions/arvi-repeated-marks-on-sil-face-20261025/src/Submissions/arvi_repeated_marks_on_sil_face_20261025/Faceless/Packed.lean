import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.HighCert

/-!
# Packed polynomial arithmetic for the HIGH certificates

The kernel evaluates the coefficient polynomials of the HIGH gate (`Piece.highU`) slowly in `Rat`
list arithmetic. Here every polynomial of that computation is carried as a few big numbers:

  `⟨A(X), B(X), A(1), B(1), e, len, ok⟩` for natural coefficient lists `A, B`,

representing the rational polynomial `(A − B)/Δ^e`. A product of two polynomials is then four
big-number products instead of one rational operation per pair of coefficients. Sums align the
exponents of `Δ` (no gcd, no growth of denominators beyond `Δ^max`). A rational constant `c` is
applied as the integer `c.num · (Δ / c.den)` with one more power of `Δ`; `ok` records that `c.den`
divides `Δ`. At the end the coefficients of `A` and `B` are read back as base-`X` digits, which is
exact once `A(1), B(1) < X`.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless

open Poly

namespace Pk

open IPoly Faceless.Kronecker

/-- A packed polynomial `(A − B)/Δ^e` at base `X` (see the module docstring). -/
structure PZ where
  pos : ℕ
  neg : ℕ
  pos1 : ℕ
  neg1 : ℕ
  e : ℕ
  len : ℕ
  ok : Bool

section ops
variable (Δ : ℕ)

def scale (r : PZ) (k : ℕ) : PZ :=
  ⟨Δ ^ k * r.pos, Δ ^ k * r.neg, Δ ^ k * r.pos1, Δ ^ k * r.neg1, r.e + k, r.len, r.ok⟩

def add (r s : PZ) : PZ :=
  let g := max r.e s.e
  let r' := scale Δ r (g - r.e)
  let s' := scale Δ s (g - s.e)
  ⟨r'.pos + s'.pos, r'.neg + s'.neg, r'.pos1 + s'.pos1, r'.neg1 + s'.neg1, g, max r.len s.len,
    r.ok && s.ok⟩

def neg (r : PZ) : PZ := ⟨r.neg, r.pos, r.neg1, r.pos1, r.e, r.len, r.ok⟩

def sub (r s : PZ) : PZ := add Δ r (neg s)

def mul (r s : PZ) : PZ :=
  ⟨r.pos * s.pos + r.neg * s.neg, r.pos * s.neg + r.neg * s.pos,
    r.pos1 * s.pos1 + r.neg1 * s.neg1, r.pos1 * s.neg1 + r.neg1 * s.pos1, r.e + s.e,
    r.len + s.len, r.ok && s.ok⟩

/-- Multiplication by the rational constant `c`. -/
def smul (c : ℚ) (r : PZ) : PZ :=
  let w := c.num.natAbs * (Δ / c.den)
  let ok := r.ok && (Δ % c.den == 0)
  if 0 ≤ c.num then ⟨w * r.pos, w * r.neg, w * r.pos1, w * r.neg1, r.e + 1, r.len, ok⟩
  else ⟨w * r.neg, w * r.pos, w * r.neg1, w * r.pos1, r.e + 1, r.len, ok⟩

/-- The zero polynomial. -/
def zero : PZ := ⟨0, 0, 0, 0, 0, 0, true⟩

/-- The constant polynomial `1`. -/
def one : PZ := ⟨1, 0, 1, 0, 0, 1, true⟩

def const (c : ℚ) : PZ := smul Δ c one

def pow (r : PZ) : ℕ → PZ
  | 0 => one
  | n + 1 => mul r (pow r n)

end ops

/-- An integer coefficient list `q` with denominator `Δ^e`. -/
def ofI (X : ℕ) (q : IPoly) (e : ℕ) : PZ :=
  let r := PP.pack X q
  ⟨r.pos, r.neg, r.pos1, r.neg1, e, q.length, true⟩

/-- A rational polynomial, scaled by `Δ^e` to integers (`ok` iff the scaling is exact). -/
def ofPoly (X Δ : ℕ) (q : Poly) (e : ℕ) : PZ :=
  let r := ofI X (IPoly.ofPoly q (Δ ^ e)) e
  { r with len := q.length, ok := IPoly.isIntMul q (Δ ^ e) }

/-- The integer coefficients `A − B`, read back as base-`X` digits. -/
def unpack (X : ℕ) (r : PZ) : IPoly := subD (Kronecker.unpack X r.len r.pos) (Kronecker.unpack X r.len r.neg)

/-- `r` represents the rational polynomial `q`: whenever `r.ok`, `A − B = Δ^e · q`. -/
def Rep (X Δ : ℕ) (r : PZ) (q : Poly) : Prop :=
  r.ok = true → ∃ A B : List ℕ, A.length ≤ r.len ∧ B.length ≤ r.len ∧
    r.pos = Kronecker.pack X A ∧ r.neg = Kronecker.pack X B ∧ r.pos1 = Kronecker.pack 1 A ∧
    r.neg1 = Kronecker.pack 1 B ∧
    ∀ y : ℚ, evalQ A y - evalQ B y = (Δ : ℚ) ^ r.e * Poly.eval q y

section reps
variable {X Δ : ℕ}

theorem rep_scale {r : PZ} {q : Poly} (k : ℕ) (h : Rep X Δ r q) : Rep X Δ (scale Δ r k) q := by
  intro hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok
  refine ⟨smulN (Δ ^ k) A, smulN (Δ ^ k) B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_smulN]; exact hA
  · rw [length_smulN]; exact hB
  · simp only [scale, h1, pack_smulN]
  · simp only [scale, h2, pack_smulN]
  · simp only [scale, h3, pack_smulN]
  · simp only [scale, h4, pack_smulN]
  · intro y
    rw [evalQ_smulN, evalQ_smulN, ← mul_sub, h5]
    simp only [scale]; push_cast; ring

theorem rep_add {r s : PZ} {q q' : Poly} (hr : Rep X Δ r q) (hs : Rep X Δ s q') :
    Rep X Δ (add Δ r s) (Poly.add q q') := by
  intro hok
  simp only [add, Bool.and_eq_true] at hok
  have hr' := rep_scale (max r.e s.e - r.e) hr
  have hs' := rep_scale (max r.e s.e - s.e) hs
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := hr' hok.1
  obtain ⟨A', B', hA', hB', h1', h2', h3', h4', h5'⟩ := hs' hok.2
  refine ⟨addN A A', addN B B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_addN]; simp only [scale] at hA hA'; simp only [add]; omega
  · rw [length_addN]; simp only [scale] at hB hB'; simp only [add]; omega
  · simp only [add, h1, h1', pack_addN]
  · simp only [add, h2, h2', pack_addN]
  · simp only [add, h3, h3', pack_addN]
  · simp only [add, h4, h4', pack_addN]
  · intro y
    have e1 : (scale Δ r (max r.e s.e - r.e)).e = max r.e s.e := by
      simp only [scale]; omega
    have e2 : (scale Δ s (max r.e s.e - s.e)).e = max r.e s.e := by
      simp only [scale]; omega
    rw [evalQ_addN, evalQ_addN, Poly.eval_add]
    have := h5 y; have := h5' y
    rw [e1] at h5; rw [e2] at h5'
    simp only [add]
    linear_combination h5 y + h5' y

theorem rep_neg {r : PZ} {q : Poly} (h : Rep X Δ r q) : Rep X Δ (neg r) (Poly.smul (-1) q) := by
  intro hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok
  refine ⟨B, A, hB, hA, h2, h1, h4, h3, fun y => ?_⟩
  rw [Poly.eval_smul]; simp only [neg]; linear_combination -(h5 y)

theorem rep_sub {r s : PZ} {q q' : Poly} (hr : Rep X Δ r q) (hs : Rep X Δ s q') :
    Rep X Δ (sub Δ r s) (Poly.sub q q') := rep_add hr (rep_neg hs)

theorem rep_mul {r s : PZ} {q q' : Poly} (hr : Rep X Δ r q) (hs : Rep X Δ s q') :
    Rep X Δ (mul r s) (Poly.mul q q') := by
  intro hok
  simp only [mul, Bool.and_eq_true] at hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := hr hok.1
  obtain ⟨A', B', hA', hB', h1', h2', h3', h4', h5'⟩ := hs hok.2
  refine ⟨addN (mulN A A') (mulN B B'), addN (mulN A B') (mulN B A'),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_addN]
    have := length_mulN_le A A'; have := length_mulN_le B B'
    simp only [mul]; omega
  · rw [length_addN]
    have := length_mulN_le A B'; have := length_mulN_le B A'
    simp only [mul]; omega
  · simp only [mul, h1, h2, h1', h2', pack_addN, pack_mulN]
  · simp only [mul, h1, h2, h1', h2', pack_addN, pack_mulN]
  · simp only [mul, h3, h4, h3', h4', pack_addN, pack_mulN]
  · simp only [mul, h3, h4, h3', h4', pack_addN, pack_mulN]
  · intro y
    rw [evalQ_addN, evalQ_addN, evalQ_mulN, evalQ_mulN, evalQ_mulN, evalQ_mulN,
      Poly.eval_mul]
    simp only [mul]
    have e : (evalQ A y * evalQ A' y + evalQ B y * evalQ B' y) -
        (evalQ A y * evalQ B' y + evalQ B y * evalQ A' y) =
        (evalQ A y - evalQ B y) * (evalQ A' y - evalQ B' y) := by ring
    rw [e, h5 y, h5' y]; ring

theorem rep_smul {r : PZ} {q : Poly} (c : ℚ) (h : Rep X Δ r q) :
    Rep X Δ (smul Δ c r) (Poly.smul c q) := by
  intro hok
  have hok' : r.ok = true ∧ Δ % c.den = 0 := by
    unfold smul at hok; split_ifs at hok <;> simpa [Bool.and_eq_true, beq_iff_eq] using hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok'.1
  have hdvd : c.den ∣ Δ := Nat.dvd_of_mod_eq_zero hok'.2
  have hden : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  have hw : ((c.num.natAbs * (Δ / c.den) : ℕ) : ℚ) = |(c.num : ℚ)| * ((Δ : ℚ) / c.den) := by
    rw [Nat.cast_mul, Nat.cast_div hdvd hden, Nat.cast_natAbs, Int.cast_abs]
  have key : (c.num : ℚ) * ((Δ : ℚ) / c.den) = c * Δ := by
    have e1 : (c.num : ℚ) * ((Δ : ℚ) / c.den) = ((c.num : ℚ) / c.den) * Δ := by ring
    rw [e1, Rat.num_div_den]
  have he : (smul Δ c r).e = r.e + 1 := by unfold smul; split_ifs <;> rfl
  have hl : (smul Δ c r).len = r.len := by unfold smul; split_ifs <;> rfl
  set w := c.num.natAbs * (Δ / c.den) with hwdef
  by_cases hs : 0 ≤ c.num
  · have habs : |(c.num : ℚ)| = c.num := abs_of_nonneg (by exact_mod_cast hs)
    have hsm : smul Δ c r = ⟨w * r.pos, w * r.neg, w * r.pos1, w * r.neg1, r.e + 1, r.len,
        r.ok && (Δ % c.den == 0)⟩ := by unfold smul; rw [if_pos hs]
    refine ⟨smulN w A, smulN w B, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [length_smulN, hl]; exact hA
    · rw [length_smulN, hl]; exact hB
    · rw [hsm, pack_smulN, h1]
    · rw [hsm, pack_smulN, h2]
    · rw [hsm, pack_smulN, h3]
    · rw [hsm, pack_smulN, h4]
    · intro y
      rw [evalQ_smulN, evalQ_smulN, ← mul_sub, h5 y, hw, he, Poly.eval_smul, habs]
      linear_combination ((Δ:ℚ) ^ r.e * Poly.eval q y) * key
  · have habs : |(c.num : ℚ)| = -c.num := abs_of_neg (by exact_mod_cast (not_le.mp hs))
    have hsm : smul Δ c r = ⟨w * r.neg, w * r.pos, w * r.neg1, w * r.pos1, r.e + 1, r.len,
        r.ok && (Δ % c.den == 0)⟩ := by unfold smul; rw [if_neg hs]
    refine ⟨smulN w B, smulN w A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [length_smulN, hl]; exact hB
    · rw [length_smulN, hl]; exact hA
    · rw [hsm, pack_smulN, h2]
    · rw [hsm, pack_smulN, h1]
    · rw [hsm, pack_smulN, h4]
    · rw [hsm, pack_smulN, h3]
    · intro y
      rw [evalQ_smulN, evalQ_smulN, ← mul_sub, ← neg_sub, mul_neg, h5 y, hw, he, Poly.eval_smul,
        habs]
      linear_combination ((Δ:ℚ) ^ r.e * Poly.eval q y) * key

theorem rep_zero : Rep X Δ zero [] := by
  intro _
  exact ⟨[], [], le_rfl, le_rfl, rfl, rfl, rfl, rfl, fun y => by simp [zero, evalQ]⟩

theorem rep_one : Rep X Δ one [1] := by
  intro _
  refine ⟨[1], [], le_rfl, by simp [one], ?_, rfl, ?_, rfl, fun y => ?_⟩
  · simp [one]
  · simp [one]
  · simp [one, evalQ]

theorem rep_const (c : ℚ) : Rep X Δ (const Δ c) [c] := by
  have h := rep_smul (X := X) (Δ := Δ) c (rep_one (X := X) (Δ := Δ))
  intro hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok
  refine ⟨A, B, hA, hB, h1, h2, h3, h4, fun y => ?_⟩
  rw [h5 y]; simp [const, Poly.smul, Poly.eval]

theorem rep_pow {r : PZ} {q : Poly} (h : Rep X Δ r q) : ∀ n, Rep X Δ (pow r n) (Poly.pow q n)
  | 0 => rep_one
  | n + 1 => rep_mul h (rep_pow h n)

theorem rep_trim {r : PZ} {q : Poly} (h : Rep X Δ r q) : Rep X Δ r (Poly.trim q) := by
  intro hok
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok
  exact ⟨A, B, hA, hB, h1, h2, h3, h4, fun y => by rw [h5 y, Poly.eval_trim]⟩

theorem rep_ofPoly (q : Poly) (e : ℕ) : Rep X Δ (ofPoly X Δ q e) q := by
  intro hok
  simp only [ofPoly] at hok
  refine ⟨posPart (IPoly.ofPoly q (Δ ^ e)), negPart (IPoly.ofPoly q (Δ ^ e)),
    ?_, ?_, rfl, rfl, rfl, rfl, fun y => ?_⟩
  · simp [ofPoly, IPoly.ofPoly]
  · simp [ofPoly, IPoly.ofPoly]
  · rw [← IPoly.eval_eq_parts, IPoly.eval_ofPoly _ _ hok]; simp [ofPoly, ofI]

end reps

/-- Read-back: the digits give `Δ^e · q` once `A(1), B(1) < X`. -/
theorem eval_unpack {X Δ : ℕ} {r : PZ} {q : Poly} (h : Rep X Δ r q) (hok : r.ok = true)
    (hp : r.pos1 < X) (hn : r.neg1 < X) (y : ℚ) :
    IPoly.eval (unpack X r) y = (Δ : ℚ) ^ r.e * Poly.eval q y := by
  obtain ⟨A, B, hA, hB, h1, h2, h3, h4, h5⟩ := h hok
  rw [unpack, h1, h2, eval_subD_unpack (h3 ▸ hp) (h4 ▸ hn) hA hB, h5 y]

/-! ## The HIGH coefficient formula on packed polynomials -/

section formula
variable (X Δ eIn : ℕ)

def dIZ (p : ℚ) : Fin 2 → PZ := ![const Δ 1, const Δ (1 - p)]
def ePZ (p : ℚ) (L : PZ) : Fin 3 → PZ := ![const Δ 1, const Δ 1, add Δ L (const Δ (-2*p))]
def gPZ (L : PZ) : Fin 3 → PZ := ![const Δ 1, const Δ 1, L]

def gateMZ (ν p : ℚ) (L : PZ) (k : Branch) : PZ :=
  add Δ (smul Δ (12*ν) (mul (dIZ Δ p k.1) (ePZ Δ p L k.2)))
    (smul Δ (5 - 6*ν) (add Δ (smul Δ 2 (ePZ Δ p L k.2)) (mul (dIZ Δ p k.1) (gPZ Δ L k.2))))

def gateGDnZ (Dn Na NF TD SD : PZ) (fee K : ℚ) (B L : PZ) (hc ν p : ℚ) (k : Branch) : PZ :=
  let bI : Fin 2 → PZ := ![smul Δ (2*p*K) SD, smul Δ p NF]
  let hP : Fin 3 → PZ := ![smul Δ (2*p) SD, smul Δ (2*p*hc) NF, mul (smul Δ (2*p) B) NF]
  let base := add Δ (smul Δ (15 - 6*ν) (sub Δ Na (smul Δ ν TD)))
    (add Δ (smul Δ ν (sub Δ (smul Δ 10 Dn) (smul Δ 60 Na)))
      (add Δ (smul Δ ((15 - 6*ν)*(1 - 2*p)*ν) SD) (add Δ (smul Δ (-10*ν) NF) (smul Δ (-fee*(15 - 6*ν)) Dn))))
  let N := add Δ (smul Δ 10 (mul NF (mul (dIZ Δ p k.1) (ePZ Δ p L k.2))))
    (smul Δ (5 - 6*ν) (add Δ (smul Δ 2 (mul (ePZ Δ p L k.2) (bI k.1))) (mul (dIZ Δ p k.1) (hP k.2))))
  add Δ (mul (gateMZ Δ ν p L k) base) (smul Δ (ν*(15 - 6*ν)) N)

/-- `Piece.valP` on packed polynomials; the polynomial inputs enter through `ofPoly` with `Δ^eIn`. -/
def valPZ (P : Piece) (b : Poly) (k : Branch) (ν p : ℚ) : PZ :=
  let DnZ := ofPoly X Δ P.DnP eIn
  let T := add Δ (ofPoly X Δ (P.tP b) eIn) (ofPoly X Δ b eIn)
  let S := sub Δ (ofPoly X Δ b eIn) (const Δ (2*feeE))
  let Na := ofPoly X Δ (P.NaP b) eIn
  let NF := sub Δ (smul Δ (1 - feeE) DnZ) (smul Δ 6 Na)
  gateGDnZ Δ DnZ Na NF (mul T DnZ) (mul S DnZ) feeF 8 (ofPoly X Δ P.B0p eIn) (ofPoly X Δ P.L0p eIn)
    capF ν p k

def cubic4Z (f : ℚ → PZ) : Fin 4 → PZ :=
  ![f 0, smul Δ (1/6) (add Δ (add Δ (smul Δ (-1) (f 2)) (smul Δ 6 (f 1)))
      (add Δ (smul Δ (-3) (f 0)) (smul Δ (-2) (f (-1))))),
    smul Δ (1/2) (add Δ (add Δ (f 1) (f (-1))) (smul Δ (-2) (f 0))),
    smul Δ (1/6) (add Δ (add Δ (f 2) (smul Δ (-3) (f 1))) (add Δ (smul Δ 3 (f 0)) (smul Δ (-1) (f (-1)))))]

def bicubicZ (f : ℚ → ℚ → PZ) (i j : Fin 4) : PZ :=
  cubic4Z Δ (fun x => cubic4Z Δ (fun z => f x z) j) i

def powsZ (α β D : PZ) (i a : ℕ) : PZ :=
  smul Δ (i.choose a) (mul (pow α (i - a)) (mul (pow β a) (pow D (3 - i))))

def sumZ (l : List PZ) : PZ := l.foldr (add Δ) zero

def cuZ (c : Fin 4 → Fin 4 → PZ) (α β D : PZ) (a j : Fin 4) : PZ :=
  sumZ Δ (((List.finRange 4).filter (fun i : Fin 4 => a.val ≤ i.val)).map
    (fun i => mul (c i j) (powsZ Δ α β D i a)))

/-- `Piece.highU` on packed polynomials. -/
def highUZ (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  cuZ Δ (bicubicZ Δ (fun ν p => valPZ X Δ eIn P b k ν p)) (ofPoly X Δ P.alphaP eIn)
    (ofPoly X Δ P.betaP eIn) (ofPoly X Δ P.sixB0P eIn) a j

end formula

section formula_reps
variable {X Δ : ℕ}

theorem rep_vec2 {a b : PZ} {a' b' : Poly} (ha : Rep X Δ a a') (hb : Rep X Δ b b') (i : Fin 2) :
    Rep X Δ (![a, b] i) (![a', b'] i) := by
  fin_cases i <;> assumption

theorem rep_vec3 {a b c : PZ} {a' b' c' : Poly} (ha : Rep X Δ a a') (hb : Rep X Δ b b')
    (hc : Rep X Δ c c') (i : Fin 3) : Rep X Δ (![a, b, c] i) (![a', b', c'] i) := by
  fin_cases i <;> assumption

theorem rep_vec4 {a b c d : PZ} {a' b' c' d' : Poly} (ha : Rep X Δ a a') (hb : Rep X Δ b b')
    (hc : Rep X Δ c c') (hd : Rep X Δ d d') (i : Fin 4) :
    Rep X Δ (![a, b, c, d] i) (![a', b', c', d'] i) := by
  fin_cases i <;> assumption

theorem rep_dIZ (p : ℚ) (i : Fin 2) : Rep X Δ (dIZ Δ p i) (dIP p i) :=
  rep_vec2 (rep_const 1) (rep_const (1 - p)) i

theorem rep_ePZ (p : ℚ) {L : PZ} {L' : Poly} (hL : Rep X Δ L L') (j : Fin 3) :
    Rep X Δ (ePZ Δ p L j) (ePP p L' j) :=
  rep_vec3 (rep_const 1) (rep_const 1) (rep_add hL (rep_const (-2*p))) j

theorem rep_gPZ {L : PZ} {L' : Poly} (hL : Rep X Δ L L') (j : Fin 3) :
    Rep X Δ (gPZ Δ L j) (gPP L' j) :=
  rep_vec3 (rep_const 1) (rep_const 1) hL j

theorem rep_gateMZ (ν p : ℚ) {L : PZ} {L' : Poly} (hL : Rep X Δ L L') (k : Branch) :
    Rep X Δ (gateMZ Δ ν p L k) (gateMP ν p L' k) :=
  rep_add (rep_smul _ (rep_mul (rep_dIZ p k.1) (rep_ePZ p hL k.2)))
    (rep_smul _ (rep_add (rep_smul _ (rep_ePZ p hL k.2)) (rep_mul (rep_dIZ p k.1) (rep_gPZ hL k.2))))

theorem rep_gateGDnZ {Dn Na NF TD SD B L : PZ} {Dn' Na' NF' TD' SD' B' L' : Poly}
    (hDn : Rep X Δ Dn Dn') (hNa : Rep X Δ Na Na') (hNF : Rep X Δ NF NF') (hTD : Rep X Δ TD TD')
    (hSD : Rep X Δ SD SD') (hB : Rep X Δ B B') (hL : Rep X Δ L L') (fee K hc ν p : ℚ) (k : Branch) :
    Rep X Δ (gateGDnZ Δ Dn Na NF TD SD fee K B L hc ν p k)
      (gateGDnP Dn' Na' NF' TD' SD' fee K B' L' hc ν p k) := by
  unfold gateGDnZ gateGDnP
  exact rep_add (rep_mul (rep_gateMZ ν p hL k)
      (rep_add (rep_smul _ (rep_sub hNa (rep_smul _ hTD)))
        (rep_add (rep_smul _ (rep_sub (rep_smul _ hDn) (rep_smul _ hNa)))
          (rep_add (rep_smul _ hSD) (rep_add (rep_smul _ hNF) (rep_smul _ hDn))))))
    (rep_smul _ (rep_add (rep_smul _ (rep_mul hNF (rep_mul (rep_dIZ p k.1) (rep_ePZ p hL k.2))))
      (rep_smul _ (rep_add (rep_smul _ (rep_mul (rep_ePZ p hL k.2)
          (rep_vec2 (rep_smul _ hSD) (rep_smul _ hNF) k.1)))
        (rep_mul (rep_dIZ p k.1)
          (rep_vec3 (rep_smul _ hSD) (rep_smul _ hNF) (rep_mul (rep_smul _ hB) hNF) k.2))))))

theorem rep_valPZ (eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (ν p : ℚ) :
    Rep X Δ (valPZ X Δ eIn P b k ν p) (P.valP b k ν p) := by
  unfold valPZ Piece.valP
  apply rep_trim
  exact rep_gateGDnZ (rep_ofPoly _ _) (rep_ofPoly _ _)
    (rep_sub (rep_smul _ (rep_ofPoly _ _)) (rep_smul _ (rep_ofPoly _ _)))
    (rep_mul (rep_add (rep_ofPoly _ _) (rep_ofPoly _ _)) (rep_ofPoly _ _))
    (rep_mul (rep_sub (rep_ofPoly _ _) (rep_const _)) (rep_ofPoly _ _))
    (rep_ofPoly _ _) (rep_ofPoly _ _) _ _ _ _ _ k

theorem rep_cubic4Z {f : ℚ → PZ} {g : ℚ → Poly} (h : ∀ x, Rep X Δ (f x) (g x)) (i : Fin 4) :
    Rep X Δ (cubic4Z Δ f i) (cubic4P g i) :=
  rep_vec4 (h 0)
    (rep_smul _ (rep_add (rep_add (rep_smul _ (h 2)) (rep_smul _ (h 1)))
      (rep_add (rep_smul _ (h 0)) (rep_smul _ (h (-1))))))
    (rep_smul _ (rep_add (rep_add (h 1) (h (-1))) (rep_smul _ (h 0))))
    (rep_smul _ (rep_add (rep_add (h 2) (rep_smul _ (h 1))) (rep_add (rep_smul _ (h 0)) (rep_smul _ (h (-1))))))
    i

theorem rep_bicubicZ {f : ℚ → ℚ → PZ} {g : ℚ → ℚ → Poly} (h : ∀ x z, Rep X Δ (f x z) (g x z))
    (i j : Fin 4) : Rep X Δ (bicubicZ Δ f i j) (bicubicP g i j) :=
  rep_cubic4Z (fun x => rep_cubic4Z (fun z => h x z) j) i

theorem rep_powsZ {α β D : PZ} {α' β' D' : Poly} (hα : Rep X Δ α α') (hβ : Rep X Δ β β')
    (hD : Rep X Δ D D') (i a : ℕ) : Rep X Δ (powsZ Δ α β D i a) (powsP α' β' D' i a) :=
  rep_smul _ (rep_mul (rep_pow hα _) (rep_mul (rep_pow hβ _) (rep_pow hD _)))

theorem rep_sumZ_map {ι : Type} (l : List ι) {f : ι → PZ} {g : ι → Poly}
    (h : ∀ i, Rep X Δ (f i) (g i)) : Rep X Δ (sumZ Δ (l.map f)) (sumP (l.map g)) := by
  induction l with
  | nil => exact rep_zero
  | cons x l ih => exact rep_add (h x) ih

theorem rep_cuZ {c : Fin 4 → Fin 4 → PZ} {c' : Fin 4 → Fin 4 → Poly}
    (hc : ∀ i j, Rep X Δ (c i j) (c' i j)) {α β D : PZ} {α' β' D' : Poly} (hα : Rep X Δ α α')
    (hβ : Rep X Δ β β') (hD : Rep X Δ D D') (a j : Fin 4) :
    Rep X Δ (cuZ Δ c α β D a j) (cuP c' α' β' D' a j) := by
  unfold cuZ cuP cuTerms
  exact rep_trim (rep_sumZ_map _ (fun i => rep_mul (hc i j) (rep_powsZ hα hβ hD _ _)))

theorem rep_highUZ (eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) :
    Rep X Δ (highUZ X Δ eIn P b k a j) (P.highU b k a j) := by
  unfold highUZ Piece.highU
  exact rep_cuZ (rep_bicubicZ (fun ν p => rep_valPZ eIn P b k ν p)) (rep_ofPoly _ _) (rep_ofPoly _ _)
    (rep_ofPoly _ _) a j

end formula_reps

/-! ## The packed HIGH certificate -/

def maxE16 (r : Fin 4 → Fin 4 → PZ) : ℕ :=
  (List.finRange 4).foldr (fun i acc => (List.finRange 4).foldr (fun j acc' => max (r i j).e acc') acc) 0

theorem le_maxE16 (r : Fin 4 → Fin 4 → PZ) (i j : Fin 4) : (r i j).e ≤ maxE16 r := by
  unfold maxE16
  have key : ∀ l : List (Fin 4), i ∈ l → (r i j).e ≤
      l.foldr (fun i acc => (List.finRange 4).foldr (fun j acc' => max (r i j).e acc') acc) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons z l ih =>
      simp only [List.foldr_cons]
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact IPoly.le_foldr_max (fun j => (r i j).e) _ _ (List.mem_finRange j)
      · exact le_trans (ih hl) (IPoly.le_foldr_max_init (fun j => (r z j).e) _ _)
  exact key _ (List.mem_finRange i)

/-- The 16 coefficient polynomials of `highU`, packed, aligned to the common power `Δ^E`. -/
def alignedK (X Δ eIn : ℕ) (P : Piece) (b : Poly) (k : Branch) (a j : Fin 4) : PZ :=
  scale Δ (highUZ X Δ eIn P b k a j)
    (maxE16 (fun a j => highUZ X Δ eIn P b k a j) - (highUZ X Δ eIn P b k a j).e)

end Pk

end QRH.RepeatedMarks.Faceless
