import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.HighCert

/-!
# Uniform scalar certificates for a piece of the faceless family

Every conjunct of `SourceValidC` (Collet's 16 scalar gates, the weak guard and the three special
sectors as cubic Bernstein coefficients in `ν ∈ [q, 3/4]`) and the cell condition of the step from
`P.node (y - Dy)` to `P.node y` is a rational function of the atoms
`A = Na(y, b)`, `D = Dn(y)`, `t = t(y, b)`, `b`, `B₀ = B(y - Dy)`, `L₀ = L(y - Dy)`
(the amplifier is `A/D`). Each gate times a positive multiplier is a polynomial `N` in the atoms;
`N` is computed as a polynomial in `y` and certified positive on `y ∈ [0, 1]` by `pos1I`.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks.Finite Poly

/-- `p > 0` on `y ∈ [0, 1]` from contiguous dyadic intervals, in integer arithmetic. -/
def pos1I (p : Poly) (l : List (ℕ × ℕ)) : Bool :=
  let D := IPoly.lcmDen p
  decide (0 < D) && IPoly.isIntMul p D && !l.isEmpty && IPoly.posOn (IPoly.ofPoly p D) 0 0 l

theorem pos1I_sound (p : Poly) (l : List (ℕ × ℕ)) (h : pos1I p l = true) (y : ℚ) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : 0 < eval p y := by
  simp only [pos1I, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hD, hint⟩, hne⟩, hpos⟩ := h
  have := IPoly.posOn_sound _ 0 0 l hpos y (by simpa using hy0) hy1
    (by intro h'; rw [h'] at hne; simp at hne)
  rw [IPoly.eval_ofPoly _ _ hint] at this
  have hD' : (0:ℚ) < (IPoly.lcmDen p : ℚ) := by exact_mod_cast hD
  exact pos_of_mul_pos_right this hD'.le

/-! ## The gates as functions of the atoms -/

/-- Collet's scalar gates with `a = A/D`, `sourceT = t`, `q = (1 - den) L₀/(6 B₀)`. -/
def sgAt (A D t b B0 L0 : ℚ) : Fin 16 → ℚ :=
  ![den, b - 2*feeE, A/D, 1/75 - A/D, (1 - 6*(A/D)) - (t + b)/2 - 4*feeE,
    B0*(1 - 6*(A/D)) - t - b - 4*feeE, 1 - (1 - den)*L0/(6*B0)*capF,
    feeR - ((1 - den)*L0/(6*B0)*B0/L0 + (1 - den)*L0/(6*B0)*capF + 4)*feeE - 10*feeE,
    A/D - 20*feeE, 49/100 - (9/2)*b,
    1 - (49/100 - (9/2)*b) - 1/2 - (9/2)*b - 10*feeE,
    5/6 + (499/1000)*(49/100 - (9/2)*b) - (t + b) - 9*(A/D) - feeF,
    1 - (t + b) - 5*(A/D) - feeF, 1 - 1/50 - (t + b) - 4*(A/D) - feeF,
    1 - 1/50 - (t + b) - (9/2)*(A/D) - feeF,
    (49/100 - (9/2)*b) - 7*(A/D) - feeF]

/-- The cleared scalar gates: `sgAt · (D · 6 B₀)`. -/
def sgNAt (A D t b B0 L0 : ℚ) : Fin 16 → ℚ :=
  let Lr := 49/100 - (9/2)*b
  ![den*(D*(6*B0)), (b - 2*feeE)*(D*(6*B0)), A*(6*B0), (D/75 - A)*(6*B0),
    (D*(1 - 4*feeE - (t + b)/2) - 6*A)*(6*B0),
    (B0*(D - 6*A) - D*(t + b + 4*feeE))*(6*B0),
    (6*B0 - (1 - den)*capF*L0)*D,
    (6*(feeR - ((1 - den)/6 + 14)*feeE)*B0 - (1 - den)*capF*feeE*L0)*D,
    (A - 20*feeE*D)*(6*B0), Lr*(D*(6*B0)), (1/100 - 10*feeE)*(D*(6*B0)),
    (D*(5/6 - feeF + (499/1000)*Lr - (t + b)) - 9*A)*(6*B0),
    (D*(1 - feeF - (t + b)) - 5*A)*(6*B0), (D*(49/50 - feeF - (t + b)) - 4*A)*(6*B0),
    (D*(49/50 - feeF - (t + b)) - (9/2)*A)*(6*B0), (D*(Lr - feeF) - 7*A)*(6*B0)]

theorem sgAt_mul (A D t b B0 L0 : ℚ) (hD : D ≠ 0) (hB : B0 ≠ 0) (hL : L0 ≠ 0) (j : Fin 16) :
    sgAt A D t b B0 L0 j * (D * (6 * B0)) = sgNAt A D t b B0 L0 j := by
  fin_cases j <;> simp [sgAt, sgNAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

/-- The weak guard times `D · L₀`. -/
def weakNAt (A D t B0 L0 : ℚ) : ℚ := capF*L0*(D - 6*A) - (B0*(D - 6*A) - t*D)

theorem weak_mul (A D t B0 L0 : ℚ) (hD : D ≠ 0) (hL : L0 ≠ 0) :
    (capF*(1 - 6*(A/D)) - (B0*(1 - 6*(A/D)) - t)/L0) * (D * L0) = weakNAt A D t B0 L0 := by
  simp only [weakNAt]; first | (field_simp; ring) | field_simp

/-- The special sectors `fixed, core, tiny` (`j = 6, 7, 8`), `F = 1 - 6a - e`. -/
def secAt (A D t b : ℚ) (j : ℕ) (ν : ℚ) : ℚ :=
  let a := A/D
  let T := t + b
  let F := 1 - 6*a - feeE
  let tt := 15 - 6*ν
  let H := (a - ν*T)*tt + (10 - 60*a)*ν
  match j with
  | 6 => H + (ν*F/2 - (1 - ν)*b - feeF)*tt
  | 7 => H + ((5/6)*F - (1 - ν)*b - feeF)*tt - 10*ν*F
  | _ => H + (ν*(F - 1/50)/2 - (1 - ν)*b - feeF)*tt - 10*ν*(1/50)

/-- `D · secAt`, cleared. -/
def secNAt (A D t b : ℚ) (j : ℕ) (ν : ℚ) : ℚ :=
  let NF := (1 - feeE)*D - 6*A
  let tt := 15 - 6*ν
  let HD := (A - ν*(t + b)*D)*tt + (10*D - 60*A)*ν
  match j with
  | 6 => HD + (ν/2*NF - (1 - ν)*(b*D) - feeF*D)*tt
  | 7 => HD + ((5/6)*NF - (1 - ν)*(b*D) - feeF*D)*tt - 10*ν*NF
  | _ => HD + (ν/2*(NF - D/50) - (1 - ν)*(b*D) - feeF*D)*tt - 10*ν/50*D

theorem secAt_mul (A D t b : ℚ) (hD : D ≠ 0) (j : ℕ) (ν : ℚ) :
    secAt A D t b j ν * D = secNAt A D t b j ν := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [secAt, secNAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

/-- Cubic Bernstein coefficients on `[N/S, 3/4]` (`3/4 - N/S = β/S`), cleared by `S³`. -/
def cubBern (c : Fin 4 → ℚ) (N β S : ℚ) : Fin 4 → ℚ :=
  let a0 := c 0*S^3 + c 1*N*S^2 + c 2*N^2*S + c 3*N^3
  let a1 := β*(c 1*S^2 + 2*c 2*N*S + 3*c 3*N^2)
  let a2 := β^2*(c 2*S + 3*c 3*N)
  let a3 := β^3*c 3
  ![a0, a0 + a1/3, a0 + 2*a1/3 + a2/3, a0 + a1 + a2 + a3]

theorem cubicBernstein_mul (f : ℚ → ℚ) (K N β S : ℚ) (hS : S ≠ 0) (hβ : β = (3/4)*S - N)
    (i : Fin 4) :
    cubicBernstein f (N/S) (3/4) i * (K * S^3) = cubBern (fun k => cubicCoeffs (fun ν => K * f ν) k) N β S i := by
  subst hβ
  fin_cases i <;> simp [cubicBernstein, cubBern, cubicCoeffs, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first | (field_simp; ring) | field_simp | ring

namespace Piece
variable (P : Piece)

/-! ## The gates of the family in terms of the atoms -/

theorem scalarGate_at (y b : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    scalarGate92 (P.node y) (P.node (y - P.Dy)) b =
      sgAt (P.NaAt y b) (P.DnAt y) (P.tAt y b) b (P.B (y - P.Dy)) (P.L (y - P.Dy)) := by
  funext j
  have hA := sourceA_eq P y b hB hL
  have hF := sourceF_eq P y b hB hL
  have hden := sourceDen_eq P y hB hL
  simp only [scalarGate92, sgAt, hA, hF, hden, sourceT_eq]
  rfl

theorem weakCap_at (y b : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) :
    weakCap (P.node y) (P.node (y - P.Dy)) b =
      capF*(1 - 6*(P.NaAt y b/P.DnAt y)) - (P.B (y - P.Dy)*(1 - 6*(P.NaAt y b/P.DnAt y)) - P.tAt y b)/P.L (y - P.Dy) := by
  simp only [weakCap, sourceF_eq P y b hB hL, sourceT_eq]
  rfl

theorem densityGate_at (y b ν : ℚ) (hB : P.B (y - P.Dy) ≠ 0) (hL : P.L (y - P.Dy) ≠ 0) (j : Fin 9)
    (hj : 6 ≤ j.val) :
    densityGate2 (P.node y) (P.node (y - P.Dy)) (some (P.node (y - P.Dy))) b ν j =
      secAt (P.NaAt y b) (P.DnAt y) (P.tAt y b) b j.val ν := by
  have hA := sourceA_eq P y b hB hL
  have hF := sourceF_eq P y b hB hL
  simp only [densityGate2, if_neg (show ¬ j.val < 6 by omega)]
  fin_cases j <;> simp at hj <;> simp only [densityGate, secAt, hA, hF, sourceT_eq] <;> rfl

/-! ## Polynomials of the atoms -/

def LrefP (b : Poly) : Poly := sub [49/100] (smul (9/2) b)

/-- `sgNAt` as a polynomial in `y`. -/
def sgN (b : Poly) (j : Fin 16) : Poly :=
  let A := P.NaP b
  let D := P.DnP
  let t := P.tP b
  let B0 := P.B0p
  let L0 := P.L0p
  let S6 := smul 6 B0
  let M := mul D S6
  let T := add t b
  let Lr := LrefP b
  ![smul den M, mul (sub b [2*feeE]) M, mul A S6, mul (sub (smul (1/75) D) A) S6,
    mul (sub (mul D (sub [1 - 4*feeE] (smul (1/2) T))) (smul 6 A)) S6,
    mul (sub (mul B0 (sub D (smul 6 A))) (mul D (add T [4*feeE]))) S6,
    mul (sub S6 (smul ((1 - den)*capF) L0)) D,
    mul (sub (smul (6*(feeR - ((1 - den)/6 + 14)*feeE)) B0) (smul ((1 - den)*capF*feeE) L0)) D,
    mul (sub A (smul (20*feeE) D)) S6, mul Lr M, smul (1/100 - 10*feeE) M,
    mul (sub (mul D (add [5/6 - feeF] (sub (smul (499/1000) Lr) T))) (smul 9 A)) S6,
    mul (sub (mul D (sub [1 - feeF] T)) (smul 5 A)) S6,
    mul (sub (mul D (sub [49/50 - feeF] T)) (smul 4 A)) S6,
    mul (sub (mul D (sub [49/50 - feeF] T)) (smul (9/2) A)) S6,
    mul (sub (mul D (sub Lr [feeF])) (smul 7 A)) S6] j

theorem eval_sgN (b : Poly) (y : ℚ) (j : Fin 16) :
    eval (P.sgN b j) y = sgNAt (P.NaAt y (eval b y)) (P.DnAt y) (P.tAt y (eval b y)) (eval b y)
      (P.B (y - P.Dy)) (P.L (y - P.Dy)) j := by
  fin_cases j <;>
    simp [sgN, sgNAt, LrefP, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

def weakN (b : Poly) : Poly :=
  let A := P.NaP b
  let D := P.DnP
  let FD := sub D (smul 6 A)
  sub (smul capF (mul P.L0p FD)) (sub (mul P.B0p FD) (mul (P.tP b) D))

theorem eval_weakN (b : Poly) (y : ℚ) :
    eval (P.weakN b) y = weakNAt (P.NaAt y (eval b y)) (P.DnAt y) (P.tAt y (eval b y))
      (P.B (y - P.Dy)) (P.L (y - P.Dy)) := by
  simp [weakN, weakNAt]; ring

/-- `secNAt` as a polynomial in `y`. -/
def secN (b : Poly) (j : ℕ) (ν : ℚ) : Poly :=
  let A := P.NaP b
  let D := P.DnP
  let t := P.tP b
  let NF := sub (smul (1 - feeE) D) (smul 6 A)
  let tt := 15 - 6*ν
  let HD := add (smul tt (sub A (smul ν (mul (add t b) D)))) (smul ν (sub (smul 10 D) (smul 60 A)))
  let bD := mul b D
  match j with
  | 6 => add HD (smul tt (sub (sub (smul (ν/2) NF) (smul (1 - ν) bD)) (smul feeF D)))
  | 7 => sub (add HD (smul tt (sub (sub (smul (5/6) NF) (smul (1 - ν) bD)) (smul feeF D))))
      (smul (10*ν) NF)
  | _ => sub (add HD (smul tt (sub (sub (smul (ν/2) (sub NF (smul (1/50) D))) (smul (1 - ν) bD))
      (smul feeF D)))) (smul (10*ν/50) D)

theorem eval_secN (b : Poly) (j : ℕ) (ν y : ℚ) :
    eval (P.secN b j ν) y = secNAt (P.NaAt y (eval b y)) (P.DnAt y) (P.tAt y (eval b y)) (eval b y) j ν := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [secN, secNAt, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- `(6 B₀)³ · Dn · cubicBernstein (special sector j)` on `[q, 3/4]`, as polynomials in `y`. -/
def secB (b : Poly) (j : ℕ) (i : Fin 4) : Poly :=
  let c := cubic4P (fun ν => P.secN b j ν)
  let N := P.alphaP
  let β := P.betaP
  let S := P.sixB0P
  let a0 := add (add (mul (c 0) (pow S 3)) (mul (c 1) (mul N (pow S 2))))
    (add (mul (c 2) (mul (pow N 2) S)) (mul (c 3) (pow N 3)))
  let a1 := mul β (add (add (mul (c 1) (pow S 2)) (smul 2 (mul (c 2) (mul N S)))) (smul 3 (mul (c 3) (pow N 2))))
  let a2 := mul (pow β 2) (add (mul (c 2) S) (smul 3 (mul (c 3) N)))
  let a3 := mul (pow β 3) (c 3)
  ![a0, add a0 (smul (1/3) a1), add (add a0 (smul (2/3) a1)) (smul (1/3) a2),
    add (add a0 a1) (add a2 a3)] i

theorem eval_secB (b : Poly) (j : ℕ) (i : Fin 4) (y : ℚ) :
    eval (P.secB b j i) y = cubBern (fun k => cubic4 (fun ν => eval (P.secN b j ν) y) k)
      (eval P.alphaP y) (eval P.betaP y) (eval P.sixB0P y) i := by
  fin_cases i <;> simp [secB, cubBern, eval_cubic4P, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

/-- The cell condition `2 (b - 2e) ≤ sourceF - e`, times `D`. -/
def cellN (b : Poly) : Poly :=
  sub (sub (smul (1 - feeE) P.DnP) (smul 6 (P.NaP b))) (smul 2 (mul (sub b [2*feeE]) P.DnP))

theorem eval_cellN (b : Poly) (y : ℚ) :
    eval (P.cellN b) y = (1 - feeE)*P.DnAt y - 6*P.NaAt y (eval b y) - 2*((eval b y - 2*feeE)*P.DnAt y) := by
  simp [cellN]

end Piece

end QRH.RepeatedMarks.Faceless
