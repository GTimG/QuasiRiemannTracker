/- Adapted by Joseph Bebel (2026-10-30) for the fixed five-window return. -/
import Candidate.Local.Qrh.PR97Refinement.Return.Tuning.Data
import Candidate.Local.Qrh.PR97Refinement.Return.Facts

/-!
# The row margins of the return as computable polynomials

`rowMargin e b δ p = countJ b δ p (θ - reserve - Ebase (edgeD e) (edgeC e) δ p) - 3/4 edgeD e countN b δ p`
(`Formulas.lean`) is, for every edge and branch, a polynomial in `(δ, p)`. `rowBrQ e bq` computes it for
any rational face `bq` (the `J`, `N` of `BranchQ`), `rowOldQ e` for Collet's old count at `kappa`;
`ev_rowBrQ` and `ev_rowOldQ` identify them with `rowMargin` once.
-/

set_option autoImplicit false

namespace QRH.PR97Refinement.ReturnTuning

open QRH.PR97Refinement.Return QRH.ArviReturnTuning QRH.ArviReturnTuning.Q2

/-- `Ebase d C δ p` of `Formulas.lean` as a polynomial. -/
def EbaseQ (d cap : ℚ) : Q2 :=
  add (C (1 / 2 + 13 * hQ / 75 - yQ / 2 - ellQ / 2 - 9 * d / 100))
    (add (smul (1 / 2) X) (smul (ellQ - cap / 2) (mul X Y)))

/-- `J (θ - reserve - Ebase) - 3/4 d N`. -/
def rowQ (d cap : ℚ) (J N : Q2) : Q2 :=
  sub (mul J (sub (C (thetaQ - reserveQ)) (EbaseQ d cap))) (smul (3 / 4 * d) N)

/-- Collet's old count at `kappa`: `oldD`, `oldC`, `countJ .old`, `countN .old`. -/
def oldDq : Q2 := sub (sub (C 3) Y) (smul (2 / (3 * kappaQ)) Y)
def oldCq : Q2 := mul (smul 2 (sub (C 1) Y)) (sub (C 1) (smul (1 / (3 * kappaQ)) Y))
def oldJq : Q2 := add (mul BranchQ.Vq oldDq) (mul X oldCq)
def oldNq : Q2 := add (mul (sub (C 1) X) oldJq) (smul (1 / 2) (mul (mul X oldCq) BranchQ.Vq))

def rowOldQ (e : Edge) : Q2 := rowQ (edgeDQ e) (edgeCQ e) oldJq oldNq
def rowBrQ (e : Edge) (b : BranchQ) : Q2 := rowQ (edgeDQ e) (edgeCQ e) b.Jq b.Nq

section
variable (δ p : ℝ)

theorem ev_EbaseQ (e : Edge) : Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p = Ebase (edgeD e) (edgeC e) δ p := by
  simp only [EbaseQ, ev_add, ev_smul, ev_mul, ev_C, ev_X, ev_Y]
  push_cast
  rw [cast_h, cast_y, cast_ell, cast_edgeD, cast_edgeC]
  unfold Ebase; ring

theorem ev_rowQ (e : Edge) (J N : Q2) :
    Q2.ev (rowQ (edgeDQ e) (edgeCQ e) J N) δ p =
      Q2.ev J δ p * (theta - reserve - Ebase (edgeD e) (edgeC e) δ p) - 3 / 4 * edgeD e * Q2.ev N δ p := by
  simp only [rowQ, ev_sub, ev_mul, ev_C, ev_smul, ev_EbaseQ]
  push_cast
  rw [cast_theta, cast_reserve, cast_edgeD]

theorem ev_oldJq : Q2.ev oldJq δ p = countJ .old δ p := by
  have hk := cast_kappa
  simp only [oldJq, oldDq, oldCq, ev_add, ev_mul, ev_sub, ev_smul, ev_C, ev_X, ev_Y, ev_Vq]
  push_cast
  rw [hk]
  simp only [countJ, oldD, oldC]
  ring

theorem ev_oldNq : Q2.ev oldNq δ p = countN .old δ p := by
  have hk := cast_kappa
  have hJ := ev_oldJq δ p
  simp only [oldNq, ev_add, ev_mul, ev_sub, ev_smul, ev_C, ev_X, hJ, ev_Vq, oldCq, ev_Y]
  push_cast
  rw [hk]
  simp only [countN, oldC]
  ring

theorem ev_rowOldQ (e : Edge) : Q2.ev (rowOldQ e) δ p = rowMargin e .old δ p := by
  rw [rowOldQ, ev_rowQ, ev_oldJq, ev_oldNq]; rfl

theorem countJ_eq (b : CountBranch) (hb : b ≠ .old) :
    countJ b δ p = R.Jr (branchL b) (isCap b) δ p := by
  cases b
  · exact (hb rfl).elim
  all_goals rfl

theorem countN_eq (b : CountBranch) (hb : b ≠ .old) :
    countN b δ p = R.Nr (branchB b) (branchL b) (branchCap b) (isCap b) δ p := by
  cases b
  · exact (hb rfl).elim
  all_goals rfl

theorem ev_rowBrQ (e : Edge) (b : CountBranch) (hb : b ≠ .old) :
    Q2.ev (rowBrQ e (toQ b)) δ p = rowMargin e b δ p := by
  obtain ⟨h1, h2, h3, h4⟩ := cast_toQ b hb
  rw [rowBrQ, ev_rowQ, ev_Jq, ev_Nq, h1, h2, h3, h4, ← countJ_eq δ p b hb, ← countN_eq δ p b hb]
  rfl

end

end QRH.PR97Refinement.ReturnTuning
