import Submissions.arvi_selected_leaf.Tuning.GuardsQ
import Submissions.arvi_selected_leaf.Return.Formulas

/-!
# One parametric admission lemma for every face

`R.guard B L cap k δ p j` is `Formulas.lean`'s `admissionGuard` with the branch data `(branchB b,
branchL b, branchCap b, isCap b)` replaced by real parameters (`admissionGuard_eq`, definitional).
`ev_guard` proves once, for every rational face `(B, Λ, cap)` and both pieces of the plain curve, that the
computable polynomial `BranchQ.guard` evaluates to it. `window_admitted` turns a passed kernel check
`windowCheck` into the `certificate` field of a `ReturnCountWindow`.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace QRH.ArviReturnTuning

open QRH.ArviDensity.Return

/-! ### The real mirror of `Formulas.lean` with the branch data as parameters -/

namespace R
noncomputable section
variable (B L cap : ℝ) (k : Bool)

def Dr (p : ℝ) : ℝ := if k then 3 - p else 3 - p - 4 * p / L
def Ar (p : ℝ) : ℝ := if k then 2 else 2 - 4 * p / L
def C0r (p : ℝ) : ℝ := if k then 1 - 2 * p * (cap - 1 / 10000000) else 1 - 2 * p * B / L
def Zr (p : ℝ) : ℝ := if k then 2 * p * (cap - 1 / 10000000) else 2 * p * B / L
def Ur (p : ℝ) : ℝ := (1 - p) * C0r B L cap k p
def Jr (δ p : ℝ) : ℝ := V δ * Dr L k p + δ * (1 - p) * Ar L k p
def Nr (δ p : ℝ) : ℝ := (1 - δ) * Jr L k δ p + V δ * δ * Ur B L cap k p
def Tr (δ p : ℝ) : ℝ := Jr L k δ p + δ * Ur B L cap k p
def RNr (δ p : ℝ) : ℝ := Ar L k p * Tr B L cap k δ p + (Zr B L cap k p - p) * Jr L k δ p
def MNr (δ p : ℝ) : ℝ := Dr L k p * Tr B L cap k δ p - RNr B L cap k δ p
def DJr (δ p : ℝ) : ℝ := Dr L k p * Jr L k δ p
def lowerMr : ℝ :=
  if k then mMinus + 1 / 10000000
  else max (mMinus + 1 / 10000000) ((B - L * (cap - 1 / 10000000)) / 2 + 1 / 10000000)
def upperMr : ℝ :=
  if k then min (min (11 / 25 - 1 / 10000000) (naturalM - 1 / 10000000))
    ((B - L * (cap - 1 / 10000000)) / 2 - 1 / 10000000)
  else min (min (11 / 25 - 1 / 10000000) (naturalM - 1 / 10000000))
    ((B - L * (sMinus + 1 / 10000000)) / 2 - 1 / 10000000)
def dDr : ℝ := if k then -1 else -1 - 4 / L
def dAr : ℝ := if k then 0 else -4 / L
def dCr : ℝ := if k then -2 * (cap - 1 / 10000000) else -2 * B / L
def dUr (p : ℝ) : ℝ := -C0r B L cap k p + (1 - p) * dCr B L cap k
def dJr (δ p : ℝ) : ℝ := V δ * dDr L k + δ * (-Ar L k p + (1 - p) * dAr L k)

def guard (δ p : ℝ) : Fin 15 → ℝ :=
  ![Dr L k p, Ar L k p, C0r B L cap k p, Jr L k δ p, Tr B L cap k δ p - Jr L k δ p,
    (12499 / 10000) * Jr L k δ p - Tr B L cap k δ p,
    RNr B L cap k δ p - (23 / 37) * DJr L k δ p, DJr L k δ p - RNr B L cap k δ p,
    MNr B L cap k δ p - lowerMr B L cap k * DJr L k δ p,
    upperMr B L cap k * DJr L k δ p - MNr B L cap k δ p,
    Nr B L cap k δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * Jr L k δ p,
    Ur B L cap k p * dJr L k δ p - dUr B L cap k p * Jr L k δ p,
    11 / 25 - naturalM - 1 / 10000000,
    B - 2 * naturalM - L * (sMinus + 1 / 10000000) - 2 / 10000000,
    if k then (cap - 1 / 10000000 - sMinus - 1 / 10000000) * DJr L k δ p else 1]

end
end R

/-- `admissionGuard` of a non-old branch is the mirror at the branch data (definitional). -/
theorem admissionGuard_eq (b : CountBranch) (hb : b ≠ .old) (δ p : ℝ) (j : Fin 15) :
    admissionGuard b δ p j =
      R.guard (branchB b) (branchL b) (branchCap b) (isCap b) δ p j := by
  cases b
  · exact (hb rfl).elim
  all_goals rfl

/-! ### The parametric evaluation lemma -/

section
variable (b : BranchQ) (δ p : ℝ)

local notation "Bq" => ((b.B : ℚ) : ℝ)
local notation "Lq" => ((b.L : ℚ) : ℝ)
local notation "Kq" => ((b.cap : ℚ) : ℝ)

theorem ev_Vq : Q2.ev BranchQ.Vq δ p = V δ := by
  simp [BranchQ.Vq, Q2.ev_sub, V]

theorem ev_Dq : Q2.ev b.Dq δ p = R.Dr Lq b.capped p := by
  unfold BranchQ.Dq R.Dr
  cases b.capped <;> simp [Q2.ev_sub, Q2.ev_smul] <;> ring

theorem ev_Aq : Q2.ev b.Aq δ p = R.Ar Lq b.capped p := by
  unfold BranchQ.Aq R.Ar
  cases b.capped <;> simp [Q2.ev_sub, Q2.ev_smul] <;> ring

theorem ev_C0q : Q2.ev b.C0q δ p = R.C0r Bq Lq Kq b.capped p := by
  unfold BranchQ.C0q R.C0r BranchQ.Zc etaQ
  cases b.capped <;> simp [Q2.ev_sub, Q2.ev_smul] <;> ring

theorem ev_Zq : Q2.ev b.Zq δ p = R.Zr Bq Lq Kq b.capped p := by
  unfold BranchQ.Zq R.Zr BranchQ.Zc etaQ
  cases b.capped <;> simp [Q2.ev_smul] <;> ring

theorem ev_Uq : Q2.ev b.Uq δ p = R.Ur Bq Lq Kq b.capped p := by
  simp [BranchQ.Uq, R.Ur, Q2.ev_mul, Q2.ev_sub, ev_C0q]

theorem ev_Jq : Q2.ev b.Jq δ p = R.Jr Lq b.capped δ p := by
  simp [BranchQ.Jq, R.Jr, Q2.ev_add, Q2.ev_mul, Q2.ev_sub, ev_Vq, ev_Dq, ev_Aq]

theorem ev_Nq : Q2.ev b.Nq δ p = R.Nr Bq Lq Kq b.capped δ p := by
  simp [BranchQ.Nq, R.Nr, Q2.ev_add, Q2.ev_mul, Q2.ev_sub, ev_Vq, ev_Jq, ev_Uq]

theorem ev_Tq : Q2.ev b.Tq δ p = R.Tr Bq Lq Kq b.capped δ p := by
  simp [BranchQ.Tq, R.Tr, Q2.ev_add, Q2.ev_mul, ev_Jq, ev_Uq]

theorem ev_RNq : Q2.ev b.RNq δ p = R.RNr Bq Lq Kq b.capped δ p := by
  simp [BranchQ.RNq, R.RNr, Q2.ev_add, Q2.ev_mul, Q2.ev_sub, ev_Aq, ev_Tq, ev_Zq, ev_Jq]

theorem ev_MNq : Q2.ev b.MNq δ p = R.MNr Bq Lq Kq b.capped δ p := by
  simp [BranchQ.MNq, R.MNr, Q2.ev_mul, Q2.ev_sub, ev_Dq, ev_Tq, ev_RNq]

theorem ev_DJq : Q2.ev b.DJq δ p = R.DJr Lq b.capped δ p := by
  simp [BranchQ.DJq, R.DJr, Q2.ev_mul, ev_Dq, ev_Jq]

theorem ev_dUq : Q2.ev b.dUq δ p = R.dUr Bq Lq Kq b.capped p := by
  unfold BranchQ.dUq R.dUr BranchQ.dC R.dCr BranchQ.Zc etaQ
  rw [Q2.ev_add, Q2.ev_smul, Q2.ev_smul, ev_C0q]
  cases b.capped <;> simp [Q2.ev_sub] <;> ring

theorem ev_dJq : Q2.ev b.dJq δ p = R.dJr Lq b.capped δ p := by
  unfold BranchQ.dJq R.dJr BranchQ.dD R.dDr BranchQ.dA R.dAr
  rw [Q2.ev_add, Q2.ev_smul, Q2.ev_mul, Q2.ev_add, Q2.ev_smul, Q2.ev_smul, ev_Vq, ev_Aq]
  cases b.capped <;> simp [Q2.ev_sub] <;> ring

theorem cast_naturalMQ : ((naturalMQ : ℚ) : ℝ) = naturalM := by
  norm_num [naturalMQ, naturalKQ, sMinusQ, naturalM, naturalK, sMinus]

theorem cast_lowerM : ((b.lowerM : ℚ) : ℝ) = R.lowerMr Bq Lq Kq b.capped := by
  unfold BranchQ.lowerM R.lowerMr
  cases b.capped <;> simp [mMinusQ, etaQ, mMinus]

theorem cast_upperM : ((b.upperM : ℚ) : ℝ) = R.upperMr Bq Lq Kq b.capped := by
  unfold BranchQ.upperM R.upperMr BranchQ.Zc
  have h1 : ((naturalMQ : ℚ) : ℝ) = naturalM := cast_naturalMQ
  cases b.capped <;> simp [etaQ, sMinusQ, sMinus, h1]

/-- **The parametric admission lemma**: for every rational face `(B, Λ, cap)` and both pieces of the
plain curve, the computable guard polynomial evaluates to the guard of `Formulas.lean`. -/
theorem ev_guard (j : Fin 15) :
    Q2.ev (b.guard j) δ p = R.guard Bq Lq Kq b.capped δ p j := by
  have hM : ((naturalMQ : ℚ) : ℝ) = naturalM := cast_naturalMQ
  have hs : ((sMinusQ : ℚ) : ℝ) = sMinus := by norm_num [sMinusQ, sMinus]
  have he : ((etaQ : ℚ) : ℝ) = 1 / 10000000 := by norm_num [etaQ]
  fin_cases j
  · exact ev_Dq b δ p
  · exact ev_Aq b δ p
  · exact ev_C0q b δ p
  · exact ev_Jq b δ p
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, ev_Tq, ev_Jq]
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, Q2.ev_smul, ev_Tq, ev_Jq]
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, Q2.ev_smul, ev_RNq, ev_DJq]
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, ev_RNq, ev_DJq]
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, Q2.ev_smul, ev_MNq, ev_DJq, cast_lowerM]
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, Q2.ev_smul, ev_MNq, ev_DJq, cast_upperM]
  · show Q2.ev (Q2.sub b.Nq (Q2.mul (Q2.sub (Q2.sub (Q2.C 1) (Q2.smul (2 * naturalMQ) Q2.X))
        (Q2.smul (2 * sMinusQ) (Q2.mul Q2.X Q2.Y))) b.Jq)) δ p =
      R.Nr Bq Lq Kq b.capped δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * R.Jr Lq b.capped δ p
    rw [Q2.ev_sub, Q2.ev_mul, Q2.ev_sub, Q2.ev_sub, Q2.ev_smul, Q2.ev_smul, Q2.ev_mul, ev_Nq, ev_Jq]
    simp only [Q2.ev_C, Q2.ev_X, Q2.ev_Y]
    push_cast; rw [hM, hs]; ring
  · simp [BranchQ.guard, R.guard, Q2.ev_sub, Q2.ev_mul, ev_Uq, ev_dJq, ev_dUq, ev_Jq]
  · simp [BranchQ.guard, R.guard, hM, he]
  · show Q2.ev (Q2.C (b.B - 2 * naturalMQ - b.L * (sMinusQ + etaQ) - 2 * etaQ)) δ p =
      Bq - 2 * naturalM - Lq * (sMinus + 1 / 10000000) - 2 / 10000000
    rw [Q2.ev_C]; push_cast; rw [hM, hs, he]; ring
  · simp only [BranchQ.guard, R.guard]
    cases hk : b.capped
    · simp
    · simp [Q2.ev_smul, ev_DJq, hk, BranchQ.Zc, he, hs]

end

/-- A passed kernel check certifies all fifteen guards on the window. -/
theorem window_admitted (b : BranchQ) (k : ℕ) (dlo dhi plo : ℚ) (h : windowCheck b k dlo dhi plo = true)
    {δ p : ℝ} (hδ : δ ∈ Set.Icc (dlo : ℝ) dhi) (hp : p ∈ Set.Icc (plo : ℝ) (1 / 2)) (j : Fin 15) :
    0 < R.guard b.B b.L b.cap b.capped δ p j := by
  rw [← ev_guard]
  simp only [windowCheck, List.all_eq_true, List.mem_finRange, true_implies] at h
  exact posBox_sound _ k dlo dhi plo (1 / 2) (h j) hδ.1 hδ.2 hp.1 (by simpa using hp.2)

end QRH.ArviReturnTuning
