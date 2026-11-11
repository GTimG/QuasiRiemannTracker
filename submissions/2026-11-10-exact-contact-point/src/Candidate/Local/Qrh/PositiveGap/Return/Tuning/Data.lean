import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Guards
import Candidate.Local.Qrh.PositiveGap.Return.Constants
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000
namespace QRH.PositiveGap.ReturnTuning
open QRH.PositiveGap.Return QRH.ArviReturnTuning
def cQ : ℚ := 1266181 / 10000000
def hQ : ℚ := 2 * (5028 * cQ - 199) / 1081
def reserveQ : ℚ := 0
def countBQ : ℚ := 1
def countLQ : ℚ := 2
def countCapQ : ℚ := 671447 / 5000000
def physBQ : ℚ := 1
def physLQ : ℚ := 2
def physCapQ : ℚ := 3 / 25
def numCapQ : ℚ := 3 / 40
def dmQ : ℚ := 19 / 25
def thetaQ : ℚ := 1 - cQ
def ellQ : ℚ := 4 * cQ - 1 / 3
def yQ : ℚ := hQ - 2 * ellQ
def kappaQ : ℚ := 1 - 2 * cQ
def dpQ : ℚ := hQ
def d0Q : ℚ := 1 / 200
def oldCapQ (d : ℚ) : ℚ := min d (2 * yQ - d) / (6 * kappaQ)
def newCapQ (d : ℚ) : ℚ := min (numCapQ * d) ((2 * yQ - (2 - physBQ) * d) / physLQ)
def edgeDQ : Edge → ℚ
  | .oldSmall => d0Q
  | .oldSwitch | .newSwitch => dmQ
  | .newTop => dpQ
def edgeCQ (e : Edge) : ℚ :=
  match e with
  | .oldSmall | .oldSwitch => oldCapQ (edgeDQ e)
  | .newSwitch | .newTop => newCapQ (edgeDQ e)
def toQ : CountBranch → BranchQ
  | .C => ⟨countBQ, countLQ, countCapQ, false⟩
  | .capC => ⟨countBQ, countLQ, countCapQ, true⟩
  | .weakC7 => ⟨countBQ - 7 / 4000, countLQ, countCapQ, false⟩
  | .capP => ⟨physBQ, physLQ, physCapQ, true⟩
  | .old => ⟨0, 1, 1 / 25, false⟩
def Close (d x y : ℝ) : Prop := -d ≤ x - y ∧ x - y ≤ d
lemma close_refl (x : ℝ) : Close 0 x x := ⟨by linarith, by linarith⟩
lemma close_mono {d1 d2 x y : ℝ} (h : Close d1 x y) (hd : d1 ≤ d2) : Close d2 x y :=
  ⟨by linarith [h.1], by linarith [h.2]⟩
lemma close_add {d1 d2 x1 y1 x2 y2 : ℝ} (h1 : Close d1 x1 y1) (h2 : Close d2 x2 y2) :
    Close (d1 + d2) (x1 + x2) (y1 + y2) :=
  ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
lemma close_sub {d1 d2 x1 y1 x2 y2 : ℝ} (h1 : Close d1 x1 y1) (h2 : Close d2 x2 y2) :
    Close (d1 + d2) (x1 - x2) (y1 - y2) :=
  ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
lemma close_smul {c d x y : ℝ} (hc : 0 ≤ c) (h : Close d x y) :
    Close (c * d) (c * x) (c * y) :=
  ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
lemma close_mul {da db A B a1 a0 b1 b0 : ℝ}
    (hA : -A ≤ a1 ∧ a1 ≤ A) (hB : -B ≤ b0 ∧ b0 ≤ B)
    (ha : Close da a1 a0) (hb : Close db b1 b0) :
    Close (A * db + da * B) (a1 * b1) (a0 * b0) :=
  ⟨by nlinarith [hA.1, hA.2, hB.1, hB.2, ha.1, ha.2, hb.1, hb.2],
   by nlinarith [hA.1, hA.2, hB.1, hB.2, ha.1, ha.2, hb.1, hb.2]⟩
noncomputable section
variable [TargetC]
def tParam : ℝ := eps / (2 + 10 * eps)
lemma hL_pos : (0 : ℝ) < 2 + 10 * eps := by linarith [eps_pos]
lemma tParam_pos : 0 < tParam := div_pos eps_pos hL_pos
lemma tParam_le : tParam ≤ eps / 2 := by
  unfold tParam
  rw [div_le_div_iff₀ hL_pos (by norm_num)]
  nlinarith [eps_pos]
lemma tParam_le_num : tParam ≤ 1 / 2000000000 := by
  linarith [tParam_le, eps_le]
lemma div_L_eq (x : ℝ) : x / (2 + 10 * eps) = x / 2 - 5 * x * tParam := by
  unfold tParam
  have hL : (2 + 10 * eps : ℝ) ≠ 0 := hL_pos.ne'
  apply mul_right_cancel₀ hL
  rw [div_mul_cancel₀ _ hL, sub_mul, mul_assoc, div_mul_cancel₀ _ hL]
  ring
lemma B_div_L_eq (x : ℝ) : x * (1 - eps) / (2 + 10 * eps) = x / 2 - 6 * x * tParam := by
  unfold tParam
  have hL : (2 + 10 * eps : ℝ) ≠ 0 := hL_pos.ne'
  apply mul_right_cancel₀ hL
  rw [div_mul_cancel₀ _ hL, sub_mul, mul_assoc, div_mul_cancel₀ _ hL]
  ring
lemma Dr_false_eq (p : ℝ) : R.Dr (2 + 10 * eps) false p = R.Dr 2 false p + 20 * p * tParam := by
  unfold R.Dr; simp only [Bool.false_eq_true, ↓reduceIte, div_L_eq]; ring
lemma Ar_false_eq (p : ℝ) : R.Ar (2 + 10 * eps) false p = R.Ar 2 false p + 20 * p * tParam := by
  unfold R.Ar; simp only [Bool.false_eq_true, ↓reduceIte, div_L_eq]; ring
lemma C0r_false_eq (cap p : ℝ) :
    R.C0r (1 - eps) (2 + 10 * eps) cap false p = R.C0r 1 2 cap false p + 12 * p * tParam := by
  unfold R.C0r; simp only [Bool.false_eq_true, ↓reduceIte, B_div_L_eq]; ring
lemma Zr_false_eq (cap p : ℝ) :
    R.Zr (1 - eps) (2 + 10 * eps) cap false p = R.Zr 1 2 cap false p - 12 * p * tParam := by
  unfold R.Zr; simp only [Bool.false_eq_true, ↓reduceIte, B_div_L_eq]; ring
lemma Ur_false_eq (cap p : ℝ) :
    R.Ur (1 - eps) (2 + 10 * eps) cap false p = R.Ur 1 2 cap false p + 12 * p * (1 - p) * tParam := by
  unfold R.Ur; rw [C0r_false_eq]; ring
lemma Jr_false_eq (δ p : ℝ) :
    R.Jr (2 + 10 * eps) false δ p = R.Jr 2 false δ p + 20 * p * (V δ + δ * (1 - p)) * tParam := by
  unfold R.Jr; rw [Dr_false_eq, Ar_false_eq]; ring
lemma Nr_false_eq (cap δ p : ℝ) :
    R.Nr (1 - eps) (2 + 10 * eps) cap false δ p =
      R.Nr 1 2 cap false δ p +
        ((1 - δ) * 20 * p * (V δ + δ * (1 - p)) + V δ * δ * 12 * p * (1 - p)) * tParam := by
  unfold R.Nr; rw [Jr_false_eq, Ur_false_eq]; ring
lemma dDr_false_eq : R.dDr (2 + 10 * eps) false = R.dDr 2 false + 20 * tParam := by
  unfold R.dDr; simp only [Bool.false_eq_true, ↓reduceIte, div_L_eq]; ring
lemma dAr_false_eq : R.dAr (2 + 10 * eps) false = R.dAr 2 false + 20 * tParam := by
  unfold R.dAr; simp only [Bool.false_eq_true, ↓reduceIte, div_L_eq]; ring
lemma dCr_false_eq (cap : ℝ) :
    R.dCr (1 - eps) (2 + 10 * eps) cap false = R.dCr 1 2 cap false + 12 * tParam := by
  unfold R.dCr; simp only [Bool.false_eq_true, ↓reduceIte, B_div_L_eq]; ring
lemma dUr_false_eq (cap p : ℝ) :
    R.dUr (1 - eps) (2 + 10 * eps) cap false p = R.dUr 1 2 cap false p + 12 * (1 - 2 * p) * tParam := by
  unfold R.dUr; rw [C0r_false_eq, dCr_false_eq]; ring
lemma dJr_false_eq (δ p : ℝ) :
    R.dJr (2 + 10 * eps) false δ p = R.dJr 2 false δ p + 20 * (V δ + δ * (1 - 2 * p)) * tParam := by
  unfold R.dJr; rw [dDr_false_eq, Ar_false_eq, dAr_false_eq]; ring
lemma lowerMr_C_eq :
    R.lowerMr (1 - eps) (2 + 10 * eps) countCap false =
      R.lowerMr 1 2 countCap false - (2342893 / 2000000) * eps := by
  unfold R.lowerMr mMinus countCap
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : max (3 / 10 + 1 / 10000000 : ℝ) ((1 - eps - (2 + 10 * eps) * (671447 / 5000000 - 1 / 10000000)) / 2 + 1 / 10000000) =
      (1 - eps - (2 + 10 * eps) * (671447 / 5000000 - 1 / 10000000)) / 2 + 1 / 10000000 :=
    max_eq_right (by linarith [eps_le])
  have h2 : max (3 / 10 + 1 / 10000000 : ℝ) ((1 - 2 * (671447 / 5000000 - 1 / 10000000)) / 2 + 1 / 10000000) =
      (1 - 2 * (671447 / 5000000 - 1 / 10000000)) / 2 + 1 / 10000000 :=
    max_eq_right (by norm_num)
  rw [h1, h2]
  ring
lemma upperMr_C_eq :
    R.upperMr (1 - eps) (2 + 10 * eps) countCap false = R.upperMr 1 2 countCap false := by
  unfold R.upperMr naturalM naturalK sMinus
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h1 : min (min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000))
      ((1 - eps - (2 + 10 * eps) * (27 / 1000 + 1 / 10000000)) / 2 - 1 / 10000000) =
      min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000) :=
    min_eq_left (by norm_num; linarith [eps_le])
  have h2 : min (min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000))
      ((1 - 2 * (27 / 1000 + 1 / 10000000)) / 2 - 1 / 10000000) =
      min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000) :=
    min_eq_left (by norm_num)
  rw [h1, h2]
lemma upperMr_capP_eq :
    R.upperMr (1 - eps) (2 + 10 * eps) physicalCap true =
      R.upperMr 1 2 physicalCap true - (2199999 / 2000000) * eps := by
  unfold R.upperMr naturalM naturalK sMinus physicalCap
  simp only [↓reduceIte]
  have h1 : min (min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000))
      ((1 - eps - (2 + 10 * eps) * (3 / 25 - 1 / 10000000)) / 2 - 1 / 10000000) =
      (1 - eps - (2 + 10 * eps) * (3 / 25 - 1 / 10000000)) / 2 - 1 / 10000000 :=
    min_eq_right (by norm_num; linarith [eps_pos])
  have h2 : min (min (11 / 25 - 1 / 10000000 : ℝ) ((1 - 9 / 2 * (27 / 1000)) / 2 - 1 / 10000000))
      ((1 - 2 * (3 / 25 - 1 / 10000000)) / 2 - 1 / 10000000) =
      (1 - 2 * (3 / 25 - 1 / 10000000)) / 2 - 1 / 10000000 :=
    min_eq_right (by norm_num)
  rw [h1, h2]
  ring
lemma Jr_close (k : Bool) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Close (10 * tParam) (R.Jr (2 + 10 * eps) k δ p) (R.Jr 2 k δ p) := by
  have ht0 := tParam_pos
  cases k
  · have hEq := Jr_false_eq δ p
    have hV : V δ + δ * (1 - p) = 5 / 6 - δ * p := by unfold V; ring
    have hdp0 : 0 ≤ δ * p := mul_nonneg hδ.1 hp.1
    have hdp1 : δ * p ≤ 3 / 8 := by nlinarith [hδ.1, hδ.2, hp.1, hp.2]
    have hJ : 0 ≤ 20 * p * (V δ + δ * (1 - p)) ∧ 20 * p * (V δ + δ * (1 - p)) ≤ 10 := by
      rw [hV]; constructor <;> nlinarith [hp.1, hp.2, hdp0, hdp1]
    constructor <;> nlinarith [hEq, hJ.1, hJ.2, ht0]
  · unfold R.Jr R.Dr R.Ar
    simp only [↓reduceIte]
    exact ⟨by nlinarith [ht0], by nlinarith [ht0]⟩
lemma Nr_close (cap : ℝ) (k : Bool) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Close (15 * tParam) (R.Nr (1 - eps) (2 + 10 * eps) cap k δ p) (R.Nr 1 2 cap k δ p) := by
  have ht0 := tParam_pos
  cases k
  · have hEq := Nr_false_eq cap δ p
    have hV : V δ + δ * (1 - p) = 5 / 6 - δ * p := by unfold V; ring
    have hdp0 : 0 ≤ δ * p := mul_nonneg hδ.1 hp.1
    have hdp1 : δ * p ≤ 3 / 8 := by nlinarith [hδ.1, hδ.2, hp.1, hp.2]
    have hp2 : 0 ≤ p * (1 - p) ∧ p * (1 - p) ≤ 1 / 4 :=
      ⟨mul_nonneg hp.1 (by linarith [hp.2]), by nlinarith [sq_nonneg (p - 1 / 2)]⟩
    have hJ : 0 ≤ p * (V δ + δ * (1 - p)) ∧ p * (V δ + δ * (1 - p)) ≤ 1 / 2 := by
      rw [hV]; constructor <;> nlinarith [hp.1, hp.2, hdp0, hdp1]
    have hVd : 0 ≤ V δ * δ ∧ V δ * δ ≤ 1 := by
      unfold V; constructor <;> nlinarith [hδ.1, hδ.2]
    have h1 : 0 ≤ (1 - δ) * 20 * p * (V δ + δ * (1 - p)) ∧
        (1 - δ) * 20 * p * (V δ + δ * (1 - p)) ≤ 10 := by
      have : (1 - δ) * 20 * p * (V δ + δ * (1 - p)) = 20 * (1 - δ) * (p * (V δ + δ * (1 - p))) := by ring
      rw [this]; constructor <;> nlinarith [hδ.1, hδ.2, hJ.1, hJ.2]
    have h2 : 0 ≤ V δ * δ * 12 * p * (1 - p) ∧ V δ * δ * 12 * p * (1 - p) ≤ 5 := by
      have : V δ * δ * 12 * p * (1 - p) = 12 * (V δ * δ) * (p * (1 - p)) := by ring
      rw [this]; constructor <;> nlinarith [hVd.1, hVd.2, hp2.1, hp2.2]
    constructor <;> nlinarith [hEq, h1.1, h1.2, h2.1, h2.2, ht0]
  · unfold R.Nr R.Jr R.Dr R.Ar R.Ur R.C0r
    simp only [↓reduceIte]
    exact ⟨by nlinarith [ht0], by nlinarith [ht0]⟩
omit [TargetC] in
lemma Jr_0_bounds {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    -3 ≤ R.Jr 2 false δ p ∧ R.Jr 2 false δ p ≤ 3 := by
  have hEq : R.Jr 2 false δ p = (1 - p) * (5 / 2 - δ - 2 * (δ * p)) := by
    unfold R.Jr R.Dr R.Ar V; simp only [Bool.false_eq_true, ↓reduceIte]; ring
  have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 := ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
  rw [hEq]; constructor <;> nlinarith [hδ.1, hδ.2, hp.1, hp.2, hdp.1, hdp.2]
omit [TargetC] in
lemma Jr_true_bounds {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    -3 ≤ R.Jr 2 true δ p ∧ R.Jr 2 true δ p ≤ 3 := by
  have hEq : R.Jr 2 true δ p = 5 / 2 - δ - 5 / 6 * p - δ * p := by
    unfold R.Jr R.Dr R.Ar V; simp only [↓reduceIte]; ring
  have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 := ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
  rw [hEq]; constructor <;> linarith [hδ.1, hδ.2, hp.1, hp.2, hdp.1, hdp.2]
omit [TargetC] in
lemma dJr_0_bounds {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    -6 ≤ R.dJr 2 false δ p ∧ R.dJr 2 false δ p ≤ 6 := by
  have hEq : R.dJr 2 false δ p = -(5 / 2 + δ - 4 * (δ * p)) := by
    unfold R.dJr R.dDr R.Ar R.dAr V; simp only [Bool.false_eq_true, ↓reduceIte]; ring
  have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 := ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
  rw [hEq]; constructor <;> linarith [hδ.1, hδ.2, hdp.1, hdp.2]
lemma guard_C_close {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Close (10 * tParam) (R.Dr (2 + 10 * eps) false p) (R.Dr 2 false p) ∧
    Close (10 * tParam) (R.Ar (2 + 10 * eps) false p) (R.Ar 2 false p) ∧
    Close (6 * tParam) (R.C0r (1 - eps) (2 + 10 * eps) countCap false p) (R.C0r 1 2 countCap false p) ∧
    Close (6 * tParam) (R.Ur (1 - eps) (2 + 10 * eps) countCap false p) (R.Ur 1 2 countCap false p) ∧
    Close (15 * tParam) (R.Tr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.Tr 1 2 countCap false δ p) ∧
    Close (70 * tParam) (R.DJr (2 + 10 * eps) false δ p) (R.DJr 2 false δ p) ∧
    (-10 ≤ R.DJr (2 + 10 * eps) false δ p ∧ R.DJr (2 + 10 * eps) false δ p ≤ 10) ∧
    Close (113 * tParam) (R.RNr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.RNr 1 2 countCap false δ p) ∧
    Close (213 * tParam) (R.MNr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.MNr 1 2 countCap false δ p) ∧
    Close (12 * tParam) (R.dUr (1 - eps) (2 + 10 * eps) countCap false p) (R.dUr 1 2 countCap false p) ∧
    Close (20 * tParam) (R.dJr (2 + 10 * eps) false δ p) (R.dJr 2 false δ p) := by
  have ht0 := tParam_pos
  have ht1 := tParam_le_num
  have hD0 : -4 ≤ R.Dr (2 + 10 * eps) false p ∧ R.Dr (2 + 10 * eps) false p ≤ 4 := by
    rw [Dr_false_eq]; unfold R.Dr; simp only [Bool.false_eq_true, ↓reduceIte]
    constructor <;> nlinarith [hp.1, hp.2, ht0, ht1]
  have hD_0 : -3 ≤ R.Dr 2 false p ∧ R.Dr 2 false p ≤ 3 := by
    unfold R.Dr; simp only [Bool.false_eq_true, ↓reduceIte]; constructor <;> linarith [hp.1, hp.2]
  have hDc : Close (10 * tParam) (R.Dr (2 + 10 * eps) false p) (R.Dr 2 false p) := by
    rw [Dr_false_eq]; constructor <;> nlinarith [hp.1, hp.2, ht0]
  have hA0 : -3 ≤ R.Ar (2 + 10 * eps) false p ∧ R.Ar (2 + 10 * eps) false p ≤ 3 := by
    rw [Ar_false_eq]; unfold R.Ar; simp only [Bool.false_eq_true, ↓reduceIte]
    constructor <;> nlinarith [hp.1, hp.2, ht0, ht1]
  have hAc : Close (10 * tParam) (R.Ar (2 + 10 * eps) false p) (R.Ar 2 false p) := by
    rw [Ar_false_eq]; constructor <;> nlinarith [hp.1, hp.2, ht0]
  have hC0c : Close (6 * tParam) (R.C0r (1 - eps) (2 + 10 * eps) countCap false p) (R.C0r 1 2 countCap false p) := by
    rw [C0r_false_eq]; constructor <;> nlinarith [hp.1, hp.2, ht0]
  have hUc : Close (6 * tParam) (R.Ur (1 - eps) (2 + 10 * eps) countCap false p) (R.Ur 1 2 countCap false p) := by
    rw [Ur_false_eq]
    have hp2 : 0 ≤ p * (1 - p) ∧ p * (1 - p) ≤ 1 / 2 := ⟨mul_nonneg hp.1 (by linarith [hp.2]), by nlinarith [hp.1, hp.2]⟩
    constructor <;> nlinarith [hp2.1, hp2.2, ht0]
  have hJc := Jr_close false hδ hp
  have hJ_0 := Jr_0_bounds hδ hp
  have hT_0 : -4 ≤ R.Tr 1 2 countCap false δ p ∧ R.Tr 1 2 countCap false δ p ≤ 4 := by
    unfold R.Tr R.Ur R.C0r; simp only [Bool.false_eq_true, ↓reduceIte]
    have hp2 : 0 ≤ (1 - p) * (1 - p) ∧ (1 - p) * (1 - p) ≤ 1 := ⟨by nlinarith [hp.2], by nlinarith [hp.1, hp.2]⟩
    constructor <;> nlinarith [hJ_0.1, hJ_0.2, hδ.1, hδ.2, hp2.1, hp2.2]
  have hTc : Close (15 * tParam) (R.Tr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.Tr 1 2 countCap false δ p) := by
    unfold R.Tr
    exact close_mono (close_add hJc (close_smul hδ.1 hUc)) (by nlinarith [hδ.2, ht0])
  have hDJc : Close (70 * tParam) (R.DJr (2 + 10 * eps) false δ p) (R.DJr 2 false δ p) := by
    unfold R.DJr
    exact close_mono (close_mul hD0 hJ_0 hDc hJc) (by linarith)
  have hDJ_0 : -9 ≤ R.DJr 2 false δ p ∧ R.DJr 2 false δ p ≤ 9 := by
    unfold R.DJr; constructor <;> nlinarith [hD_0.1, hD_0.2, hJ_0.1, hJ_0.2]
  have hDJ0 : -10 ≤ R.DJr (2 + 10 * eps) false δ p ∧ R.DJr (2 + 10 * eps) false δ p ≤ 10 :=
    ⟨by linarith [hDJc.1, hDJ_0.1, ht1], by linarith [hDJc.2, hDJ_0.2, ht1]⟩
  have hZ0 : -1 ≤ R.Zr (1 - eps) (2 + 10 * eps) countCap false p - p ∧ R.Zr (1 - eps) (2 + 10 * eps) countCap false p - p ≤ 1 := by
    rw [Zr_false_eq]; unfold R.Zr; simp only [Bool.false_eq_true, ↓reduceIte]
    constructor <;> nlinarith [hp.1, hp.2, ht0, ht1]
  have hZc : Close (6 * tParam) (R.Zr (1 - eps) (2 + 10 * eps) countCap false p - p) (R.Zr 1 2 countCap false p - p) := by
    rw [Zr_false_eq]; constructor <;> nlinarith [hp.1, hp.2, ht0]
  have hRNc : Close (113 * tParam) (R.RNr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.RNr 1 2 countCap false δ p) := by
    unfold R.RNr
    exact close_mono (close_add (close_mul hA0 hT_0 hAc hTc) (close_mul hZ0 hJ_0 hZc hJc)) (by linarith)
  have hMNc : Close (213 * tParam) (R.MNr (1 - eps) (2 + 10 * eps) countCap false δ p) (R.MNr 1 2 countCap false δ p) := by
    unfold R.MNr
    exact close_mono (close_sub (close_mul hD0 hT_0 hDc hTc) hRNc) (by linarith)
  have hdUc : Close (12 * tParam) (R.dUr (1 - eps) (2 + 10 * eps) countCap false p) (R.dUr 1 2 countCap false p) := by
    rw [dUr_false_eq]; constructor <;> nlinarith [hp.1, hp.2, ht0]
  have hdJc : Close (20 * tParam) (R.dJr (2 + 10 * eps) false δ p) (R.dJr 2 false δ p) := by
    rw [dJr_false_eq]
    have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 := ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
    have h1 : 0 ≤ V δ + δ * (1 - 2 * p) ∧ V δ + δ * (1 - 2 * p) ≤ 1 := by
      unfold V; constructor <;> linarith [hδ.1, hδ.2, hdp.1, hdp.2]
    constructor <;> nlinarith [h1.1, h1.2, ht0]
  exact ⟨hDc, hAc, hC0c, hUc, hTc, hDJc, hDJ0, hRNc, hMNc, hdUc, hdJc⟩
theorem guard_ge (b : CountBranch) (hb : b = .C ∨ b = .capP) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) (j : Fin 15) :
    R.guard ((toQ b).B : ℝ) ((toQ b).L : ℝ) ((toQ b).cap : ℝ) (toQ b).capped δ p j - 1 / 1000000 ≤
      admissionGuard b δ p j := by
  have hne : b ≠ .old := by rcases hb with rfl | rfl <;> decide
  rw [admissionGuard_eq b hne]
  have ht0 := tParam_pos
  have ht1 := tParam_le_num
  have he0 := eps_pos
  have he1 := eps_le
  rcases hb with rfl | rfl
  · have hcast : R.guard ((toQ CountBranch.C).B : ℝ) ((toQ CountBranch.C).L : ℝ) ((toQ CountBranch.C).cap : ℝ) (toQ CountBranch.C).capped δ p j =
        R.guard 1 2 countCap false δ p j := by
      congr 1 <;> norm_num [toQ, countBQ, countLQ, countCapQ, countCap]
    rw [hcast]
    change R.guard 1 2 countCap false δ p j - 1 / 1000000 ≤
      R.guard (1 - eps) (2 + 10 * eps) countCap false δ p j
    obtain ⟨hDc, hAc, hC0c, hUc, hTc, hDJc, hDJ0, hRNc, hMNc, hdUc, hdJc⟩ := guard_C_close hδ hp
    have hJc := Jr_close false hδ hp
    have hNc := Nr_close countCap false hδ hp
    fin_cases j
    · show R.Dr 2 false p - 1 / 1000000 ≤ R.Dr (2 + 10 * eps) false p
      linarith [hDc.1, ht1]
    · show R.Ar 2 false p - 1 / 1000000 ≤ R.Ar (2 + 10 * eps) false p
      linarith [hAc.1, ht1]
    · show R.C0r 1 2 countCap false p - 1 / 1000000 ≤ R.C0r (1 - eps) (2 + 10 * eps) countCap false p
      linarith [hC0c.1, ht1]
    · show R.Jr 2 false δ p - 1 / 1000000 ≤ R.Jr (2 + 10 * eps) false δ p
      linarith [hJc.1, ht1]
    · show (R.Tr 1 2 countCap false δ p - R.Jr 2 false δ p) - 1 / 1000000 ≤
        R.Tr (1 - eps) (2 + 10 * eps) countCap false δ p - R.Jr (2 + 10 * eps) false δ p
      linarith [hTc.1, hJc.2, ht1]
    · show ((12499 / 10000) * R.Jr 2 false δ p - R.Tr 1 2 countCap false δ p) - 1 / 1000000 ≤
        (12499 / 10000) * R.Jr (2 + 10 * eps) false δ p - R.Tr (1 - eps) (2 + 10 * eps) countCap false δ p
      linarith [hJc.1, hTc.2, ht1]
    · show (R.RNr 1 2 countCap false δ p - (23 / 37) * R.DJr 2 false δ p) - 1 / 1000000 ≤
        R.RNr (1 - eps) (2 + 10 * eps) countCap false δ p - (23 / 37) * R.DJr (2 + 10 * eps) false δ p
      linarith [hRNc.1, hDJc.2, ht1]
    · show (R.DJr 2 false δ p - R.RNr 1 2 countCap false δ p) - 1 / 1000000 ≤
        R.DJr (2 + 10 * eps) false δ p - R.RNr (1 - eps) (2 + 10 * eps) countCap false δ p
      linarith [hDJc.1, hRNc.2, ht1]
    · show (R.MNr 1 2 countCap false δ p - R.lowerMr 1 2 countCap false * R.DJr 2 false δ p) - 1 / 1000000 ≤
        R.MNr (1 - eps) (2 + 10 * eps) countCap false δ p - R.lowerMr (1 - eps) (2 + 10 * eps) countCap false * R.DJr (2 + 10 * eps) false δ p
      rw [lowerMr_C_eq]
      have hlo : R.lowerMr 1 2 countCap false = 3657108 / 10000000 := by
        unfold R.lowerMr mMinus countCap; norm_num
      rw [hlo]
      nlinarith [hMNc.1, hDJc.1, hDJc.2, hDJ0.1, hDJ0.2, ht1, he0, he1]
    · show (R.upperMr 1 2 countCap false * R.DJr 2 false δ p - R.MNr 1 2 countCap false δ p) - 1 / 1000000 ≤
        R.upperMr (1 - eps) (2 + 10 * eps) countCap false * R.DJr (2 + 10 * eps) false δ p - R.MNr (1 - eps) (2 + 10 * eps) countCap false δ p
      rw [upperMr_C_eq]
      have hup : R.upperMr 1 2 countCap false = 4392499 / 10000000 := by
        unfold R.upperMr naturalM naturalK sMinus; norm_num
      rw [hup]
      linarith [hDJc.1, hMNc.2, ht1]
    · show (R.Nr 1 2 countCap false δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * R.Jr 2 false δ p) - 1 / 1000000 ≤
        R.Nr (1 - eps) (2 + 10 * eps) countCap false δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * R.Jr (2 + 10 * eps) false δ p
      have hcoef : -1 ≤ 1 - 2 * δ * naturalM - 2 * δ * p * sMinus ∧ 1 - 2 * δ * naturalM - 2 * δ * p * sMinus ≤ 1 := by
        unfold naturalM naturalK sMinus
        have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 := ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
        constructor <;> linarith [hδ.1, hδ.2, hdp.1, hdp.2]
      have h1 := close_mul hcoef (Jr_0_bounds hδ hp) (close_refl _) hJc
      linarith [hNc.1, h1.2, ht1]
    · show (R.Ur 1 2 countCap false p * R.dJr 2 false δ p - R.dUr 1 2 countCap false p * R.Jr 2 false δ p) - 1 / 1000000 ≤
        R.Ur (1 - eps) (2 + 10 * eps) countCap false p * R.dJr (2 + 10 * eps) false δ p -
          R.dUr (1 - eps) (2 + 10 * eps) countCap false p * R.Jr (2 + 10 * eps) false δ p
      have hU0 : -2 ≤ R.Ur (1 - eps) (2 + 10 * eps) countCap false p ∧ R.Ur (1 - eps) (2 + 10 * eps) countCap false p ≤ 2 := by
        have hU_0 : -1 ≤ R.Ur 1 2 countCap false p ∧ R.Ur 1 2 countCap false p ≤ 1 := by
          unfold R.Ur R.C0r; simp only [Bool.false_eq_true, ↓reduceIte]
          constructor <;> nlinarith [hp.1, hp.2]
        exact ⟨by linarith [hUc.1, hU_0.1, ht1], by linarith [hUc.2, hU_0.2, ht1]⟩
      have hdU0 : -3 ≤ R.dUr (1 - eps) (2 + 10 * eps) countCap false p ∧ R.dUr (1 - eps) (2 + 10 * eps) countCap false p ≤ 3 := by
        rw [dUr_false_eq]; unfold R.dUr R.C0r R.dCr; simp only [Bool.false_eq_true, ↓reduceIte]
        constructor <;> nlinarith [hp.1, hp.2, ht0, ht1]
      have h1 := close_mul hU0 (dJr_0_bounds hδ hp) hUc hdJc
      have h2 := close_mul hdU0 (Jr_0_bounds hδ hp) hdUc hJc
      linarith [h1.1, h2.2, ht1]
    · show (11 / 25 - naturalM - 1 / 10000000) - 1 / 1000000 ≤ 11 / 25 - naturalM - 1 / 10000000
      linarith
    · show (1 - 2 * naturalM - 2 * (sMinus + 1 / 10000000) - 2 / 10000000) - 1 / 1000000 ≤
        (1 - eps) - 2 * naturalM - (2 + 10 * eps) * (sMinus + 1 / 10000000) - 2 / 10000000
      unfold sMinus; linarith [he1]
    · show (1 : ℝ) - 1 / 1000000 ≤ 1
      linarith
  · have hcast : R.guard ((toQ CountBranch.capP).B : ℝ) ((toQ CountBranch.capP).L : ℝ) ((toQ CountBranch.capP).cap : ℝ) (toQ CountBranch.capP).capped δ p j =
        R.guard 1 2 physicalCap true δ p j := by
      congr 1 <;> norm_num [toQ, physBQ, physLQ, physCapQ, physicalCap]
    rw [hcast]
    change R.guard 1 2 physicalCap true δ p j - 1 / 1000000 ≤
      R.guard (1 - eps) (2 + 10 * eps) physicalCap true δ p j
    fin_cases j
    · show R.Dr 2 true p - 1 / 1000000 ≤ R.Dr (2 + 10 * eps) true p
      unfold R.Dr; simp only [↓reduceIte]; linarith
    · show R.Ar 2 true p - 1 / 1000000 ≤ R.Ar (2 + 10 * eps) true p
      unfold R.Ar; simp only [↓reduceIte]; linarith
    · show R.C0r 1 2 physicalCap true p - 1 / 1000000 ≤ R.C0r (1 - eps) (2 + 10 * eps) physicalCap true p
      unfold R.C0r; simp only [↓reduceIte]; linarith
    · show R.Jr 2 true δ p - 1 / 1000000 ≤ R.Jr (2 + 10 * eps) true δ p
      unfold R.Jr R.Dr R.Ar; simp only [↓reduceIte]; linarith
    · show (R.Tr 1 2 physicalCap true δ p - R.Jr 2 true δ p) - 1 / 1000000 ≤
        R.Tr (1 - eps) (2 + 10 * eps) physicalCap true δ p - R.Jr (2 + 10 * eps) true δ p
      unfold R.Tr R.Jr R.Dr R.Ar R.Ur R.C0r; simp only [↓reduceIte]; linarith
    · show ((12499 / 10000) * R.Jr 2 true δ p - R.Tr 1 2 physicalCap true δ p) - 1 / 1000000 ≤
        (12499 / 10000) * R.Jr (2 + 10 * eps) true δ p - R.Tr (1 - eps) (2 + 10 * eps) physicalCap true δ p
      unfold R.Tr R.Jr R.Dr R.Ar R.Ur R.C0r; simp only [↓reduceIte]; linarith
    · show (R.RNr 1 2 physicalCap true δ p - (23 / 37) * R.DJr 2 true δ p) - 1 / 1000000 ≤
        R.RNr (1 - eps) (2 + 10 * eps) physicalCap true δ p - (23 / 37) * R.DJr (2 + 10 * eps) true δ p
      unfold R.RNr R.DJr R.Tr R.Jr R.Dr R.Ar R.Ur R.C0r R.Zr; simp only [↓reduceIte]; linarith
    · show (R.DJr 2 true δ p - R.RNr 1 2 physicalCap true δ p) - 1 / 1000000 ≤
        R.DJr (2 + 10 * eps) true δ p - R.RNr (1 - eps) (2 + 10 * eps) physicalCap true δ p
      unfold R.RNr R.DJr R.Tr R.Jr R.Dr R.Ar R.Ur R.C0r R.Zr; simp only [↓reduceIte]; linarith
    · show (R.MNr 1 2 physicalCap true δ p - R.lowerMr 1 2 physicalCap true * R.DJr 2 true δ p) - 1 / 1000000 ≤
        R.MNr (1 - eps) (2 + 10 * eps) physicalCap true δ p - R.lowerMr (1 - eps) (2 + 10 * eps) physicalCap true * R.DJr (2 + 10 * eps) true δ p
      unfold R.MNr R.RNr R.DJr R.Tr R.Jr R.Dr R.Ar R.Ur R.C0r R.Zr R.lowerMr; simp only [↓reduceIte]; linarith
    · show (R.upperMr 1 2 physicalCap true * R.DJr 2 true δ p - R.MNr 1 2 physicalCap true δ p) - 1 / 1000000 ≤
        R.upperMr (1 - eps) (2 + 10 * eps) physicalCap true * R.DJr (2 + 10 * eps) true δ p - R.MNr (1 - eps) (2 + 10 * eps) physicalCap true δ p
      rw [upperMr_capP_eq]
      have hMN : R.MNr (1 - eps) (2 + 10 * eps) physicalCap true δ p = R.MNr 1 2 physicalCap true δ p := rfl
      have hDJ : R.DJr (2 + 10 * eps) true δ p = R.DJr 2 true δ p := rfl
      rw [hMN, hDJ]
      have hDJ_hi : R.DJr 2 true δ p ≤ 12 := by
        have hJ := (Jr_true_bounds hδ hp).2
        have hD : 0 ≤ R.Dr 2 true p ∧ R.Dr 2 true p ≤ 3 := by
          unfold R.Dr; simp only [↓reduceIte]; constructor <;> linarith [hp.1, hp.2]
        unfold R.DJr; nlinarith [hD.1, hD.2, hJ, (Jr_true_bounds hδ hp).1]
      nlinarith [hDJ_hi, he0, he1]
    · show (R.Nr 1 2 physicalCap true δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * R.Jr 2 true δ p) - 1 / 1000000 ≤
        R.Nr (1 - eps) (2 + 10 * eps) physicalCap true δ p - (1 - 2 * δ * naturalM - 2 * δ * p * sMinus) * R.Jr (2 + 10 * eps) true δ p
      unfold R.Nr R.Jr R.Dr R.Ar R.Ur R.C0r; simp only [↓reduceIte]; linarith
    · show (R.Ur 1 2 physicalCap true p * R.dJr 2 true δ p - R.dUr 1 2 physicalCap true p * R.Jr 2 true δ p) - 1 / 1000000 ≤
        R.Ur (1 - eps) (2 + 10 * eps) physicalCap true p * R.dJr (2 + 10 * eps) true δ p -
          R.dUr (1 - eps) (2 + 10 * eps) physicalCap true p * R.Jr (2 + 10 * eps) true δ p
      unfold R.Ur R.dJr R.dUr R.Jr R.Dr R.Ar R.C0r R.dDr R.dAr R.dCr; simp only [↓reduceIte]; linarith
    · show (11 / 25 - naturalM - 1 / 10000000) - 1 / 1000000 ≤ 11 / 25 - naturalM - 1 / 10000000
      linarith
    · show (1 - 2 * naturalM - 2 * (sMinus + 1 / 10000000) - 2 / 10000000) - 1 / 1000000 ≤
        (1 - eps) - 2 * naturalM - (2 + 10 * eps) * (sMinus + 1 / 10000000) - 2 / 10000000
      unfold sMinus; linarith [he1]
    · show (if true then (physicalCap - 1 / 10000000 - sMinus - 1 / 10000000) * R.DJr 2 true δ p else 1) - 1 / 1000000 ≤
        if true then (physicalCap - 1 / 10000000 - sMinus - 1 / 10000000) * R.DJr (2 + 10 * eps) true δ p else 1
      have hDJ : R.DJr (2 + 10 * eps) true δ p = R.DJr 2 true δ p := rfl
      rw [hDJ]; simp only [↓reduceIte]; linarith
theorem admission_of_check (b : CountBranch) (hb : b = .C ∨ b = .capP) (k : ℕ) (dlo dhi plo : ℚ)
    (hd0 : 0 ≤ dlo) (hd1 : dhi ≤ 3 / 4) (hp0 : 0 ≤ plo)
    (h : windowCheckB (toQ b) k dlo dhi plo = true) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (dlo : ℝ) dhi) (hp : p ∈ Set.Icc (plo : ℝ) (1 / 2)) (j : Fin 15) :
    0 < admissionGuard b δ p j := by
  have hd0' : (0 : ℝ) ≤ dlo := by exact_mod_cast hd0
  have hd1'' : (dhi : ℝ) ≤ ((3 / 4 : ℚ) : ℝ) := by exact_mod_cast hd1
  have hd1' : (dhi : ℝ) ≤ 3 / 4 := by simpa using hd1''
  have hp0' : (0 : ℝ) ≤ plo := by exact_mod_cast hp0
  have h1 := window_admittedB (toQ b) k dlo dhi plo h hδ hp j
  have h2 := guard_ge b hb ⟨hd0'.trans hδ.1, hδ.2.trans hd1'⟩ ⟨hp0'.trans hp.1, hp.2⟩ j
  linarith
end
end QRH.PositiveGap.ReturnTuning
