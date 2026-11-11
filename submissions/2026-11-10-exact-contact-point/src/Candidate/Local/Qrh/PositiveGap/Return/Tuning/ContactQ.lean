import Candidate.Local.Qrh.PositiveGap.Return.Tuning.CoverQ
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.PositiveGap.ReturnTuning
open QRH.PositiveGap.Return QRH.ArviReturnTuning
def evalQ : Q1 → ℚ → ℚ
  | [], _ => 0
  | c :: cs, a => c + a * evalQ cs a
def divQ : Q1 → ℚ → Q1
  | [], _ => []
  | _ :: cs, a => Q1.add cs (Q1.smul a (divQ cs a))
theorem ev_divQ (r : Q1) (a : ℚ) (p : ℝ) :
    Q1.ev r p = (evalQ r a : ℝ) + (p - a) * Q1.ev (divQ r a) p := by
  induction r with
  | nil => simp [evalQ, divQ]
  | cons c cs ih =>
    simp only [Q1.ev_cons, evalQ, divQ, Q1.ev_add, Q1.ev_smul]
    push_cast
    rw [ih]
    ring
def headsQ (P : Q2) (a : ℚ) : Q1 := P.map (evalQ · a)
def quotQ (P : Q2) (a : ℚ) : Q2 := P.map (divQ · a)
theorem ev_split (P : Q2) (a : ℚ) (d p : ℝ) :
    Q2.ev P d p = Q1.ev (headsQ P a) d + (p - a) * Q2.ev (quotQ P a) d p := by
  induction P with
  | nil => simp [headsQ, quotQ]
  | cons r P ih =>
    simp only [headsQ, quotQ, List.map_cons, Q2.ev_cons, Q1.ev_cons] at ih ⊢
    rw [ev_divQ r a p, ih]
    ring
theorem ev_at_half (P : Q2) (d : ℝ) :
    Q2.ev P d (1 / 2) = Q1.ev (headsQ P (1 / 2)) d := by
  have h := ev_split P (1 / 2) d (1 / 2)
  push_cast at h
  linarith
theorem contact_slope_ok :
    bernCheck (Q2.smul (-1) (quotQ (rowBrQ .newTop (toQ .C)) (1 / 2))) (3 / 8) (15 / 32) (7 / 16) (1 / 2) = true := by
  decide +kernel
noncomputable section
variable [TargetC]
def rowTopC0 (δ p : ℝ) : ℝ :=
  R.Jr 2 false δ p * (1 - c - Ebase h ((2 * y - h) / 2) δ p) - 3 / 4 * h * R.Nr 1 2 countCap false δ p
lemma edgeC_newTop_eq : edgeC .newTop = (2 * y - (1 + eps) * (h + eps)) / (2 + 10 * eps) := by
  have hmin1 : min (numeratorCap * dp) ((2 * y - (2 - physicalB) * dp) / physicalLambda) =
      (2 * y - (2 - physicalB) * dp) / physicalLambda := by
    apply min_eq_right
    rw [div_le_iff₀ (by unfold physicalLambda; linarith [eps_pos])]
    unfold numeratorCap dp y h ell physicalB physicalLambda
    nlinarith [c_lo, c_hi, eps_pos, eps_le]
  unfold edgeC newCapacity edgeD
  rw [hmin1]
  unfold physicalB physicalLambda dp
  ring
lemma edgeC_newTop_close : Close (3 * eps) (edgeC .newTop) ((2 * y - h) / 2) := by
  rw [edgeC_newTop_eq]
  apply close_div_of_bounds hL_pos <;>
    { unfold y h ell; nlinarith [c_lo, c_hi, eps_pos, eps_le] }
lemma rowTopC0_close {δ p : ℝ} (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    rowTopC0 δ p - 100 * eps ≤ rowMargin .newTop .C δ p := by
  have ht1 := tParam_le
  have he0 := eps_pos
  have he1 := eps_le
  have hdp : 0 ≤ δ * p ∧ δ * p ≤ 3 / 8 :=
    ⟨mul_nonneg hδ.1 hp.1, by nlinarith [hδ.1, hδ.2, hp.1, hp.2]⟩
  have hC_close := edgeC_newTop_close
  have hM_close : Close (2 * eps) (theta - reserve - Ebase (edgeD .newTop) (edgeC .newTop) δ p)
      (1 - c - Ebase h ((2 * y - h) / 2) δ p) := by
    unfold Close theta reserve Ebase edgeD dp
    constructor <;> nlinarith [hC_close.1, hC_close.2, hdp.1, hdp.2, he0]
  have hM0 : -2 ≤ 1 - c - Ebase h ((2 * y - h) / 2) δ p ∧
      1 - c - Ebase h ((2 * y - h) / 2) δ p ≤ 2 := by
    unfold Ebase y h ell
    constructor <;> nlinarith [c_lo, c_hi, hδ.1, hδ.2, hdp.1, hdp.2]
  have hJc : Close (5 * eps) (countJ .C δ p) (R.Jr 2 false δ p) :=
    close_mono (Jr_close false hδ hp) (by linarith [ht1])
  have hNc : Close (8 * eps) (countN .C δ p) (R.Nr 1 2 countCap false δ p) :=
    close_mono (Nr_close countCap false hδ hp) (by linarith [ht1])
  have hJ_0 : -3 ≤ R.Jr 2 false δ p ∧ R.Jr 2 false δ p ≤ 3 := Jr_0_bounds hδ hp
  have hJ0 : -4 ≤ countJ .C δ p ∧ countJ .C δ p ≤ 4 :=
    ⟨by linarith [hJc.1, hJ_0.1, he1], by linarith [hJc.2, hJ_0.2, he1]⟩
  have hVd : 0 ≤ V δ * δ ∧ V δ * δ ≤ 1 := by unfold V; constructor <;> nlinarith [hδ.1, hδ.2]
  have hp2 : 0 ≤ (1 - p) * (1 - p) ∧ (1 - p) * (1 - p) ≤ 1 := ⟨by nlinarith [hp.2], by nlinarith [hp.1, hp.2]⟩
  have hN0_step := nr_bounds_step hδ hVd hJ_0 hp2
  have hN_eq : R.Nr 1 2 countCap false δ p = (1 - δ) * R.Jr 2 false δ p + (V δ * δ) * ((1 - p) * (1 - p)) := by
    unfold R.Nr R.Ur R.C0r; simp only [Bool.false_eq_true, ↓reduceIte]; ring
  have hN0 : -4 ≤ R.Nr 1 2 countCap false δ p ∧ R.Nr 1 2 countCap false δ p ≤ 4 := by
    rw [hN_eq]; exact hN0_step
  have hd0 : -1 ≤ 3 / 4 * edgeD .newTop ∧ 3 / 4 * edgeD .newTop ≤ 1 := by
    unfold edgeD dp h; constructor <;> linarith [c_lo, c_hi, he0, he1]
  have hdc : Close eps (3 / 4 * edgeD .newTop) (3 / 4 * h) := by
    unfold Close edgeD dp; constructor <;> linarith [he0]
  have h1 := close_mul hJ0 hM0 hJc hM_close
  have h2 := close_mul hd0 hN0 hdc hNc
  have hsub := close_sub h1 h2
  have hrm : rowMargin .newTop .C δ p =
      countJ .C δ p * (theta - reserve - Ebase (edgeD .newTop) (edgeC .newTop) δ p) -
        (3 / 4 * edgeD .newTop) * countN .C δ p := rfl
  have htc : rowTopC0 δ p =
      R.Jr 2 false δ p * (1 - c - Ebase h ((2 * y - h) / 2) δ p) -
        (3 / 4 * h) * R.Nr 1 2 countCap false δ p := rfl
  rw [hrm, htc]
  linarith [hsub.1]
lemma rowTopC0_half_ge (δ : ℝ) : 200 * eps ≤ rowTopC0 δ (1 / 2) := by
  let a2 : ℝ := (10891 - 62148 * c) / 25944
  let a1 : ℝ := 5 * (12741 * c - 1742) / 6486
  have hid : 4 * a2 * rowTopC0 δ (1 / 2) = (2 * a2 * δ + a1) ^ 2 + (475 / 14736192) * gap := by
    dsimp only [a2, a1]
    unfold rowTopC0 R.Nr R.Jr R.Dr R.Ar R.Ur R.C0r V Ebase y h ell gap
    simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  have ha2_pos : 0 < a2 := by dsimp only [a2]; linarith [c_hi]
  have ha2_hi : 4 * a2 ≤ 1 / 2 := by dsimp only [a2]; linarith [c_lo]
  have hsq : 0 ≤ (2 * a2 * δ + a1) ^ 2 := sq_nonneg _
  have hgap : gap = 10000000000 * eps := by unfold eps; ring
  have hpos : 0 < rowTopC0 δ (1 / 2) := by
    have : 0 < 4 * a2 * rowTopC0 δ (1 / 2) := by linarith [hid, hsq, gap_pos]
    nlinarith [ha2_pos]
  nlinarith [hid, hsq, hgap, ha2_hi, hpos, eps_pos]
lemma rowTopC0_ge_half {δ p : ℝ} (hd0 : (3 / 8 : ℝ) ≤ δ) (hd1 : δ ≤ 15 / 32)
    (hp0 : (7 / 16 : ℝ) ≤ p) (hp1 : p ≤ 1 / 2) :
    rowTopC0 δ (1 / 2) ≤ rowTopC0 δ p := by
  have hslope := @bernCheck_sound (Q2.smul (-1) (quotQ (rowBrQ .newTop (toQ .C)) (1 / 2)))
    (3 / 8) (15 / 32) (7 / 16) (1 / 2) contact_slope_ok δ p
    (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
  rw [Q2.ev_smul] at hslope
  push_cast at hslope
  have hsplit := ev_split (rowBrQ .newTop (toQ .C)) (1 / 2) δ p
  rw [← ev_at_half] at hsplit
  push_cast at hsplit
  have hq_ge : 0 ≤ Q2.ev (rowBrQ .newTop (toQ .C)) δ p - Q2.ev (rowBrQ .newTop (toQ .C)) δ (1 / 2) := by
    have : 0 ≤ (1 / 2 - p) * (-Q2.ev (quotQ (rowBrQ .newTop (toQ .C)) (1 / 2)) δ p) :=
      mul_nonneg (by linarith) (by linarith)
    linarith [hsplit]
  have hminQ : min (numCapQ * dpQ) ((2 * yQ - (2 - physBQ) * dpQ) / physLQ) =
      (2 * yQ - (2 - physBQ) * dpQ) / physLQ :=
    min_eq_right (by norm_num [numCapQ, dpQ, yQ, hQ, ellQ, cQ, physBQ, physLQ])
  have hev_eq (q : ℝ) : Q2.ev (rowBrQ .newTop (toQ .C)) δ q =
      R.Jr 2 false δ q * (1 - (cQ : ℝ) -
        (1 / 2 + 13 * (hQ : ℝ) / 75 - (yQ : ℝ) / 2 - (ellQ : ℝ) / 2 - 9 * (hQ : ℝ) / 100 +
          δ / 2 + δ * q * ((ellQ : ℝ) - ((2 * (yQ : ℝ) - (hQ : ℝ)) / 2) / 2))) -
        3 / 4 * (hQ : ℝ) * R.Nr 1 2 countCap false δ q := by
    rw [rowBrQ]
    simp only [rowQ, EbaseQ, Q2.ev_sub, Q2.ev_mul, Q2.ev_add, Q2.ev_smul, Q2.ev_C, Q2.ev_X, Q2.ev_Y]
    have hJ : Q2.ev (toQ .C).Jq δ q = R.Jr 2 false δ q := by
      simpa [toQ, countLQ] using ev_Jq (toQ .C) δ q
    have hN : Q2.ev (toQ .C).Nq δ q = R.Nr 1 2 countCap false δ q := by
      simpa [toQ, countBQ, countLQ, countCapQ, countCap] using ev_Nq (toQ .C) δ q
    rw [hJ, hN]
    dsimp only [edgeDQ, edgeCQ, newCapQ]
    rw [hminQ]
    unfold dpQ physBQ physLQ thetaQ reserveQ
    push_cast
    ring
  have hdiff : (rowTopC0 δ p - rowTopC0 δ (1 / 2)) -
      (Q2.ev (rowBrQ .newTop (toQ .C)) δ p - Q2.ev (rowBrQ .newTop (toQ .C)) δ (1 / 2)) =
      ((cQ : ℝ) - c) * (1 / 2 - p) *
        ((32975 - 34190 * δ - 8280 * (δ * p) - 10358 * (δ * δ) + 45252 * δ * (δ * p) -
          24536 * ((δ * p) * (δ * p))) / 2162) := by
    rw [hev_eq p, hev_eq (1 / 2)]
    unfold rowTopC0 R.Nr R.Jr R.Dr R.Ar R.Ur R.C0r V Ebase y h ell yQ hQ ellQ
    simp only [Bool.false_eq_true, ↓reduceIte]
    push_cast
    ring
  have hdp : 0 ≤ δ * p ∧ δ * p ≤ 15 / 64 := ⟨by positivity, by nlinarith⟩
  have hd2 : 0 ≤ δ * δ ∧ δ * δ ≤ 225 / 1024 := ⟨by positivity, by nlinarith⟩
  have hdp2 : 0 ≤ (δ * p) * (δ * p) ∧ (δ * p) * (δ * p) ≤ 225 / 4096 := ⟨by positivity, by nlinarith⟩
  have hpoly : 0 ≤ (32975 - 34190 * δ - 8280 * (δ * p) - 10358 * (δ * δ) + 45252 * δ * (δ * p) -
      24536 * ((δ * p) * (δ * p))) / 2162 := by
    nlinarith [hd0, hd1, hdp.1, hdp.2, hd2.1, hd2.2, hdp2.1, hdp2.2]
  have hc_ge : 0 ≤ (cQ : ℝ) - c := by unfold cQ; push_cast; linarith [c_hi]
  have hprod : 0 ≤ ((cQ : ℝ) - c) * (1 / 2 - p) *
      ((32975 - 34190 * δ - 8280 * (δ * p) - 10358 * (δ * δ) + 45252 * δ * (δ * p) -
        24536 * ((δ * p) * (δ * p))) / 2162) :=
    mul_nonneg (mul_nonneg hc_ge (by linarith)) hpoly
  linarith [hdiff, hq_ge, hprod]
theorem contact_topRR03_row (ws : List WinQ) (env : ℝ → ℝ → ℝ)
    (hwin : ∀ w ∈ ws, w.branch ≠ .old → ∀ δ p, δ ∈ Set.Icc (w.dlo : ℝ) w.dhi →
      p ∈ Set.Icc (w.plo : ℝ) (1 / 2) → env δ p ≤ countN w.branch δ p / countJ w.branch δ p)
    (hw : ⟨.C, 9 / 25, 49 / 100, 0⟩ ∈ ws) {δ p : ℝ}
    (hd0 : (3 / 8 : ℝ) ≤ δ) (hd1 : δ ≤ 15 / 32) (hp0 : (7 / 16 : ℝ) ≤ p)
    (hδ : δ ∈ Set.Icc (0 : ℝ) (3 / 4)) (hp : p ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Ebase (edgeD .newTop) (edgeC .newTop) δ p + 3 / 4 * edgeD .newTop * env δ p < theta - reserve := by
  have h1 := rowTopC0_close hδ hp
  have h2 := rowTopC0_half_ge δ
  have h3 := rowTopC0_ge_half hd0 hd1 hp0 hp.2
  have hF : 0 < rowMargin .newTop .C δ p := by linarith [eps_pos]
  exact exponent_lt_of_margin (countJ_pos .C hδ hp) hF
    (hwin ⟨.C, 9 / 25, 49 / 100, 0⟩ hw (by decide) δ p
      ⟨by norm_num; linarith, by norm_num; linarith⟩ ⟨by norm_num; linarith [hp.1], hp.2⟩)
end
end QRH.PositiveGap.ReturnTuning
