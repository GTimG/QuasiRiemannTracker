import Candidate.Local.Qrh.PositiveGap.Return.Tuning.Data
import Candidate.Local.Qrh.PositiveGap.Return.Facts
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.PositiveGap.ReturnTuning
open QRH.PositiveGap.Return QRH.ArviReturnTuning QRH.ArviReturnTuning.Q2
def EbaseQ (d cap : ℚ) : Q2 :=
  add (C (1 / 2 + 13 * hQ / 75 - yQ / 2 - ellQ / 2 - 9 * d / 100))
    (add (smul (1 / 2) X) (smul (ellQ - cap / 2) (mul X Y)))
def rowQ (d cap : ℚ) (J N : Q2) : Q2 :=
  sub (mul J (sub (C (thetaQ - reserveQ)) (EbaseQ d cap))) (smul (3 / 4 * d) N)
def oldDq : Q2 := sub (sub (C 3) Y) (smul (2 / (3 * kappaQ)) Y)
def oldCq : Q2 := mul (smul 2 (sub (C 1) Y)) (sub (C 1) (smul (1 / (3 * kappaQ)) Y))
def oldJq : Q2 := add (mul BranchQ.Vq oldDq) (mul X oldCq)
def oldNq : Q2 := add (mul (sub (C 1) X) oldJq) (smul (1 / 2) (mul (mul X oldCq) BranchQ.Vq))
def rowOldQ (e : Edge) : Q2 := rowQ (edgeDQ e) (edgeCQ e) oldJq oldNq
def rowBrQ (e : Edge) (b : BranchQ) : Q2 := rowQ (edgeDQ e) (edgeCQ e) b.Jq b.Nq
lemma close_div_of_bounds {d x y q : ℝ} (hy : 0 < y)
    (h1 : (q - d) * y ≤ x) (h2 : x ≤ (q + d) * y) : Close d (x / y) q :=
  ⟨by linarith [(le_div_iff₀ hy).mpr h1], by linarith [(div_le_iff₀ hy).mpr h2]⟩
lemma edgeDQ_bounds (e : Edge) : 0 ≤ (edgeDQ e : ℝ) ∧ (edgeDQ e : ℝ) ≤ 1 := by
  cases e <;>
    { unfold edgeDQ d0Q dmQ dpQ hQ cQ; norm_num }
lemma edgeCQ_bounds (e : Edge) : 0 ≤ (edgeCQ e : ℝ) ∧ (edgeCQ e : ℝ) ≤ 1 := by
  cases e <;>
    { unfold edgeCQ oldCapQ newCapQ edgeDQ d0Q dmQ dpQ numCapQ physBQ physLQ yQ hQ ellQ kappaQ cQ; norm_num }
noncomputable section
variable [TargetC]
lemma edgeD_close (e : Edge) : Close (1 / 1000000) (edgeD e) (edgeDQ e : ℝ) := by
  cases e <;>
    unfold Close edgeD edgeDQ d0 d0Q dm dmQ dp dpQ h hQ cQ <;>
    push_cast <;>
    constructor <;>
    linarith [c_lo, c_hi, eps_pos, eps_le]
lemma edgeC_close (e : Edge) : Close (2 / 1000000) (edgeC e) (edgeCQ e : ℝ) := by
  cases e
  · have hmin1 : min (1 / 200 : ℝ) (2 * y - 1 / 200) = 1 / 200 :=
      min_eq_left (by unfold y h ell; linarith [c_lo, c_hi])
    have hmin2 : min d0Q (2 * yQ - d0Q) = d0Q :=
      min_eq_left (by norm_num [d0Q, yQ, hQ, ellQ, cQ])
    unfold edgeC edgeCQ oldCapacity oldCapQ edgeD edgeDQ d0
    rw [hmin1, hmin2]; push_cast
    apply close_div_of_bounds (by unfold kappa; linarith [c_hi]) <;>
      { unfold d0Q kappaQ cQ kappa; norm_num; linarith [c_lo, c_hi] }
  · have hmin1 : min (19 / 25 : ℝ) (2 * y - 19 / 25) = 2 * y - 19 / 25 :=
      min_eq_right (by unfold y h ell; linarith [c_lo, c_hi])
    have hmin2 : min dmQ (2 * yQ - dmQ) = 2 * yQ - dmQ :=
      min_eq_right (by norm_num [dmQ, yQ, hQ, ellQ, cQ])
    unfold edgeC edgeCQ oldCapacity oldCapQ edgeD edgeDQ dm
    rw [hmin1, hmin2]; push_cast
    apply close_div_of_bounds (by unfold kappa; linarith [c_hi]) <;>
      { unfold dmQ yQ hQ ellQ kappaQ cQ y h ell kappa; norm_num; linarith [c_lo, c_hi] }
  · have hmin1 : min (numeratorCap * dm) ((2 * y - (2 - physicalB) * dm) / physicalLambda) = numeratorCap * dm := by
      apply min_eq_left
      rw [le_div_iff₀ (by unfold physicalLambda; linarith [eps_pos])]
      unfold numeratorCap dm y h ell physicalB physicalLambda
      nlinarith [c_lo, c_hi, eps_pos, eps_le]
    have hmin2 : min (numCapQ * dmQ) ((2 * yQ - (2 - physBQ) * dmQ) / physLQ) = numCapQ * dmQ :=
      min_eq_left (by norm_num [numCapQ, dmQ, yQ, hQ, ellQ, cQ, physBQ, physLQ])
    unfold edgeC edgeCQ newCapacity newCapQ edgeD edgeDQ
    rw [hmin1, hmin2]; unfold numeratorCap dm numCapQ dmQ Close; push_cast; constructor <;> norm_num
  · have hmin1 : min (numeratorCap * dp) ((2 * y - (2 - physicalB) * dp) / physicalLambda) =
        (2 * y - (2 - physicalB) * dp) / physicalLambda := by
      apply min_eq_right
      rw [div_le_iff₀ (by unfold physicalLambda; linarith [eps_pos])]
      unfold numeratorCap dp y h ell physicalB physicalLambda
      nlinarith [c_lo, c_hi, eps_pos, eps_le]
    have hmin2 : min (numCapQ * dpQ) ((2 * yQ - (2 - physBQ) * dpQ) / physLQ) =
        (2 * yQ - (2 - physBQ) * dpQ) / physLQ :=
      min_eq_right (by norm_num [numCapQ, dpQ, yQ, hQ, ellQ, cQ, physBQ, physLQ])
    unfold edgeC edgeCQ newCapacity newCapQ edgeD edgeDQ
    rw [hmin1, hmin2]; push_cast
    apply close_div_of_bounds (by unfold physicalLambda; linarith [eps_pos]) <;>
      { unfold dpQ yQ hQ ellQ cQ physBQ physLQ dp y h ell physicalB physicalLambda
        norm_num; nlinarith [c_lo, c_hi, eps_pos, eps_le] }
lemma edgeD_bounds (e : Edge) : -1 ≤ edgeD e ∧ edgeD e ≤ 1 := by
  cases e <;> unfold edgeD d0 dm dp h <;> constructor <;> linarith [c_lo, c_hi, eps_pos, eps_le]
lemma Ebase_close (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Close (1 / 1000000) (theta - reserve - Ebase (edgeD e) (edgeC e) δ p)
      (((thetaQ - reserveQ : ℚ) : ℝ) - Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p) := by
  have hd := edgeD_close e
  have hc := edgeC_close e
  have hdp0 : 0 ≤ δ * p := mul_nonneg hδ.1 hp.1
  have hdp1 : δ * p ≤ 3 / 8 := by nlinarith [hδ.1, hδ.2, hp.1, hp.2]
  have hel : Close (14 / 10000000) (ell - edgeC e / 2) ((ellQ : ℝ) - (edgeCQ e : ℝ) / 2) := by
    unfold Close ell ellQ cQ at *; push_cast; constructor <;> linarith [c_lo, c_hi, hc.1, hc.2]
  have hdp_c : Close (21 / 40000000) (δ * p * (ell - edgeC e / 2))
      ((δ * p) * ((ellQ : ℝ) - (edgeCQ e : ℝ) / 2)) := by
    unfold Close at *; constructor <;> nlinarith [hdp0, hdp1, hel.1, hel.2]
  have hev : Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p =
      1 / 2 + 13 * (hQ : ℝ) / 75 - (yQ : ℝ) / 2 - (ellQ : ℝ) / 2 - 9 * (edgeDQ e : ℝ) / 100 +
        δ / 2 + (δ * p) * ((ellQ : ℝ) - (edgeCQ e : ℝ) / 2) := by
    simp only [EbaseQ, ev_add, ev_smul, ev_mul, ev_C, ev_X, ev_Y]; push_cast; ring
  rw [hev]
  unfold Ebase theta reserve thetaQ reserveQ y h ell yQ hQ ellQ cQ Close at *
  push_cast
  constructor <;> linarith [c_lo, c_hi, eps_pos, eps_le, hd.1, hd.2, hdp_c.1, hdp_c.2]
omit [TargetC] in
lemma Ebase_bounds (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    -1 ≤ ((thetaQ - reserveQ : ℚ) : ℝ) - Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p ∧
      ((thetaQ - reserveQ : ℚ) : ℝ) - Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p ≤ 1 := by
  have hD := edgeDQ_bounds e
  have hC := edgeCQ_bounds e
  have hdp0 : 0 ≤ δ * p := mul_nonneg hδ.1 hp.1
  have hdp1 : δ * p ≤ 3 / 8 := by nlinarith [hδ.1, hδ.2, hp.1, hp.2]
  simp only [EbaseQ, ev_add, ev_smul, ev_mul, ev_C, ev_X, ev_Y]
  unfold thetaQ reserveQ yQ hQ ellQ cQ
  push_cast
  constructor <;> nlinarith [hδ.1, hδ.2, hdp0, hdp1, hD.1, hD.2, hC.1, hC.2]
lemma rowQ_le_of_close (e : Edge) (b : CountBranch) (J N : Q2) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2))
    (hJ0 : -4 ≤ countJ b δ p ∧ countJ b δ p ≤ 4)
    (hN0 : -4 ≤ Q2.ev N δ p ∧ Q2.ev N δ p ≤ 4)
    (hJc : Close (1 / 1000000) (countJ b δ p) (Q2.ev J δ p))
    (hNc : Close (2 / 1000000) (countN b δ p) (Q2.ev N δ p)) :
    Q2.ev (rowQ (edgeDQ e) (edgeCQ e) J N) δ p - 1 / 100000 ≤ rowMargin e b δ p := by
  have hMc := Ebase_close e hδ hp
  have hM0 := Ebase_bounds e hδ hp
  have hd0 := edgeD_bounds e
  have hdc := edgeD_close e
  have h1 := close_mul hJ0 hM0 hJc hMc
  have hd34_0 : -(3 / 4 : ℝ) ≤ 3 / 4 * edgeD e ∧ 3 / 4 * edgeD e ≤ 3 / 4 :=
    ⟨by linarith [hd0.1], by linarith [hd0.2]⟩
  have hd34_c : Close (3 / 4000000) (3 / 4 * edgeD e) (3 / 4 * (edgeDQ e : ℝ)) :=
    ⟨by linarith [hdc.1], by linarith [hdc.2]⟩
  have h2 := close_mul hd34_0 hN0 hd34_c hNc
  have hsub := close_sub h1 h2
  have hev : Q2.ev (rowQ (edgeDQ e) (edgeCQ e) J N) δ p =
      Q2.ev J δ p * (((thetaQ - reserveQ : ℚ) : ℝ) - Q2.ev (EbaseQ (edgeDQ e) (edgeCQ e)) δ p) -
        (3 / 4 * (edgeDQ e : ℝ)) * Q2.ev N δ p := by
    simp only [rowQ, ev_sub, ev_mul, ev_C, ev_smul]
    push_cast; ring
  have hrm : rowMargin e b δ p =
      countJ b δ p * (theta - reserve - Ebase (edgeD e) (edgeC e) δ p) -
        (3 / 4 * edgeD e) * countN b δ p := rfl
  rw [hev, hrm]
  linarith [hsub.1]
omit [TargetC] in
lemma oldD_close_step {p k kq : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2))
    (hk : Close (1 / 1000000) k kq) (hkq : kq = 5000000 / 11201457) :
    Close (1 / 1000000) (3 - p - 2 * p * k) (3 - p - 2 * p * kq) ∧
      (0 ≤ 3 - p - 2 * p * kq ∧ 3 - p - 2 * p * kq ≤ 3) := by
  unfold Close at *
  refine ⟨⟨by nlinarith [hp.1, hp.2, hk.1, hk.2], by nlinarith [hp.1, hp.2, hk.1, hk.2]⟩, ?_⟩
  rw [hkq]; constructor <;> linarith [hp.1, hp.2]
omit [TargetC] in
lemma oldC_close_step {p k kq : ℝ} (hp : p ∈ Set.Icc 0 (1 / 2))
    (hk : Close (1 / 1000000) k kq) (hkq : kq = 5000000 / 11201457) :
    Close (1 / 1000000) (2 * (1 - p) * (1 - p * k)) (2 * (1 - p) * (1 - p * kq)) ∧
      (0 ≤ 2 * (1 - p) * (1 - p * kq) ∧ 2 * (1 - p) * (1 - p * kq) ≤ 2) := by
  unfold Close at *
  have hp2 : 0 ≤ 2 * (1 - p) * p ∧ 2 * (1 - p) * p ≤ 1 :=
    ⟨by nlinarith [hp.1, hp.2], by nlinarith [hp.1, hp.2]⟩
  have hdiff : 2 * (1 - p) * (1 - p * k) - 2 * (1 - p) * (1 - p * kq) =
      -(2 * (1 - p) * p) * (k - kq) := by ring
  refine ⟨⟨by nlinarith [hdiff, hk.1, hk.2, hp2.1, hp2.2], by nlinarith [hdiff, hk.1, hk.2, hp2.1, hp2.2]⟩, ?_⟩
  rw [hkq]; constructor <;> nlinarith [hp.1, hp.2]
omit [TargetC] in
lemma oldJ_close_step {v d x y xq yq : ℝ} (hv : v = 5 / 6 - d) (hd : d ∈ Set.Icc 0 (3 / 4))
    (hx : Close (1 / 1000000) x xq) (hy : Close (1 / 1000000) y yq)
    (hx0 : 0 ≤ xq ∧ xq ≤ 3) (hy0 : 0 ≤ yq ∧ yq ≤ 2) :
    Close (1 / 1000000) (v * x + d * y) (v * xq + d * yq) ∧
      (0 ≤ v * xq + d * yq ∧ v * xq + d * yq ≤ 3) := by
  unfold Close at *
  rw [hv]
  refine ⟨⟨by nlinarith [hd.1, hd.2, hx.1, hx.2, hy.1, hy.2],
    by nlinarith [hd.1, hd.2, hx.1, hx.2, hy.1, hy.2]⟩,
    ⟨by nlinarith [hd.1, hd.2, hx0.1, hx0.2, hy0.1, hy0.2],
    by nlinarith [hd.1, hd.2, hx0.1, hx0.2, hy0.1, hy0.2]⟩⟩
omit [TargetC] in
lemma oldN_close_step {d v j c jq cq : ℝ} (hv : v = 5 / 6 - d) (hd : d ∈ Set.Icc 0 (3 / 4))
    (hj : Close (1 / 1000000) j jq) (hc : Close (1 / 1000000) c cq)
    (hj0 : 0 ≤ jq ∧ jq ≤ 3) (hc0 : 0 ≤ cq ∧ cq ≤ 2) :
    Close (2 / 1000000) ((1 - d) * j + 1 / 2 * ((v * d) * c)) ((1 - d) * jq + 1 / 2 * ((v * d) * cq)) ∧
      (-4 ≤ (1 - d) * jq + 1 / 2 * ((v * d) * cq) ∧ (1 - d) * jq + 1 / 2 * ((v * d) * cq) ≤ 4) := by
  unfold Close at *
  have hvd : 0 ≤ v * d ∧ v * d ≤ 1 := by rw [hv]; constructor <;> nlinarith [hd.1, hd.2]
  refine ⟨⟨by nlinarith [hd.1, hd.2, hvd.1, hvd.2, hj.1, hj.2, hc.1, hc.2],
    by nlinarith [hd.1, hd.2, hvd.1, hvd.2, hj.1, hj.2, hc.1, hc.2]⟩,
    ⟨by nlinarith [hd.1, hd.2, hvd.1, hvd.2, hj0.1, hj0.2, hc0.1, hc0.2],
    by nlinarith [hd.1, hd.2, hvd.1, hvd.2, hj0.1, hj0.2, hc0.1, hc0.2]⟩⟩
omit [TargetC] in
lemma nr_bounds_step {d vd j u : ℝ} (hd : d ∈ Set.Icc 0 (3 / 4)) (hvd : 0 ≤ vd ∧ vd ≤ 1)
    (hj : -3 ≤ j ∧ j ≤ 3) (hu : 0 ≤ u ∧ u ≤ 1) :
    -4 ≤ (1 - d) * j + vd * u ∧ (1 - d) * j + vd * u ≤ 4 := by
  constructor <;> nlinarith [hd.1, hd.2, hvd.1, hvd.2, hj.1, hj.2, hu.1, hu.2]
theorem rowOldQ_le (e : Edge) {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Q2.ev (rowOldQ e) δ p - 1 / 100000 ≤ rowMargin e .old δ p := by
  have hk : Close (1 / 1000000) (1 / (3 * kappa)) (1 / (3 * (kappaQ : ℝ))) := by
    apply close_div_of_bounds (by unfold kappa; linarith [c_hi]) <;>
      { unfold kappaQ cQ kappa; norm_num; linarith [c_lo, c_hi] }
  have hk_val : (1 / (3 * (kappaQ : ℝ))) = 5000000 / 11201457 := by
    unfold kappaQ cQ; push_cast; norm_num
  obtain ⟨hDc, hD0⟩ := oldD_close_step hp hk hk_val
  obtain ⟨hCc, hC0⟩ := oldC_close_step hp hk hk_val
  have hevD : Q2.ev oldDq δ p = 3 - p - 2 * p * (1 / (3 * (kappaQ : ℝ))) := by
    simp only [oldDq, ev_sub, ev_smul, ev_C, ev_Y]; push_cast; ring
  have hevC : Q2.ev oldCq δ p = 2 * (1 - p) * (1 - p * (1 / (3 * (kappaQ : ℝ)))) := by
    simp only [oldCq, ev_mul, ev_smul, ev_sub, ev_C, ev_Y]; push_cast; ring
  have hD_real : oldD p = 3 - p - 2 * p * (1 / (3 * kappa)) := by unfold oldD; ring
  have hC_real : oldC p = 2 * (1 - p) * (1 - p * (1 / (3 * kappa))) := by unfold oldC; ring
  rw [← hD_real, ← hevD] at hDc; rw [← hevD] at hD0
  rw [← hC_real, ← hevC] at hCc; rw [← hevC] at hC0
  obtain ⟨hJc, hJ_0⟩ := oldJ_close_step (rfl : V δ = 5 / 6 - δ) hδ hDc hCc hD0 hC0
  have hevJ : Q2.ev oldJq δ p = V δ * Q2.ev oldDq δ p + δ * Q2.ev oldCq δ p := by
    simp only [oldJq, ev_add, ev_mul, ev_X, ev_Vq]
  have hJ_real : countJ .old δ p = V δ * oldD p + δ * oldC p := rfl
  rw [← hJ_real, ← hevJ] at hJc; rw [← hevJ] at hJ_0
  obtain ⟨hNc, hN0⟩ := oldN_close_step (rfl : V δ = 5 / 6 - δ) hδ hJc hCc hJ_0 hC0
  have hevN : Q2.ev oldNq δ p = (1 - δ) * Q2.ev oldJq δ p + 1 / 2 * ((V δ * δ) * Q2.ev oldCq δ p) := by
    simp only [oldNq, ev_add, ev_mul, ev_sub, ev_smul, ev_C, ev_X, ev_Vq]; ring
  have hN_real : countN .old δ p = (1 - δ) * countJ .old δ p + 1 / 2 * ((V δ * δ) * oldC p) := by
    unfold countN; ring
  rw [← hN_real, ← hevN] at hNc; rw [← hevN] at hN0
  have hJ0 : -4 ≤ countJ .old δ p ∧ countJ .old δ p ≤ 4 :=
    ⟨by linarith [hJc.1, hJ_0.1], by linarith [hJc.2, hJ_0.2]⟩
  exact rowQ_le_of_close e .old oldJq oldNq hδ hp hJ0 hN0 hJc hNc
theorem rowBrQ_le (e : Edge) (b : CountBranch) (hb : b = .C ∨ b = .capP) {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3 / 4)) (hp : p ∈ Set.Icc 0 (1 / 2)) :
    Q2.ev (rowBrQ e (toQ b)) δ p - 1 / 100000 ≤ rowMargin e b δ p := by
  have ht1 := tParam_le_num
  have hVd : 0 ≤ V δ * δ ∧ V δ * δ ≤ 1 := by
    unfold V; constructor <;> nlinarith [hδ.1, hδ.2]
  rcases hb with rfl | rfl
  · have hJ_real : countJ .C δ p = R.Jr (2 + 10 * eps) false δ p := rfl
    have hN_real : countN .C δ p = R.Nr (1 - eps) (2 + 10 * eps) countCap false δ p := rfl
    have hevJ : Q2.ev (toQ .C).Jq δ p = R.Jr 2 false δ p := by
      simpa [toQ, countLQ] using ev_Jq (toQ .C) δ p
    have hevN : Q2.ev (toQ .C).Nq δ p = (1 - δ) * Q2.ev (toQ .C).Jq δ p + (V δ * δ) * ((1 - p) * (1 - p)) := by
      rw [ev_Nq (toQ .C) δ p, hevJ]
      unfold R.Nr R.Ur R.C0r toQ countBQ countLQ countCapQ
      simp only [Bool.false_eq_true, ↓reduceIte]; push_cast; ring
    have hJc : Close (1 / 1000000) (countJ .C δ p) (Q2.ev (toQ .C).Jq δ p) := by
      rw [hJ_real, hevJ]; exact close_mono (Jr_close false hδ hp) (by linarith [ht1])
    have hNc : Close (2 / 1000000) (countN .C δ p) (Q2.ev (toQ .C).Nq δ p) := by
      rw [hN_real, ev_Nq (toQ .C) δ p]
      simpa [toQ, countBQ, countLQ, countCapQ, countCap] using
        close_mono (Nr_close countCap false hδ hp) (by linarith [ht1])
    have hJ_0 : -3 ≤ Q2.ev (toQ .C).Jq δ p ∧ Q2.ev (toQ .C).Jq δ p ≤ 3 := by
      rw [hevJ]; exact Jr_0_bounds hδ hp
    have hJ0 : -4 ≤ countJ .C δ p ∧ countJ .C δ p ≤ 4 :=
      ⟨by linarith [hJc.1, hJ_0.1], by linarith [hJc.2, hJ_0.2]⟩
    have hp2 : 0 ≤ (1 - p) * (1 - p) ∧ (1 - p) * (1 - p) ≤ 1 := ⟨by nlinarith [hp.2], by nlinarith [hp.1, hp.2]⟩
    have hN0 := nr_bounds_step hδ hVd hJ_0 hp2
    rw [← hevN] at hN0
    exact rowQ_le_of_close e .C (toQ .C).Jq (toQ .C).Nq hδ hp hJ0 hN0 hJc hNc
  · have hJ_real : countJ .capP δ p = R.Jr (2 + 10 * eps) true δ p := rfl
    have hN_real : countN .capP δ p = R.Nr (1 - eps) (2 + 10 * eps) physicalCap true δ p := rfl
    have hevJ : Q2.ev (toQ .capP).Jq δ p = R.Jr 2 true δ p := by
      simpa [toQ, physLQ] using ev_Jq (toQ .capP) δ p
    have hevN : Q2.ev (toQ .capP).Nq δ p =
        (1 - δ) * Q2.ev (toQ .capP).Jq δ p + (V δ * δ) * ((1 - p) * (1 - 2 * p * (3 / 25 - 1 / 10000000))) := by
      rw [ev_Nq (toQ .capP) δ p, hevJ]
      unfold R.Nr R.Ur R.C0r toQ physBQ physLQ physCapQ
      simp only [↓reduceIte]; push_cast; ring
    have hJc : Close (1 / 1000000) (countJ .capP δ p) (Q2.ev (toQ .capP).Jq δ p) := by
      rw [hJ_real, hevJ]; exact close_mono (Jr_close true hδ hp) (by linarith [ht1])
    have hNc : Close (2 / 1000000) (countN .capP δ p) (Q2.ev (toQ .capP).Nq δ p) := by
      rw [hN_real, ev_Nq (toQ .capP) δ p]
      simpa [toQ, physBQ, physLQ, physCapQ, physicalCap] using
        close_mono (Nr_close physicalCap true hδ hp) (by linarith [ht1])
    have hJ_0 : -3 ≤ Q2.ev (toQ .capP).Jq δ p ∧ Q2.ev (toQ .capP).Jq δ p ≤ 3 := by
      rw [hevJ]; exact Jr_true_bounds hδ hp
    have hJ0 : -4 ≤ countJ .capP δ p ∧ countJ .capP δ p ≤ 4 :=
      ⟨by linarith [hJc.1, hJ_0.1], by linarith [hJc.2, hJ_0.2]⟩
    have hp2 : 0 ≤ (1 - p) * (1 - 2 * p * (3 / 25 - 1 / 10000000)) ∧
        (1 - p) * (1 - 2 * p * (3 / 25 - 1 / 10000000)) ≤ 1 := by
      constructor <;> nlinarith [hp.1, hp.2]
    have hN0 := nr_bounds_step hδ hVd hJ_0 hp2
    rw [← hevN] at hN0
    exact rowQ_le_of_close e .capP (toQ .capP).Jq (toQ .capP).Nq hδ hp hJ0 hN0 hJc hNc
end
end QRH.PositiveGap.ReturnTuning
