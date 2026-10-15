import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedRamified
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedActual

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ProbeLocal
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

/-!
The official selected-prime estimates are stated for `7/8 ≤ x.re`.  The
canonical-minus-central lane only needs the parent-forced line
`87/100 ≤ x.re`, together with `1/2 ≤ w.re` and `17/50 ≤ z.re`.
The proofs below repeat the actual local estimates at that line.  No Euler
factor, row object, phase, or selected-prime weight is changed.
-/

lemma unramifiedMarked_selected_error_first87 (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤ 28 ∧
      ‖star eta * (Q : ℂ) ^ x‖ *
        ‖unramifiedMarked Q A eta v x w z + coordD Q eta v x‖ ≤ 28 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta * (Q : ℂ) ^ x
  have hR : ‖R‖ ≤ Q ^ (4 - 6 * x.re - 6 * z.re) :=
    coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖ = Q ^ (-6 * z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖ ≤ Q ^ (-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖ ≤ 1 :=
    (coordW_norm_le Q hQ0 v w hv).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (1 - x.re - w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : ‖B‖ ≤ Q ^ x.re := by
    dsimp only [B]
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖ ≤ 1 / 2 := by
    rw [hV]
    exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q ^ aa) (hbb : b ≤ Q ^ bb) (he : aa + bb ≤ 0) : a * b ≤ 1 := by
    calc
      a * b ≤ Q ^ aa * Q ^ bb :=
        mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (aa + bb) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : ‖K‖ * ‖V‖ ≤ 1 :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : ‖B‖ * ‖R‖ ≤ 1 :=
    hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : ‖K‖ * ‖V‖ ≤ Q ^ (1 - x.re - w.re - 6 * z.re) := by
    calc
      _ ≤ Q ^ (1 - x.re - w.re) * Q ^ (-6 * z.re) :=
        mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _ = _ := by
        rw [← Real.rpow_add hQ0]
        congr 1
        ring
  have hBKV : ‖B‖ * (‖K‖ * ‖V‖) ≤ 1 :=
    hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := unramified_marked_error_bound R V (Q : ℂ)⁻¹ K W D hRh hVh hqi hDh
  change ‖unramifiedMarked Q A eta v x w z + D‖ ≤ _ at hE
  have hE' :
      ‖unramifiedMarked Q A eta v x w z + D‖ ≤ 24 * ‖R‖ + 4 * (‖K‖ * ‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z + D‖ ≤ 28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖ * ‖unramifiedMarked Q A eta v x w z + D‖ ≤ 28
    nlinarith

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

include hc in
theorem sourceRowTerm_selected_base_first87 (eta a rho x w z : ℂ)
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (_hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re)
    (j e l k m : ℕ) (hj : j < 6) (hk : k ≤ 1)
    (hf : (e = 0 ∧ l = 2) ∨ (e = 1 ∧ l = 0) ∨
      (e = 0 ∧ l = 1) ∨ (e = 1 ∧ l = 1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖ ≤
      2 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hb0 : (0 : ℝ) ≤ max (1 - w.re) 0 := le_max_right _ _
  have hb1 : 1 - w.re ≤ max (1 - w.re) 0 := le_max_left _ _
  have hzm : 0 ≤ 6 * z.re * (m : ℝ) := by positivity
  have hzm1 (hm : m ≠ 0) : 6 * z.re ≤ 6 * z.re * (m : ℝ) := by
    have hm1 : (1 : ℝ) ≤ m := by
      exact_mod_cast (by omega : 1 ≤ m)
    nlinarith
  have hrelax (v : ℝ) : Q ^ v ≤ 2 * Q ^ v := by
    nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t ≠ 0) :
      sourceScalar p hp hg t k (j + 6 * m) =
        positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg)
          (t - 1) k (j + 6 * m) := by
    rw [sourceScalar, ite_eq_right ht]
  rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · by_cases hm : m = 0
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
          heta ha hρ j 0 2 0 m 5 (-x.re + max (1 - w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 6 0 (by decide),
            Nat.reduceSub, Real.rpow_natCast, Real.rpow_ofNat] using
            hs.trans (show Q ^ 5 ≤ 2 * Q ^ 5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero, Nat.cast_ofNat, mul_zero, mul_one, sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
          heta ha hρ j 0 2 0 m 6 (-x.re + max (1 - w.re) 0)
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 6 0 (by decide),
            Nat.reduceSub, Real.rpow_natCast, Real.rpow_ofNat] using
            hs.trans (show Q ^ 6 ≤ 2 * Q ^ 6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero, Nat.cast_ofNat, mul_zero, mul_one, sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m = 0
      · subst m
        simp only [sourceRowTerm, sourceScalar, Nat.reduceMul, Nat.reduceAdd,
          Nat.reduceSub, Nat.reduceEqDiff, ite_false, mul_zero, add_zero,
          even_base_kone_zero p hp hg hc j hj, sourceWeightedScalar,
          zero_mul, mul_zero, norm_zero]
        positivity
      · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
          heta ha hρ j 0 2 1 m 6 (-x.re + max (1 - w.re) 0)
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j + 6 * m)
            (by decide) (by decide)
          simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 6 1 (by decide),
            Nat.reduceSub, Real.rpow_natCast, Real.rpow_ofNat] using
            hs.trans (show Q ^ 6 ≤ 2 * Q ^ 6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero, Nat.cast_ofNat, mul_zero, mul_one, sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 1 0 0 m (1 / 2) (-x.re + max (1 - w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j + 6 * m) (by decide)
        simp only [pow_zero, one_mul, Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 1 0 (by decide),
          Nat.reduceSub] using hs.trans (hrelax (1 / 2))
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 1 0 1 m (3 / 2) (-x.re + max (1 - w.re) 0)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j + 6 * m) (by decide)
        simp only [Nat.zero_add, pow_one] at hs
        have he : 2 * Q * Real.sqrt Q = 2 * Q ^ (3 / 2 : ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc, ht]
        rw [he] at hs
        simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 1 1 (by decide),
          Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 0 1 0 m (5 / 2) (-x.re + max (1 - w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j + 6 * m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5 / 2)) using 1 <;>
          simp only [sourceScalar, Nat.reduceMul, Nat.reduceAdd,
            Nat.reduceEqDiff, ite_false, Nat.reduceSub]
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 0 1 1 m 3 (-x.re + max (1 - w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j + 6 * m)
          (by decide) (by decide)
        simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 3 1 (by decide),
          Nat.reduceSub, Real.rpow_natCast, Real.rpow_ofNat] using
          hs.trans (show Q ^ 3 ≤ 2 * Q ^ 3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 1 1 0 m (7 / 2) (-x.re + max (1 - w.re) 0)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j + 6 * m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7 / 2)) using 1 <;>
          simp only [sourceScalar, Nat.reduceMul, Nat.reduceAdd,
            Nat.reduceEqDiff, ite_false, Nat.reduceSub]
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z
        heta ha hρ j 1 1 1 m 4 (-x.re + max (1 - w.re) 0)
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j + 6 * m)
          (by decide) (by decide)
        simpa only [Nat.reduceMul, Nat.reduceAdd, hz0 4 1 (by decide),
          Nat.reduceSub, Real.rpow_natCast, Real.rpow_ofNat] using
          hs.trans (show Q ^ 4 ≤ 2 * Q ^ 4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, sub_zero]
        linarith

include hc in
lemma rowBaseFinite_selected_bound_first87 (eta a rho x w z : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re)
    (j e l : ℕ) (hj : j < 6)
    (hf : (e = 0 ∧ l = 2) ∨ (e = 1 ∧ l = 0) ∨
      (e = 0 ∧ l = 1) ∨ (e = 1 ∧ l = 1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j e l‖ ≤
      16 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
  have hpow :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
    positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
        ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j e l k.val m‖ ≤
        2 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
    have ht : e + 3 * l ≠ 0 := by
      rcases hf with h | h | h | h <;> omega
    rw [← sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_selected_base_first87 p hp hg hc eta a rho x w z
      heta ha hρ hx hw hz j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,
        8 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd :
          ‖rowMarkedTerm p hp hg eta a
              ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
              ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
              (coordV (Ideal.absNorm (Ideal.span {p})) z)
              rho j e l k.val 2 /
            (1 - coordV (Ideal.absNorm (Ideal.span {p})) z)‖ ≤
            4 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^
              (-x.re + max (1 - w.re) 0) := by
        rw [div_eq_mul_inv, norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp; ring

include hc in
theorem rowClosedMarked_selected_bound_first87 (eta a rho x w z : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) (j : ℕ) (hj : j < 6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-x))
      ((Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w))
      (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖ ≤
      128 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
  have hpow :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-x.re + max (1 - w.re) 0) := by
    positivity
  have h02 := rowBaseFinite_selected_bound_first87 p hp hg hc eta a rho x w z hQ
    heta ha hρ hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound_first87 p hp hg hc eta a rho x w z hQ
    heta ha hρ hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound_first87 p hp hg hc eta a rho x w z hQ
    heta ha hρ hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound_first87 p hp hg hc eta a rho x w z hQ
    heta ha hρ hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _
    (first_region_R_half _ hQ a x z ha (by linarith) hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv, norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11))
    (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedSelected_bound_first87 (eta a rho x w z : ℂ)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hρ : rho ^ 6 = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) (j : ℕ) (hj : j < 6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j‖ ≤
      385 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (max (1 - w.re) 0) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let B : ℝ := max (1 - w.re) 0
  have hQ0 : 0 < Q := by dsimp [Q]; linarith
  have hQ1 : 1 ≤ Q := by dsimp [Q]; linarith
  have hB0 : 0 ≤ B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound_first87 p hp hg hc eta a rho x w z
    hQ heta ha hρ hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ
    heta ha hρ (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : ‖1 - coordV (Ideal.absNorm (Ideal.span {p})) z‖ ≤ 3 / 2 := by
    have hh := norm_sub_le (1 : ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    simp only [norm_one] at hh
    linarith
  have hphase : ‖star eta * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ x‖ ≤ Q ^ x.re := by
    change ‖star eta * (Q : ℂ) ^ x‖ ≤ Q ^ x.re
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (-w)‖ ≤ Q ^ B := by
    change ‖(Q : ℂ) ^ (-w)‖ ≤ Q ^ B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B]; linarith)
  have he : Q ^ x.re * Q ^ (-x.re + B) = Q ^ B := by
    rw [← Real.rpow_add hQ0]
    congr 1
    ring
  unfold ramifiedSelected
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _ ≤ (Q ^ x.re * (3 / 2)) * (128 * Q ^ (-x.re + B)) + Q ^ B * 193 := by
      gcongr
    _ = 385 * Q ^ B := by nlinarith [he]

lemma unramifiedSelected_error_bound_first87 (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z +
      unramifiedClosed Q A eta v x w z * star v‖ ≤ 720 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖coordW Q v w‖ ≤ 1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans
      (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error_first87 Q A eta v x w z hQ hA
    heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w)
    (coordD Q eta v x) (unramifiedMarked Q A eta v x w z)
    (star eta * (Q : ℂ) ^ x) ((Q : ℂ) ^ (-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2)
    (by rw [norm_star, hv]) hi.1 hi.2
  simpa only [mul_one, unramifiedSelected, unramifiedClosed, unramifiedMarked] using hh

lemma unramifiedSelected_bound_first87 (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ = 1) (hv : ‖v‖ = 1)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z‖ ≤ 961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1 / 4)
    hQ hA heta.le hv.le (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q ^ (-1 - min (1 / 4 : ℝ) (1 / 50)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖ ≤ 241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound_first87 Q A eta v x w z
    hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z +
      unramifiedClosed Q A eta v x w z * star v)
    (unramifiedClosed Q A eta v x w z * star v)
  rw [add_sub_cancel_right, norm_mul, norm_star, hv, mul_one] at hh
  linarith


theorem actualUnramifiedSelected_bound_first87
    (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (hu : IsCoprime u p)
    (hQ : (4 : ℝ) ≤ Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (87 / 100 : ℝ) ≤ x.re) (hw : (1 / 2 : ℝ) ≤ w.re)
    (hz : (17 / 50 : ℝ) ≤ z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖ ≤ 961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one
    (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : (6 : ℕ) ≠ 0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta | heta
  · have hA : actualAPhase eta p = 0 := by simp [actualAPhase, heta]
    rw [heta, hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound_first87 _ _ _ _ x w z hQ
      (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end SevenEighths.ProbeEuler
end

end OAI
