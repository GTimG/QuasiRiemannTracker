/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Submissions.arvi_selected_leaf.JointDetector.SlotWordProducer

/-! Uniform late-constant absorption for the actual selected slot word.
The divisor exponent is chosen before the slot count. Word degree and fixed
coefficient bounds enter only the later constant and height threshold. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open WholeWordAmplification SlotWordProducer
local notation "O" => ActualEisensteinCubic.O

theorem finite_word_degree_bound (N r : ℕ) (target T W wmin : ℝ)
    (ht : 0 ≤ target) (hT : target ≤ T) (hw : 0 < wmin) (hW : wmin ≤ W)
    (hr : (r : ℝ) ≤ (target/W+1)*N) :
    r ≤ Nat.ceil ((T/wmin+1)*N) := by
  have hW0 : 0 < W := hw.trans_le hW
  have hdiv : target/W ≤ T/wmin :=
    (div_le_div_of_nonneg_left ht hw hW).trans (div_le_div_of_nonneg_right hT hw.le)
  have hh := hr.trans (mul_le_mul_of_nonneg_right (add_le_add hdiv le_rfl) (Nat.cast_nonneg N))
  exact_mod_cast hh.trans (Nat.le_ceil _)

/-- Actual all-source inverse amplification with uniform constants over
all literal descriptors and every target in a fixed bounded interval. -/
theorem uniform_slot_crossing (P T loss : ℝ) (hP : 0 ≤ P) (hT : 0 ≤ T) (hloss : 0 < loss)
    (N : ℕ) (Cslot wmin : ℝ) (hCslot : 0 ≤ Cslot) (hwmin : 0 < wmin) :
    ∃ K Z₀ : ℝ, 0 < K ∧ ∀ (Z L mesh δ target : ℝ) (d : SelectedSlotData N)
      (rows : Finset O) (S : Finset (Ideal O)),
      Z₀ ≤ Z → 1 ≤ L → L ≤ Z^P → 0 ≤ mesh → mesh ≤ 1 →
      0 ≤ δ → δ ≤ 1 → 0 ≤ target → target ≤ T →
      d.Bounded Z mesh Cslot → d.Selects Z rows → d.HasSlope δ → wmin ≤ ∑ i, d.width i →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      ∃ (Y : ℝ) (merged : Finset (Ideal O)),
        L*Z^target ≤ Y ∧ Y ≤ L*Z^(target+mesh+loss) ∧
        (∀ I ∈ merged, (Ideal.absNorm I : ℝ) ≤ Y) ∧
        selectedNorm rows S ≤ K*Z^loss*selectedNorm rows merged/(Y/L)^δ := by
  let ε := loss/(P+2*T+3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heps : (P+2*T+2)*ε ≤ loss := by
    have hid : ε*(P+2*T+3) = loss := by dsimp [ε]; field_simp
    nlinarith
  let R := Nat.ceil ((T/wmin+1)*N)
  let M := (2 : ℝ)^R
  have hM : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hM0 : 0 < M := by linarith
  let Dword := ∑ r ∈ Finset.range (R+1), wordDivisorConstant r ε hε
  have hDw : 0 ≤ Dword := Finset.sum_nonneg fun r hr => (wordDivisorConstant_pos r ε hε).le
  let Ccoeff := (max 1 Cslot)^R
  have hCc : 0 < Ccoeff := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  have hdivCpos := idealDivisorConstant_pos ε hε
  let K := Dword*Ccoeff*idealDivisorConstant ε hε*(M^ε)^2*M+1
  have hK : 0 < K := by dsimp [K]; positivity
  let Z₀ := max 2 (M^(1/loss))
  refine ⟨K,Z₀,hK,?_⟩
  intro Z L mesh δ target d rows S hZ₀ hL hLP hm hm1 hδ hδ1 ht htT hb hsel hslope hw hS
  have hz2 : 2 ≤ Z := (le_max_left _ _).trans hZ₀
  have hz1 : 1 ≤ Z := by linarith
  have hz : 0 < Z := by linarith
  have hL0 : 0 < L := by linarith
  have hlate : M ≤ Z^loss := by
    calc
      _ = (M^(1/loss))^loss := by rw [← Real.rpow_mul hM0.le,one_div_mul_cancel hloss.ne',Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hM0.le _)
        ((le_max_right _ _).trans hZ₀) hloss.le
  obtain ⟨r,f,hmlo,hmhi,hr,hword,hmerged,hinverse⟩ := slot_crossing_amplification d rows S Z mesh Cslot L δ target ε
    hz1 hm hCslot hL0.le ht hε hb hsel (hwmin.trans_le hw) hslope hS
  have hrR : r ≤ R := finite_word_degree_bound N r target T (∑ i, d.width i) wmin ht htT hwmin hw hr
  let m := wordWidth d f
  let X := wordScale d f Z
  let Y := L*X
  let merged := idealProductSources (S.erase 0) (amplifierSources d f)
  have hm0 : 0 ≤ m := ht.trans hmlo
  have hmT : m ≤ T+1 := by dsimp [m]; linarith
  have hX0 : 0 < X := by dsimp [X,wordScale]; positivity
  have hY0 : 0 < Y := mul_pos hL0 hX0
  have htwo : (2 : ℝ)^r ≤ M := pow_le_pow_right₀ (by norm_num) hrR
  have hXU : X ≤ M*Z^(T+1) := by
    dsimp [X,wordScale]
    exact mul_le_mul htwo (Real.rpow_le_rpow_of_exponent_le hz1 hmT) (Real.rpow_nonneg hz.le _) hM0.le
  have hYU : Y ≤ M*Z^(P+T+1) := by
    calc
      _ ≤ Z^P*(M*Z^(T+1)) := mul_le_mul hLP hXU hX0.le (Real.rpow_nonneg hz.le _)
      _ = _ := by rw [show P+T+1 = P+(T+1) by ring,Real.rpow_add hz P (T+1)]; ring
  have hDword : wordDivisorConstant r ε hε ≤ Dword := Finset.single_le_sum
    (fun i hi => (wordDivisorConstant_pos i ε hε).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hrR))
  have hcoeff : Cslot^r ≤ Ccoeff :=
    (pow_le_pow_left₀ hCslot (le_max_right _ _) r).trans (pow_le_pow_right₀ (le_max_left _ _) hrR)
  have htwopow : ((2 : ℝ)^r)^δ ≤ M := by
    calc
      _ ≤ (2 : ℝ)^r := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (one_le_pow₀ (by norm_num : (1 : ℝ)≤2) (n := r)) hδ1
      _ ≤ _ := htwo
  have hpoly : X^ε*Y^ε ≤ (M^ε)^2*Z^loss := by
    calc
      _ ≤ (M*Z^(T+1))^ε*(M*Z^(P+T+1))^ε := mul_le_mul
        (Real.rpow_le_rpow hX0.le hXU hε.le) (Real.rpow_le_rpow hY0.le hYU hε.le)
        (Real.rpow_nonneg hY0.le _) (Real.rpow_nonneg (by positivity) _)
      _ = (M^ε)^2*Z^((P+2*T+2)*ε) := by
        rw [Real.mul_rpow hM0.le (Real.rpow_nonneg hz.le _),Real.mul_rpow hM0.le (Real.rpow_nonneg hz.le _),
          ← Real.rpow_mul hz.le, ← Real.rpow_mul hz.le]
        calc
          _ = (M^ε)^2*(Z^((T+1)*ε)*Z^((P+T+1)*ε)) := by ring
          _ = _ := by rw [← Real.rpow_add hz]; congr 1; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 heps) (sq_nonneg _)
  have hcost : (wordDivisorConstant r ε hε*X^ε*Cslot^r)*idealDivisorConstant ε hε*Y^ε*((2 : ℝ)^r)^δ ≤ K*Z^loss := by
    calc
      _ = wordDivisorConstant r ε hε*Cslot^r*idealDivisorConstant ε hε*(X^ε*Y^ε)*((2 : ℝ)^r)^δ := by ring
      _ ≤ Dword*Ccoeff*idealDivisorConstant ε hε*((M^ε)^2*Z^loss)*M := by
        gcongr
      _ = (Dword*Ccoeff*idealDivisorConstant ε hε*(M^ε)^2*M)*Z^loss := by ring
      _ ≤ _ := by dsimp [K]; gcongr; linarith
  have hden : Z^(δ*m)*((2 : ℝ)^r)^δ = (Y/L)^δ := by
    have hy : Y/L = X := by dsimp [Y]; field_simp
    rw [hy]
    dsimp [X,wordScale,m]
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hz.le _),← Real.rpow_mul hz.le]
    rw [mul_comm δ (wordWidth d f)]
    ring
  refine ⟨Y,merged,?_,?_,fun I hI => (hmerged I hI).2,?_⟩
  · calc
      _ ≤ L*Z^m := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1 hmlo) hL0.le
      _ ≤ _ := by
        dsimp [Y,X,wordScale,m]
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.rpow_nonneg hz.le _) (one_le_pow₀ (by norm_num))) hL0.le
  · calc
      _ ≤ L*(M*Z^(target+mesh)) := by
        dsimp [Y,X,wordScale]
        gcongr
      _ ≤ L*(Z^loss*Z^(target+mesh)) := by gcongr
      _ = _ := by rw [← Real.rpow_add hz]; congr 1; congr 1; ring
  · have hnorm0 : 0 ≤ selectedNorm rows merged := sq_nonneg _
    apply hinverse.trans
    have hid : (wordDivisorConstant r ε hε*X^ε*Cslot^r)*idealDivisorConstant ε hε*Y^ε*
        selectedNorm rows merged/Z^(δ*m) =
        ((wordDivisorConstant r ε hε*X^ε*Cslot^r)*idealDivisorConstant ε hε*Y^ε*((2 : ℝ)^r)^δ)*
          selectedNorm rows merged/(Y/L)^δ := by
      rw [← hden]
      field_simp
    change (wordDivisorConstant r ε hε*X^ε*Cslot^r)*idealDivisorConstant ε hε*Y^ε*
        selectedNorm rows merged/Z^(δ*m) ≤ _
    rw [hid]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcost hnorm0)
      (Real.rpow_nonneg (div_nonneg hY0.le hL0.le) _)

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.uniform_slot_crossing
