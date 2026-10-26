/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Actual finite h and fixed-hole mass preserve the centered reference saving.
The analytic inlet is the already checked ordinary centered rectangle estimate. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CenteredExpand

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O

theorem centered_generic_divisor_transport {ι : Type*} (D : Finset ι)
    (f : ℝ→ℝ→ℝ→ℝ→ℝ→ℂ) (X₁ X₂ Y₁ Y₂ T L α A : ℝ)
    (hT : 0<T) (hL : 0<L)
    (hX₁ : L≤X₁) (hX₂ : L≤X₂) (hY₁ : L≤Y₁) (hY₂ : L≤Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T)
    (d₁ d₂ : ι→ℝ) (w : ι→ℂ)
    (hd₁ : ∀i∈D,1≤d₁ i) (hd₂ : ∀i∈D,1≤d₂ i)
    (hchild : ∀x₁ x₂ y₁ y₂ t' l : ℝ,0<l →
      l≤x₁ →l≤x₂ →l≤y₁ →l≤y₂ →x₁*x₂=t' →y₁*y₂=t' →
      ‖f x₁ x₂ y₁ y₂ t'‖≤A*Real.sqrt t'*l^(-α)) :
    ‖∑i∈D,(w i/(Real.sqrt (d₁ i*d₂ i):ℂ))*
      f (X₁/d₁ i) (X₂/d₂ i) (Y₁/d₁ i) (Y₂/d₂ i) (T/(d₁ i*d₂ i))‖≤
      A*Real.sqrt T*L^(-α)*(∑i∈D,‖w i‖/(d₁ i*d₂ i)^(1-α)) := by
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h₁ : 0<d₁ i:=lt_of_lt_of_le zero_lt_one (hd₁ i hi)
  have h₂ : 0<d₂ i:=lt_of_lt_of_le zero_lt_one (hd₂ i hi)
  have hd : 0<d₁ i*d₂ i:=mul_pos h₁ h₂
  have lo₁:=divisor_common_lower L X₁ (d₁ i) (d₂ i) hL.le hX₁ (hd₁ i hi) (hd₂ i hi)
  have lo₂:=divisor_common_lower L X₂ (d₂ i) (d₁ i) hL.le hX₂ (hd₂ i hi) (hd₁ i hi)
  have ly₁:=divisor_common_lower L Y₁ (d₁ i) (d₂ i) hL.le hY₁ (hd₁ i hi) (hd₂ i hi)
  have ly₂:=divisor_common_lower L Y₂ (d₂ i) (d₁ i) hL.le hY₂ (hd₂ i hi) (hd₁ i hi)
  rw [mul_comm (d₂ i) (d₁ i)] at lo₂ ly₂
  have hc:=hchild _ _ _ _ _ _ (div_pos hL hd) lo₁ lo₂ ly₁ ly₂
    (by rw [div_mul_div_comm,hpX]) (by rw [div_mul_div_comm,hpY])
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hc (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).trans_eq
  calc
    _=(‖w i‖*A)*((Real.sqrt (d₁ i*d₂ i))⁻¹*
        (Real.sqrt (T/(d₁ i*d₂ i))*(L/(d₁ i*d₂ i))^(-α))) := by ring
    _=_ := by rw [centered_divisor_scalar T L (d₁ i*d₂ i) α hT hL hd];ring

theorem centeredHoleRow_bound (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T L α C : ℝ)
    (hL : 0<L) (hX₁ : L≤X₁) (hX₂ : L≤X₂) (hY₁ : L≤Y₁) (hY₂ : L≤Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) (hα : α≤1) (hC : 0≤C)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (hchild : ∀x₁ x₂ y₁ y₂ t' l : ℝ,0<l →
      l≤x₁ →l≤x₂ →l≤y₁ →l≤y₂ →x₁*x₂=t' →y₁*y₂=t' →
      ‖centeredRectangle χ W₁ W₂ t x₁ x₂ y₁ y₂ t'‖≤C*Real.sqrt t'*l^(-α)) :
    ‖centeredHoleRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T‖≤
      (C*mobiusPool.card)*Real.sqrt T*L^(-α) := by
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  rw [centeredHoleRow_mobius η χ m A z hrow W₁ W₂ b t X₁ X₂ Y₁ Y₂ T
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂) hT hs₁ hs₂]
  let d₁:=fun d : Finset PrimeIdeal×Finset PrimeIdeal=>(Ideal.absNorm (mobiusPair d).1:ℝ)
  let d₂:=fun d : Finset PrimeIdeal×Finset PrimeIdeal=>(Ideal.absNorm (mobiusPair d).2:ℝ)
  let w:=fun d : Finset PrimeIdeal×Finset PrimeIdeal=>
    mobiusSign d*rowWeight η m A z t ((mobiusPair d).1*(mobiusPair d).2)
  have hd₁ : ∀d∈mobiusPool,1≤d₁ d:=fun d _=>ideal_norm_one_le (subsetProduct_nonzero _)
  have hd₂ : ∀d∈mobiusPool,1≤d₂ d:=fun d _=>ideal_norm_one_le (subsetProduct_nonzero _)
  have hmass : (∑d∈mobiusPool,‖w d‖/(d₁ d*d₂ d)^(1-α))≤mobiusPool.card := by
    calc
      _≤∑d∈mobiusPool,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hbase : 1≤d₁ d*d₂ d:=one_le_mul_of_one_le_of_one_le (hd₁ d hd) (hd₂ d hd)
        have hpow : 1≤(d₁ d*d₂ d)^(1-α):=Real.one_le_rpow hbase (by linarith)
        exact (div_le_self (norm_nonneg _) hpow).trans (mobius_row_coefficient_norm η m A z t d)
      _=_ := by simp
  have hc:=centered_divisor_transport mobiusPool χ W₁ W₂ t X₁ X₂ Y₁ Y₂ T L α C
    hT hL hX₁ hX₂ hY₁ hY₂ hpX hpY d₁ d₂ w hd₁ hd₂ hchild
  change ‖∑d∈mobiusPool,(w d/(Real.sqrt (d₁ d*d₂ d):ℂ))*
    centeredRectangle χ W₁ W₂ t (X₁/d₁ d) (X₂/d₂ d) (Y₁/d₁ d) (Y₂/d₂ d)
      (T/(d₁ d*d₂ d))‖≤_ 
  apply hc.trans
  exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring)

theorem centeredSquarefreeRow_bound (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
      (HeckeRowClosure.elementHom η) m 1 (A*z) n)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T L α C : ℝ) (hb : 0≤b)
    (hL : 0<L) (hX₁ : L≤X₁) (hX₂ : L≤X₂) (hY₁ : L≤Y₁) (hY₂ : L≤Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) (hα : α<1/2) (hC : 0≤C)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (hchild : ∀x₁ x₂ y₁ y₂ t' l : ℝ,0<l →
      l≤x₁ →l≤x₂ →l≤y₁ →l≤y₂ →x₁*x₂=t' →y₁*y₂=t' →
      ‖centeredRectangle χ W₁ W₂ t x₁ x₂ y₁ y₂ t'‖≤C*Real.sqrt t'*l^(-α)) :
    ‖centeredSquarefreeRow η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T‖≤
      (C*mobiusPool.card*eulerBound 5 (1-α))*Real.sqrt T*L^(-α) := by
  have hT : 0<T:=hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  rw [centeredSquarefreeRow_forward η m A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T hb
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂) hT hs₁ hs₂]
  let D:=divisorPool (holePairPool b (max X₁ Y₁) (max X₂ Y₂))
  let w:=fun d : IdealPair=>(forwardKernel d.1 d.2:ℂ)*rowWeight η m A z t (d.1*d.2)
  let d₁:=fun d : IdealPair=>(Ideal.absNorm d.1:ℝ)
  let d₂:=fun d : IdealPair=>(Ideal.absNorm d.2:ℝ)
  have hg : ∀d∈D,GoodPair d:=fun _ hd=>divisorPool_hole_good hd
  have hd₁ : ∀d∈D,1≤d₁ d:=fun d hd=>ideal_norm_one_le (hg d hd).1
  have hd₂ : ∀d∈D,1≤d₂ d:=fun d hd=>ideal_norm_one_le (hg d hd).2.1
  have hmass : (∑d∈D,‖w d‖/(d₁ d*d₂ d)^(1-α))≤eulerBound 5 (1-α) := by
    apply le_trans _ (forward_good_finite_mass (1-α) (by linarith) D hg)
    apply Finset.sum_le_sum
    intro d hd
    have hn:=pairNorm_pos (hg d hd).1 (hg d hd).2.1
    dsimp only [w,d₁,d₂]
    rw [norm_mul,Complex.norm_intCast]
    apply (div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all η m A z t _))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)).trans_eq
    rw [idealPairWeight_eq_pairNorm,Real.rpow_neg hn.le]
    rfl
  have hh:=centered_generic_divisor_transport D (centeredHoleRow η m A z W₁ W₂ b t)
    X₁ X₂ Y₁ Y₂ T L α (C*mobiusPool.card) hT hL hX₁ hX₂ hY₁ hY₂ hpX hpY d₁ d₂ w hd₁ hd₂
    (fun x₁ x₂ y₁ y₂ t' l hl hx₁ hx₂ hy₁ hy₂ hpx hpy=>
      centeredHoleRow_bound η χ m A z hrow W₁ W₂ b t x₁ x₂ y₁ y₂ t' l α C
        hl hx₁ hx₂ hy₁ hy₂ hpx hpy (by linarith) hC hs₁ hs₂ hchild)
  change ‖∑d∈D,(w d/(Real.sqrt (d₁ d*d₂ d):ℂ))*
    centeredHoleRow η m A z W₁ W₂ b t (X₁/d₁ d) (X₂/d₂ d) (Y₁/d₁ d) (Y₂/d₂ d)
      (T/(d₁ d*d₂ d))‖≤_
  exact hh.trans ((mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring))

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.centeredSquarefreeRow_bound
