/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal one-corner frozen rows retain both squarefree and ordinary-hole projectors. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.VariableRestoration
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredNewtonPositive
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedLow
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSourceRectangleMask
open CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O
variable {ι Row : Type*} [Fintype ι]

def positiveFrozenRow (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ)
    (A₁ A₂ : Ideal O) (b X₁ X₂ T : ℝ) : ℂ :=
  (Real.sqrt T:ℂ)⁻¹*∑n∈holePairPool b X₁ X₂,
    (squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*ψ (n.1*n.2)*
      ordinaryHoleIndicator (A₁*n.1) (A₂*n.2)*pairProfile W₁ W₂ X₁ X₂ n

lemma positiveFrozenRow_excluded (η : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (W₁ W₂ : ℝ→ℂ) (b t X₁ X₂ T : ℝ) :
    positiveFrozenRow (rowWeight η m A z t) W₁ W₂ A₁ A₂ b X₁ X₂ T=
      ((squarefreeIndicator (A₁*A₂):ℂ)*ordinaryHoleIndicator A₁ A₂)*
        ((Real.sqrt T:ℂ)⁻¹*squarefreePlainSum
          (rowWeight η (m*idealGenerator (A₁*A₂)) A z t) W₁ W₂ b X₁ X₂) := by
  rw [squarefreePlainSum_eq_hole_sum]
  unfold positiveFrozenRow
  rw [mul_left_comm _ ((Real.sqrt T:ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hg:=holePairPool_good hn
  have hh:=(ordinarySmallHole_iff_good hg.1 hg.2.1).mpr hg
  rw [ordinaryHoleIndicator_frozen A₁ A₂ n.1 n.2 hA₁ hA₂ hg.1 hg.2.1 hh,
    squarefree_frozen_mask,←rowWeight_ideal_mask η m A z t hml hm2]
  ring

lemma positiveFrozenRow_normalized_slots
    (η : Character) (R A₁ A₂ : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (z : O) :
    positiveFrozenRow (rowWeight η (fixedBadMask*idealGenerator R) 1 z t) W₁ W₂
      (A₁*d.1) (A₂*d.2) b X₁ X₂ (X₁*X₂)*
        (∏i,normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t (P i))=
      ((squarefreeIndicator ((A₁*d.1)*(A₂*d.2)):ℂ)*ordinaryHoleIndicator (A₁*d.1) (A₂*d.2))*
        squarefreePositiveSlotRow η (fixedBadMask*idealGenerator (R*(d.1*d.2))) 1 z
          W₁ W₂ b S β P t X₁ X₂ := by
  have hm : goodLambda∣fixedBadMask*idealGenerator R :=
    (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣fixedBadMask*idealGenerator R :=
    (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hw : rowWeight η ((fixedBadMask*idealGenerator R)*idealGenerator ((A₁*d.1)*(A₂*d.2))) 1 z t=
      rowWeight η (fixedBadMask*idealGenerator (R*(d.1*d.2))) 1 z t := by
    ext I
    exact rowWeight_newton_puncture η R A₁ A₂ d.1 d.2 hAR 1 z t I
  have hslots : (∏i,rowSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t)=
      ∏i,rowSlot η (fixedBadMask*idealGenerator (R*(d.1*d.2))) 1 z (S i) (β i) t := by
    apply Finset.prod_congr rfl
    intro i _
    exact (rowSlot_newton_puncture η R (d.1*d.2) 1 z t (S i) (β i) (havoid i)).symm
  have hnormalized : (∏i,normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t (P i))=
      (Real.sqrt (∏i,P i):ℂ)⁻¹*∏i,rowSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t := by
    simp only [normalizedSlot,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
    rw [Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_prod]
  rw [positiveFrozenRow_excluded η (fixedBadMask*idealGenerator R) 1 z hm hm2
    (A₁*d.1) (A₂*d.2) (mul_ne_zero hA₁ hd.1) (mul_ne_zero hA₂ hd.2.1),hnormalized,hslots,hw]
  unfold squarefreePositiveSlotRow
  rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le]
  simp only [Complex.ofReal_mul,mul_inv_rev]
  ring

theorem positive_frozen_finite_family
    (rows : Finset Row) (τ : Row→Character) (t weight : Row→ℝ) (z : Row→O)
    (hw : ∀u∈rows,0≤weight u) (R A₁ A₂ : Row→Ideal O)
    (hA₁ : ∀u∈rows,A₁ u≠0) (hA₂ : ∀u∈rows,A₂ u≠0)
    (hAR : ∀u∈rows,A₁ u*A₂ u∣R u) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (X₁ X₂ : Row→ℝ) (hX : ∀u∈rows,0<X₁ u ∧ 0<X₂ u)
    (E δ B U : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : ∀u∈rows,b^2*X₁ u*X₂ u≤U^B)
    (hraw : ∀Y₁ Y₂ : Row→ℝ,
      (∀u∈rows,0<Y₁ u ∧ 0<Y₂ u ∧ Y₁ u≤X₁ u ∧ Y₂ u≤X₂ u) →
      (∑u∈rows,‖positiveSlotRow (τ u) (fixedBadMask*idealGenerator (R u*(d.1*d.2)))
        1 (z u) W₁ W₂ S β P (t u) (Y₁ u) (Y₂ u)‖^2*weight u)≤E) :
    (∑u∈rows,‖positiveFrozenRow (rowWeight (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u) (t u))
      W₁ W₂ (A₁ u*d.1) (A₂ u*d.2) b (X₁ u) (X₂ u) (X₁ u*X₂ u)*
      (∏i,normalizedSlot (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u)
        (S i) (β i) (t u) (P i))‖^2*weight u)≤
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
        eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  have hh:=forward_finite_family_variable_rankin rows τ
    (fun u=>fixedBadMask*idealGenerator (R u*(d.1*d.2))) (fun _=>1) z t weight hw
    W₁ W₂ b hs₁ hs₂ S β P hP X₁ X₂ hX E hE δ B U hδ hB hU hcut hraw
  apply le_trans _ hh
  apply Finset.sum_le_sum
  intro u hu
  rw [positiveFrozenRow_normalized_slots (τ u) (R u) (A₁ u) (A₂ u)
    (hA₁ u hu) (hA₂ u hu) (hAR u hu) d hd W₁ W₂ b S β P hP havoid
    (t u) (X₁ u) (X₂ u) (hX u hu).1 (hX u hu).2 (z u),norm_mul,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (hw u hu)
  apply mul_le_of_le_one_left (sq_nonneg _)
  unfold squarefreeIndicator ordinaryHoleIndicator
  split_ifs <;> norm_num
end
end QRH.Record1252270103Source.Admission.RetainedLow
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.positiveFrozenRow_excluded
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.positiveFrozenRow_normalized_slots
#print axioms QRH.Record1252270103Source.Admission.RetainedLow.positive_frozen_finite_family
