/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual Newton cofactor families from their ordinary fixed-anchor admission. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FamilyRestoration
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonBound
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => ActualEisensteinCubic.O
variable {ι Row : Type*} [Fintype ι]

lemma normalized_slots_product (η : Character) (m A z : O)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i) (t : ℝ) :
    (∏i,normalizedSlot η m A z (S i) (β i) t (P i))=
      (Real.sqrt (∏i,P i):ℂ)⁻¹*∏i,rowSlot η m A z (S i) (β i) t := by
  simp only [normalizedSlot,Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  rw [Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_prod]

/-- The normalized singleton expression used by HIGH is precisely the literal
cofactor child at the divided scales. -/
theorem frozen_cofactor_normalized_slots (η : Character) (R A₁ A₂ : Ideal O) (d : IdealPair)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ)
    (P : ι→ℝ) (hP : ∀i,0<P i) (t X₁ X₂ Y₁ Y₂ : ℝ) (z : O) :
    frozenCenteredRow (rowWeight η (fixedBadMask*idealGenerator R) 1 z t) W₁ W₂
      (A₁*d.1) (A₂*d.2) b (X₁/d.1.absNorm) (X₂/d.2.absNorm)
      (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) ((X₁*X₂)/pairNorm d)*
      (∏i,normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t (P i))=
    newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t
      (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) z := by
  rw [normalized_slots_product η _ 1 z S β P hP t]
  exact newton_positive_child_cofactor η R A₁ A₂ d W₁ W₂ b S β P t X₁ X₂ Y₁ Y₂ z

/-- The family version retains moving characters, physical numerators and all
original weights. The remaining ordinary family premise is supplied by
`global_fixed_missing_positive_family`, using one fixed earlier source. -/
theorem newton_positive_finite_family
    (rows : Finset Row) (τ : Row→Character) (t weight : Row→ℝ) (z : Row→O)
    (hw : ∀u∈rows,0≤weight u) (R A₁ A₂ : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b : ℝ) (hb : 0≤b)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hXY : Y₁*Y₂=X₁*X₂)
    (E δ B U : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : b^2*X₁*X₂≤U^B)
    (hordinary : ∀Z₁ Z₂ : ℝ,0<Z₁ →0<Z₂ →
      ((Z₁≤X₁ ∧ Z₂≤X₂) ∨ (Z₁≤Y₁ ∧ Z₂≤Y₂)) →
      (∑u∈rows,‖positiveSlotRow (τ u) (fixedBadMask*idealGenerator (R*(d.1*d.2)))
        1 (z u) W₁ W₂ S β P (t u) Z₁ Z₂‖^2*weight u)≤E) :
    (∑u∈rows,‖newtonPositiveChild (τ u) R A₁ A₂ d W₁ W₂ b S β P
      (t u) X₁ X₂ Y₁ Y₂ (z u)‖^2*weight u)≤
      4*(holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
        eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  let m := fixedBadMask*idealGenerator (R*(d.1*d.2))
  let f := fun u=>squarefreePositiveSlotRow (τ u) m 1 (z u) W₁ W₂ b S β P (t u) X₁ X₂
  let g := fun u=>squarefreePositiveSlotRow (τ u) m 1 (z u) W₁ W₂ b S β P (t u) Y₁ Y₂
  have hc : ‖((squarefreeIndicator ((A₁*d.1)*(A₂*d.2)):ℂ)*ordinaryHoleIndicator (A₁*d.1) (A₂*d.2))‖^2≤1 := by
    unfold squarefreeIndicator ordinaryHoleIndicator
    split_ifs <;> norm_num
  have hn (u : Row) : ‖newtonPositiveChild (τ u) R A₁ A₂ d W₁ W₂ b S β P
      (t u) X₁ X₂ Y₁ Y₂ (z u)‖^2≤2*(‖f u‖^2+‖g u‖^2) := by
    rw [newton_positive_child_row (τ u) R A₁ A₂ hA₁ hA₂ hAR d hd W₁ W₂ b hb hs₁ hs₂
      S β P hP havoid (t u) X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY (z u),norm_mul,mul_pow]
    apply (mul_le_of_le_one_left (sq_nonneg _) hc).trans
    change ‖f u-g u‖^2≤_
    have hh:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f u) (g u)) 2
    nlinarith [sq_nonneg (‖f u‖-‖g u‖)]
  have hx:=forward_finite_family_rankin rows τ (fun _=>m) (fun _=>1) z t weight hw
    W₁ W₂ b hs₁ hs₂ S β P hP X₁ X₂ hX₁ hX₂ E hE δ B U hδ hB hU hcut
    (fun Z₁ Z₂ hz₁ hz₂ he₁ he₂=>hordinary Z₁ Z₂ hz₁ hz₂ (Or.inl ⟨he₁,he₂⟩))
  have hy:=forward_finite_family_rankin rows τ (fun _=>m) (fun _=>1) z t weight hw
    W₁ W₂ b hs₁ hs₂ S β P hP Y₁ Y₂ hY₁ hY₂ E hE δ B U hδ hB hU
    (by simpa only [mul_assoc,hXY] using hcut)
    (fun Z₁ Z₂ hz₁ hz₂ he₁ he₂=>hordinary Z₁ Z₂ hz₁ hz₂ (Or.inr ⟨he₁,he₂⟩))
  have hh : (∑u∈rows,‖newtonPositiveChild (τ u) R A₁ A₂ d W₁ W₂ b S β P
      (t u) X₁ X₂ Y₁ Y₂ (z u)‖^2*weight u)≤
      2*((∑u∈rows,‖f u‖^2*weight u)+(∑u∈rows,‖g u‖^2*weight u)) := by
    rw [←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    exact (mul_le_mul_of_nonneg_right (hn u) (hw u hu)).trans_eq (by ring)
  exact hh.trans (by dsimp only [f,g] at *;linarith)

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.normalized_slots_product
#print axioms QRH.Record1252270103Source.Admission.frozen_cofactor_normalized_slots
#print axioms QRH.Record1252270103Source.Admission.newton_positive_finite_family
