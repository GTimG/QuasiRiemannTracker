/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Positive Newton children use the literal divided scales and moving puncture. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardFull

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSecondHeightFamily QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered Record1252270103Source
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def newtonPositiveChild (η : Character) (R A₁ A₂ : Ideal O) (d : IdealPair)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ Y₁ Y₂ : ℝ) (z : O) : ℂ :=
  frozenCenteredRow (rowWeight η (fixedBadMask*idealGenerator R) 1 z t) W₁ W₂
    (A₁*d.1) (A₂*d.2) b X₁ X₂ Y₁ Y₂ (X₁*X₂)*
      ((Real.sqrt (∏i,P i):ℂ)⁻¹*∏i,rowSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t)

theorem newton_positive_child_row (η : Character) (R A₁ A₂ : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b : ℝ) (hb : 0≤b)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hXY : Y₁*Y₂=X₁*X₂) (z : O) :
    newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t X₁ X₂ Y₁ Y₂ z=
      ((squarefreeIndicator ((A₁*d.1)*(A₂*d.2)):ℂ)*ordinaryHoleIndicator (A₁*d.1) (A₂*d.2))*
        (squarefreePositiveSlotRow η (fixedBadMask*idealGenerator (R*(d.1*d.2))) 1 z
          W₁ W₂ b S β P t X₁ X₂-
         squarefreePositiveSlotRow η (fixedBadMask*idealGenerator (R*(d.1*d.2))) 1 z
          W₁ W₂ b S β P t Y₁ Y₂) := by
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
    intro i hi
    exact (rowSlot_newton_puncture η R (d.1*d.2) 1 z t (S i) (β i) (havoid i)).symm
  unfold newtonPositiveChild
  rw [frozen_centered_row_excluded η (fixedBadMask*idealGenerator R) 1 z hm hm2
    (A₁*d.1) (A₂*d.2) (mul_ne_zero hA₁ hd.1) (mul_ne_zero hA₂ hd.2.1)
    W₁ W₂ b t X₁ X₂ Y₁ Y₂ (X₁*X₂) hb hX₁ hX₂ hY₁ hY₂ hs₁ hs₂,hslots]
  unfold centeredSquarefreeRow squarefreePositiveSlotRow
  rw [hw,hXY,Real.sqrt_mul (mul_pos hX₁ hX₂).le]
  simp only [Complex.ofReal_mul,mul_inv_rev]
  ring

/-- Genuine restored ordinary source bounds on all shorter scales imply
this literal normalized cofactor child bound, with R*d and the same keep. -/
theorem newton_positive_child_energy (η : Character) (R A₁ A₂ : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (d : IdealPair) (hd : GoodPair d)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b : ℝ) (hb : 0≤b)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hP : ∀i,0<P i) (havoid : ∀i I,I∈S i→IsCoprime I (d.1*d.2))
    (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hXY : Y₁*Y₂=X₁*X₂)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H) (hΦ : ∀x,0≤(Φ x).re)
    (E δ B U : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : b^2*X₁*X₂≤U^B)
    (hordinary : ∀Z₁ Z₂ : ℝ,0<Z₁ →0<Z₂ →
      ((Z₁≤X₁ ∧ Z₂≤X₂) ∨ (Z₁≤Y₁ ∧ Z₂≤Y₂)) →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*idealGenerator (R*(d.1*d.2)))
        1 t W₁ W₂ S β P Z₁ Z₂ keep Φ H≤E) :
    (∑'z : O,if keep z then ‖newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t X₁ X₂ Y₁ Y₂ z‖^2*
      (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0)≤
      4*(holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  let m := fixedBadMask*idealGenerator (R*(d.1*d.2))
  let f := fun z=>squarefreePositiveSlotRow η m 1 z W₁ W₂ b S β P t X₁ X₂
  let g := fun z=>squarefreePositiveSlotRow η m 1 z W₁ W₂ b S β P t Y₁ Y₂
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0
  have hu (z : O) : 0≤u z := by dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have hc : ‖((squarefreeIndicator ((A₁*d.1)*(A₂*d.2)):ℂ)*ordinaryHoleIndicator (A₁*d.1) (A₂*d.2))‖^2≤1 := by
    unfold squarefreeIndicator ordinaryHoleIndicator
    split_ifs <;> norm_num
  have hn (z : O) : ‖newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t X₁ X₂ Y₁ Y₂ z‖^2≤
      2*(‖f z‖^2+‖g z‖^2) := by
    rw [newton_positive_child_row η R A₁ A₂ hA₁ hA₂ hAR d hd W₁ W₂ b hb hs₁ hs₂
      S β P hP havoid t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hXY z,norm_mul,mul_pow]
    apply (mul_le_of_le_one_left (sq_nonneg _) hc).trans
    change ‖f z-g z‖^2≤_
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f z) (g z)) 2
    nlinarith [sq_nonneg (‖f z‖-‖g z‖)]
  have hx := forward_energy_transfer η m 1 W₁ W₂ b hs₁ hs₂ S β P hP t X₁ X₂ hX₁ hX₂
    keep Φ H hH hΦ E hE δ B U hδ hB hU hcut
    (fun Z₁ Z₂ hz₁ hz₂ he₁ he₂=>hordinary Z₁ Z₂ hz₁ hz₂ (Or.inl ⟨he₁,he₂⟩))
  have hy := forward_energy_transfer η m 1 W₁ W₂ b hs₁ hs₂ S β P hP t Y₁ Y₂ hY₁ hY₂
    keep Φ H hH hΦ E hE δ B U hδ hB hU (by simpa only [mul_assoc,hXY] using hcut)
    (fun Z₁ Z₂ hz₁ hz₂ he₁ he₂=>hordinary Z₁ Z₂ hz₁ hz₂ (Or.inr ⟨he₁,he₂⟩))
  apply Real.tsum_le_of_sum_le
  · intro z
    change 0≤(if keep z then _ else 0)
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  intro rows
  have hfx := squarefree_finite_energy_le η m 1 W₁ W₂ b S β P t X₁ X₂ keep Φ H hH hΦ rows
  have hgy := squarefree_finite_energy_le η m 1 W₁ W₂ b S β P t Y₁ Y₂ keep Φ H hH hΦ rows
  have he : (∑z∈rows,if keep z then ‖newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t X₁ X₂ Y₁ Y₂ z‖^2*
      (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0)≤
      2*((∑z∈rows,‖f z‖^2*u z)+(∑z∈rows,‖g z‖^2*u z)) := by
    rw [←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hh := mul_le_mul_of_nonneg_right (hn z) (hu z)
    dsimp only [u] at hh ⊢
    split_ifs at hh ⊢ <;> nlinarith
  exact he.trans (by dsimp only [f,g,u] at *;nlinarith)

/-- Amplifier-pool avoidance supplies the complete assigned divisor mask on
every actual marked prime, including repeated or overlapping marked pools. -/
theorem newton_divisor_avoids_marked (s : CenteredMomentCommonRadialData.Input ι)
    (P S A : Finset (Ideal O)) (hSP : S⊆P) (hAS : A⊆S)
    (hp : ∀p∈P,Prime p) (havoid : ∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (i : ι) (I : Ideal O) (hI : I∈s.slots i) :
    IsCoprime I ((QRH.Record1252270103Low.newtonDivisorPair S A).1*
      (QRH.Record1252270103Low.newtonDivisorPair S A).2) := by
  have hc (p : Ideal O) (hpin : p∈P) : IsCoprime I p := by
    letI : I.IsMaximal := (Ideal.isPrime_of_prime (s.prime i I hI)).isMaximal (s.prime i I hI).ne_zero
    letI : p.IsMaximal := (Ideal.isPrime_of_prime (hp p hpin)).isMaximal (hp p hpin).ne_zero
    apply Ideal.isCoprime_of_isMaximal
    intro he
    exact havoid p hpin i I hI (by rw [he])
  unfold QRH.Record1252270103Low.newtonDivisorPair
  apply IsCoprime.mul_right
  · exact IsCoprime.prod_right (fun p hpa=>hc p (hSP (hAS hpa)))
  · exact IsCoprime.prod_right (fun p hpa=>hc p (hSP (Finset.mem_sdiff.mp hpa).1))

theorem newton_positive_child_cofactor (η : Character) (R A₁ A₂ : Ideal O) (d : IdealPair)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ Y₁ Y₂ : ℝ) (z : O) :
    frozenCenteredRow (rowWeight η (fixedBadMask*idealGenerator R) 1 z t) W₁ W₂
      (A₁*d.1) (A₂*d.2) b (X₁/d.1.absNorm) (X₂/d.2.absNorm)
      (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) ((X₁*X₂)/pairNorm d)*
      ((Real.sqrt (∏i,P i):ℂ)⁻¹*∏i,rowSlot η (fixedBadMask*idealGenerator R) 1 z (S i) (β i) t)=
    newtonPositiveChild η R A₁ A₂ d W₁ W₂ b S β P t
      (X₁/d.1.absNorm) (X₂/d.2.absNorm) (Y₁/d.1.absNorm) (Y₂/d.2.absNorm) z := by
  simp only [newtonPositiveChild,pairNorm,div_mul_div_comm]

end
end OAI.SevenEighths.Record1252270103Second
#print axioms OAI.SevenEighths.Record1252270103Second.newton_positive_child_row
#print axioms OAI.SevenEighths.Record1252270103Second.newton_positive_child_energy

#print axioms OAI.SevenEighths.Record1252270103Second.newton_divisor_avoids_marked
#print axioms OAI.SevenEighths.Record1252270103Second.newton_positive_child_cofactor
