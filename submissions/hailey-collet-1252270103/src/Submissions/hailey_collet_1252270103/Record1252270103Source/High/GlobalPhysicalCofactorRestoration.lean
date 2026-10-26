/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal frozen centered cofactors are restored at all positive shorter scales.
The same row and original full singleton slots are kept in the raw inlet. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FamilyNewton
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalJointNewton
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentSecondHeightFamily
open CenteredMomentRetainedEnergy QRH.Record1252270103Low
open CenteredMomentWholeSlotDeletion
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O"=>ActualEisensteinCubic.O

def cofactorRestorationCost (δ B Z : ℝ) : ℝ :=
  4*(holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
    eulerBound 432 (1/2+δ/(B+1)))*Z^δ))^2

lemma cofactorRestorationCost_nonneg (δ B Z : ℝ) : 0≤cofactorRestorationCost δ B Z := by
  unfold cofactorRestorationCost
  positivity

theorem newton_cofactor_pointwise_from_ordinary {ι J : Type*} [Fintype ι] [Fintype J]
    (s : Input ι) (A₁ A₂ R : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R)
    (S A : Finset (Ideal O)) (hd : GoodPair (newtonDivisorPair S A))
    (τ : Character) (t : ℝ) (z : O) (b : ℝ) (hb : 0≤b)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (hW₁ : s.W₁=(W₁:ℝ→ℂ)) (hW₂ : s.W₂=(W₂:ℝ→ℂ))
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b)
    (slots : J→Finset (Ideal O)) (coeff : J→Ideal O→ℂ) (scale : J→ℝ)
    (hscale : ∀i,0<scale i)
    (havoid : ∀i I,I∈slots i→IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))
    (E δ B Z : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hZ : 1≤Z)
    (hcut : b^2*(s.X₁/(newtonDivisorPair S A).1.absNorm)*
      (s.X₂/(newtonDivisorPair S A).2.absNorm)≤Z^B)
    (hordinary : ∀X₁ X₂:ℝ,0<X₁→0<X₂→
      ((X₁≤s.X₁/(newtonDivisorPair S A).1.absNorm ∧ X₂≤s.X₂/(newtonDivisorPair S A).2.absNorm) ∨
       (X₁≤s.Y₁/(newtonDivisorPair S A).1.absNorm ∧ X₂≤s.Y₂/(newtonDivisorPair S A).2.absNorm))→
      ‖positiveSlotRow τ (fixedBadMask*idealGenerator (R*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)))
        1 z W₁ W₂ slots coeff scale t X₁ X₂‖^2≤E) :
    ‖newtonCofactorPlain s A₁ A₂ R b S A τ t z*
      (∏i,normalizedSlot τ (fixedBadMask*idealGenerator R) 1 z (slots i) (coeff i) t (scale i))‖^2≤
      cofactorRestorationCost δ B Z*E := by
  let d:=newtonDivisorPair S A
  have hx₁ : 0<s.X₁/d.1.absNorm:=(shorten_positive s.X₁_pos hd.1).1
  have hx₂ : 0<s.X₂/d.2.absNorm:=(shorten_positive s.X₂_pos hd.2.1).1
  have hy₁ : 0<s.Y₁/d.1.absNorm:=(shorten_positive s.Y₁_pos hd.1).1
  have hy₂ : 0<s.Y₂/d.2.absNorm:=(shorten_positive s.Y₂_pos hd.2.1).1
  have hxy : (s.Y₁/d.1.absNorm)*(s.Y₂/d.2.absNorm)=
      (s.X₁/d.1.absNorm)*(s.X₂/d.2.absNorm) := by
    rw [div_mul_div_comm,div_mul_div_comm,s.same_product]
  have hh:=Admission.newton_positive_finite_family {()} (fun _ : Unit=>τ) (fun _=>t)
    (fun _=>1) (fun _=>z) (by simp) R A₁ A₂ hA₁ hA₂ hAR d hd W₁ W₂ b hb hs₁ hs₂
    slots coeff scale hscale havoid (s.X₁/d.1.absNorm) (s.X₂/d.2.absNorm)
    (s.Y₁/d.1.absNorm) (s.Y₂/d.2.absNorm) hx₁ hx₂ hy₁ hy₂ hxy E δ B Z hE hδ hB hZ hcut
    (by intro X₁ X₂ hx₁ hx₂ hshort;simpa only [Finset.sum_singleton,mul_one] using hordinary X₁ X₂ hx₁ hx₂ hshort)
  simp only [Finset.sum_singleton,mul_one] at hh
  have he:=Admission.frozen_cofactor_normalized_slots τ R A₁ A₂ d W₁ W₂ b slots coeff scale hscale
    t s.X₁ s.X₂ s.Y₁ s.Y₂ z
  rw [←he] at hh
  simpa only [newtonCofactorPlain,hW₁,hW₂,cofactorRestorationCost,d] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.cofactorRestorationCost_nonneg
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.newton_cofactor_pointwise_from_ordinary
