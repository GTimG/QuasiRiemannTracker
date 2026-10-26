/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The exact finite detector field follows from the earlier ordinary InitialAffineAt.
Based on prior NaturalMarkedPlain's literal polynomial transport (Apache-2.0). -/
import Submissions.hailey_collet_1252270103.Record12518109Source.InitialMoment
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.NaturalMarkedPlainField
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentPositiveSummability CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentHeckeTwist CenteredMomentDetectorDictionary
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainProfileControl
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ConcreteTraceCRT QuadraticInitialBound Cycle61MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem initialAffineAt_finite_polynomials {Row : Type*}
    (W : ℝ→ℂ) (bslot a b bΦ Lslot lo hi ε U : ℝ) (hU : 0<U) (face : SourceFace)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : InitialAffineAt (α:=α) M H hH face W bslot a b bΦ Lslot lo hi 1 1 ε U η η₀ Q degree seminorms C)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
 (p : Profiles a b) (X₁ X₂ σd td : ℝ)
    (V₁ V₂ : ℝ→ℂ) (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hcap : face.Admissible (length U X₁) (length U X₂) (∑s,w s) 1)
    (Φ : 𝓢(ℝ,ℂ)) (hsupport : Function.support (Φ : ℝ→ℂ)⊆Iic bΦ)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u)) (hΦ : ∀x,0≤(Φ x).re)
    (hone : ∀u∈rows,Φ (‖eisEmbedding (row u)‖^2/U)=1) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2)≤
      C*diagonalControl Φ*(p.control seminorms)^2*
        (1+height)^degree*U^(1+ε) := by
  have hfinite := finite_positive_energy (Slot:=slots) (rows.image row) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
    (p.profile 0) (p.profile 1) b b X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun s=>primePool M H bslot (U^(w s)))
    (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
    (fun s=>U^(w s)) (initialKeep η (internalQ Q η₀)) Φ U hU
    (fun u hu=>by obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu; exact hkeep v hv) hΦ
    (fun u hu=>by obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu; exact hone v hv)
  have he := hinput slots θ w σ v 0 height hw hwm hσlo hσhi hheight hv
    1 le_rfl le_rfl Φ hsupport hΦ p X₁ X₂ hX₁ hX₂ hcap
  simp only [Real.rpow_one] at he
  have he := hfinite.trans he
  simp only [abs_zero,add_zero] at he
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product η (χ u) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (row u)
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=>Real.rpow_pos_of_pos hU _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row η (χ u) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 (row u) (hrow u hu) _ _ _


end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.initialAffineAt_finite_polynomials
