/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Actual original aligned pair energy restored to its literal colored canonical
root leaves. The sole downstream energy input is displayed with actual masks. -/
import Candidate.C092.transport.ColoredRootRestoreActual
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentTwist CenteredMomentWholeSlotDeletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.KernelRowPools
open QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open QRH.Cycle092.OrderedPairPhase QRH.Cycle092.TwistedRawBallRootProducer
open QRH.Cycle092.RegularColoredForward
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
local notation "Prime"=>QRH.Record1252270103KernelMass.PrimeIdeal

theorem actual_aligned_restoration {ι:Type} (T:Finset ι) (B ε:ℝ) (hB:1≤B) (hε:0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ Xcap:ℝ,1≤Xcap → ∀ S:Finset Prime,
      (∀ Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤Xcap) →
    ∀ (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
      (hHr:RayOrthogonality.globalUnits M≤Hr) (base η₁ η₂:Character)
      (θ:T→RayQuotient.Characters M Hr) (rows:Finset FreeRow)
      (pool:T→Finset Id) (slotWeight:T→Id→ℂ) (P:T→ℝ),
      (∀ i,supportedPool (pool i)⊆QRH.Record1252270103KernelMass.primeValues S) →
      (∀ i,0<P i) → (∀ i I,I∈pool i → (I.absNorm:ℝ)≤2*P i) →
      (∀ i I,I∈pool i → ‖slotWeight i I‖≤B) →
    ∀ (mark:ι→FreeRow→ℂ) (tMark:ℝ) (W₁ W₂:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hb:0≤b)
      (hs₁:Function.support W₁⊆Set.Icc a b) (hs₂:Function.support W₂⊆Set.Icc a b)
      (hW₁:ContDiff ℝ ∞ W₁) (hW₂:ContDiff ℝ ∞ W₂)
      (t₁ t₂ M₁ M₂ X₁ X₂ Y₁ Y₂ E:ℝ),
      0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → Y₁*Y₂=X₁*X₂ →
      X₁≤M₁ → X₂≤M₂ → Y₁≤M₁ → Y₂≤M₂ → 0≤E →
      (∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*M₁ ∨ (I.absNorm:ℝ)≤b*M₂) →
        QRH.Record1252270103KernelMass.primeValues S ⊇ primeSupport I) →
      (∀ u∈rows,∀ i:T,‖mark i.val u‖=‖normalizedSlot η₁
        (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
        (fun I=>idealCoeff (relativeCharacter M Hr hHr base (θ i)) I*slotWeight i I) tMark (P i)‖) →
    let β:=fun i:T=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr
      (base.product η₁.inverse) (θ i)) I*slotWeight i I) tMark;
    let V₁:=normPowerProfile W₁ a b ha hs₁ hW₁ t₁;
    let V₂:=normPowerProfile W₂ a b ha hs₂ hW₂ t₂;
      (∀ (r:Setoid T) (tc:{q // ¬singletonBlock r q}→S)
        (A:Finset {q // singletonBlock r q}) (ti:A→S),Function.Injective ti →
        ∀ d∈QRH.Record1252270103KernelMass.divisorPool (supportedRectangle S b M₁ M₂),
        (∑ u∈rows,‖
          restoredRow (bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂) S
            (fun q:{q:{q // singletonBlock r q} // q∉A}=>supportedPool (pool (singletonRepresentative r q.val)))
            (crossBeta A S ti (collisionBeta r S tc β)) (fun q=>P (singletonRepresentative r q.val))
            V₁ V₂ b (X₁/d.1.absNorm) (X₂/d.2.absNorm)-
          restoredRow (bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂) S
            (fun q:{q:{q // singletonBlock r q} // q∉A}=>supportedPool (pool (singletonRepresentative r q.val)))
            (crossBeta A S ti (collisionBeta r S tc β)) (fun q=>P (singletonRepresentative r q.val))
            V₁ V₂ b (Y₁/d.1.absNorm) (Y₂/d.2.absNorm)‖^2)≤E) →
      alignedPairEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark≤C*Xcap^ε*E := by
  obtain ⟨C,hC,hrestore⟩:=full_signed_energy (α:=T) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro Xcap hXcap S hS M _ Hr hHr base η₁ η₂ θ rows pool slotWeight P hpool hP hp hWeight
    mark tMark W₁ W₂ a b ha hb hs₁ hs₂ hW₁ hW₂ t₁ t₂ M₁ M₂ X₁ X₂ Y₁ Y₂ E
    hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂ hE henclose hmark
  dsimp only
  intro hroot
  let β:=fun i:T=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr
    (base.product η₁.inverse) (θ i)) I*slotWeight i I) tMark
  let V₁:=normPowerProfile W₁ a b ha hs₁ hW₁ t₁
  let V₂:=normPowerProfile W₂ a b ha hs₂ hW₂ t₂
  have hV₁:Function.support (V₁:ℝ→ℂ)⊆Set.Iic b :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(hs₁ hx).2)
  have hV₂:Function.support (V₂:ℝ→ℂ)⊆Set.Iic b :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(hs₂ hx).2)
  have hβ:∀ i I,I∈supportedPool (pool i) → ‖β i I‖≤B := by
    intro i I hI
    have hIp:I∈pool i := (Finset.mem_filter.mp hI).1
    by_cases hI0:I=0
    · subst I
      simp only [β,heightCoefficient,map_zero,zero_mul,norm_zero]
      exact zero_le_one.trans hB
    · dsimp only [β]
      rw [heightCoefficient_norm _ _ I hI0,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one _ I)).trans (hWeight i I hIp)
  rw [aligned_energy_eq_bare T M Hr hHr base η₁ η₂ θ rows S pool slotWeight P mark tMark
    W₁ W₂ a b ha hb hs₁ hs₂ hW₁ hW₂ t₁ t₂ M₁ M₂ X₁ X₂ Y₁ Y₂
    hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂ henclose hmark]
  have hh:=hrestore Xcap hXcap S hS rows (fun _=>1) (fun u=>bareCharacter u.val)
    (idealCoeff η₁) (idealCoeff η₂) (color_norm_le_one η₁ η₂)
    (fun i=>supportedPool (pool i)) β P hpool hP
    (fun i I hI=>⟨(Finset.mem_filter.mp hI).2,hp i I (Finset.mem_filter.mp hI).1⟩) hβ
    V₁ V₂ b M₁ M₂ X₁ X₂ Y₁ Y₂ 1 1 E hX₁ hX₂ hY₁ hY₂ hE (by intros;exact zero_le_one) (by
      intro r tc A ti hti d hd
      have hleaf:=hroot r tc A ti hti d hd
      apply (le_of_eq ?_).trans hleaf
      apply Finset.sum_congr rfl
      intro u hu
      rw [one_mul,signed_residual_sources (bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂)
        S _ _ _ V₁ V₂ hb hX₁ hX₂ hY₁ hY₂ hx₁ hx₂ hy₁ hy₂ hV₁ hV₂ hd])
  simpa only [one_mul] using hh

#print axioms actual_aligned_restoration
end
end QRH.Cycle092.ColoredRootRestore
