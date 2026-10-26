/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected allocation ideals and the literal LOW positive value. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSelectedNewton
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPositiveCornerSplit
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowDictionary
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentCanonicalFirst Cycle61Moment
open CenteredMomentSecondHeightFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open OAI.SevenEighths.Record1252270103Source Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open CenteredMomentFiniteProfileExceptional
open SelectedHighCofactorFamily High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance selectedDictionaryDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α:Type}[Fintype α]{s:Input α}{reflected second:Bool}
    {l:FirstSourceLabel}{C₂ D₂ R:Ideal O}

theorem actual_frozen_ideal_gates (sel:Selection s reflected second l C₂ D₂ R)(hR:R≠0):
    Selection.frozenLeft sel≠0 ∧ Selection.frozenRight sel≠0 ∧ Selection.puncture sel≠0 ∧
      Selection.frozenLeft sel*Selection.frozenRight sel∣Selection.puncture sel := by
  have h₁:=alloc_ne s _ sel.B₁
  have h₂:=alloc_ne sel.firstInput _ sel.B₂
  have hf:=alloc_ne _ _ sel.Bf
  have hp₁:sel.B₁.val (Sum.inr 0)*sel.B₁.val (Sum.inr 1)∣(if reflected then l.1.2 else l.1.1):=by
    simpa only [allocation_product s _ sel.B₁] using plain_product_dvd_tuple sel.B₁.val
  have hp₂:sel.B₂.val (Sum.inr 0)*sel.B₂.val (Sum.inr 1)∣(if second then D₂ else C₂):=by
    simpa only [allocation_product sel.firstInput _ sel.B₂] using plain_product_dvd_tuple sel.B₂.val
  have hpf:sel.Bf.val (Sum.inr 0)*sel.Bf.val (Sum.inr 1)∣sel.Cf:=by
    simpa only [allocation_product _ _ sel.Bf] using plain_product_dvd_tuple sel.Bf.val
  have hd:=mul_dvd_mul (mul_dvd_mul hp₁ hp₂) hpf
  have hdR:((if reflected then l.1.2 else l.1.1)*(if second then D₂ else C₂))*sel.Cf∣
      Selection.puncture sel:=by
    refine ⟨R,?_⟩
    dsimp only [Selection.puncture]
    ring
  refine ⟨mul_ne_zero (mul_ne_zero (h₁ _) (h₂ _)) (hf _),
    mul_ne_zero (mul_ne_zero (h₁ _) (h₂ _)) (hf _),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hR (allocation_ne s _ sel.B₁))
      (allocation_ne sel.firstInput _ sel.B₂)) (allocation_ne _ _ sel.Bf),?_⟩
  have he:Selection.frozenLeft sel*Selection.frozenRight sel=
      ((sel.B₁.val (Sum.inr 0)*sel.B₁.val (Sum.inr 1))*
        (sel.B₂.val (Sum.inr 0)*sel.B₂.val (Sum.inr 1)))*
        (sel.Bf.val (Sum.inr 0)*sel.Bf.val (Sum.inr 1)):=by
    dsimp only [Selection.frozenLeft,Selection.frozenRight]
    ring
  rw [he]
  exact hd.trans hdR

theorem actual_selected_profiles (sel:Selection s reflected second l C₂ D₂ R):
    sel.finalInput.W₁=s.W₁ ∧ sel.finalInput.W₂=s.W₂ := by
  rcases sel with ⟨B₁,τ₁,t₁,hf₁,B₂,τ₂,t₂,hf₂,Cf,Bf,τf,tf,hff⟩
  exact ⟨rfl,rfl⟩

theorem actual_positive_low_value
    (sel:Selection s reflected second l C₂ D₂ R)(T:Finset α)(corner:Bool)
    (S A:Finset (Ideal O))(τ:Character)(t:ℝ)(z:O)(p:Profiles (1/4:ℝ) (9/4:ℝ))
    (S₀:α→Finset (Ideal O))(β₀:α→Ideal O→ℂ)(P₀:α→ℝ)
    (hW₁:s.W₁=(p.profile 0:ℝ→ℂ))(hW₂:s.W₂=(p.profile 1:ℝ→ℂ))
    (hslots:∀i∈T,s.slots i=S₀ i)(hβ:∀i∈T,restoredSlotCoeff s i=β₀ i)(hP:∀i∈T,s.P i=P₀ i):
    positiveNewtonCofactorPlain corner sel.finalInput (Selection.frozenLeft sel)
      (Selection.frozenRight sel) (Selection.puncture sel) (9/4:ℝ) S A τ t z*
      (∏i:T,normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))=
    let d:=newtonDivisorPair S A
    let X₁:=(if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)/d.1.absNorm
    let X₂:=(if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)/d.2.absNorm
    RetainedLow.positiveFrozenRow (rowWeight τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z t)
      (p.profile 0) (p.profile 1) (Selection.frozenLeft sel*d.1) (Selection.frozenRight sel*d.2)
      (9/4:ℝ) X₁ X₂ (X₁*X₂)*
      (∏i:T,normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
        (S₀ i) (β₀ i) t (P₀ i)) := by
  let d:=newtonDivisorPair S A
  let X₁:=(if corner then sel.finalInput.Y₁ else sel.finalInput.X₁)/d.1.absNorm
  let X₂:=(if corner then sel.finalInput.Y₂ else sel.finalInput.X₂)/d.2.absNorm
  let plain: (ℝ→ℂ)→(ℝ→ℂ)→ℂ:=fun V₁ V₂=>RetainedLow.positiveFrozenRow
    (rowWeight τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z t)
    V₁ V₂ (Selection.frozenLeft sel*d.1) (Selection.frozenRight sel*d.2)
    (9/4:ℝ) X₁ X₂ (X₁*X₂)
  have hp:positiveNewtonCofactorPlain corner sel.finalInput (Selection.frozenLeft sel)
      (Selection.frozenRight sel) (Selection.puncture sel) (9/4:ℝ) S A τ t z=
      plain sel.finalInput.W₁ sel.finalInput.W₂:=
    positive_newton_corner_normalization corner sel.finalInput _ _ _ _ S A τ t z
  have hprofiles:plain sel.finalInput.W₁ sel.finalInput.W₂=plain (p.profile 0) (p.profile 1):=
    congrArg₂ plain ((actual_selected_profiles sel).1.trans hW₁) ((actual_selected_profiles sel).2.trans hW₂)
  have hprod:(∏i:T,normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
      (s.slots i) (restoredSlotCoeff s i) t (s.P i))=
      (∏i:T,normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
        (S₀ i) (β₀ i) t (P₀ i)):=by
    apply Finset.prod_congr rfl
    intro i _
    have h₁:=congrArg (fun v=>normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
      v (restoredSlotCoeff s i) t (s.P i)) (hslots i i.property)
    have h₂:=congrArg (fun v=>normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
      (S₀ i) v t (s.P i)) (hβ i i.property)
    have h₃:=congrArg (fun v=>normalizedSlot τ (fixedBadMask*idealGenerator (Selection.puncture sel)) 1 z
      (S₀ i) (β₀ i) t v) (hP i i.property)
    exact h₁.trans (h₂.trans h₃)
  exact congrArg₂ (fun a b:ℂ=>a*b) (hp.trans hprofiles) hprod

end
end QRH.Record1252270103Source.Admission.SelectedLowDictionary
#print axioms QRH.Record1252270103Source.Admission.SelectedLowDictionary.actual_frozen_ideal_gates
#print axioms QRH.Record1252270103Source.Admission.SelectedLowDictionary.actual_positive_low_value
