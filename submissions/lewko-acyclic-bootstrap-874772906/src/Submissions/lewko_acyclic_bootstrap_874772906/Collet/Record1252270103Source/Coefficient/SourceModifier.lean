/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The source projector is the literal squarefree ordinary pair and the fixed
ordinary-only small-prime hole. Both remain inside the tuple coefficient under
common allocation; the whole-column multiplier is retained without alteration. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.ModifierEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.Contract

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal
open QRH.Record1252270103Restoration
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentSourceLiveAllocation CenteredMomentSourceLiveColumn
open CenteredMomentLiveSupport CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def ordinaryHoleIndicator (I J : Ideal O) : ℂ := if ordinarySmallHole I J then 1 else 0

def sourceModifier (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι) : ℂ :=
  ordinaryHoleIndicator (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1))*coupledFactor A₁ A₂ D F v

theorem squarefreeIndicator_cast (I : Ideal O) :
    (QRH.Record1252270103KernelMass.squarefreeIndicator I : ℂ)=squarefreeIndicator I := by
  by_cases h : Squarefree I <;>
    simp [QRH.Record1252270103KernelMass.squarefreeIndicator,squarefreeIndicator,h]

theorem sourceModifier_eq_literal (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι) :
    sourceModifier A₁ A₂ D F v =
      if ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1)) then
        (QRH.Record1252270103KernelMass.squarefreeIndicator
          ((A₁*v (Sum.inr 0))*(A₂*v (Sum.inr 1))) : ℂ)*F (D*finiteTupleProduct v)
      else 0 := by
  rw [squarefreeIndicator_cast]
  by_cases h : ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1)) <;>
    simp [sourceModifier,ordinaryHoleIndicator,coupledFactor,h,mul_assoc]

theorem sourceModifier_norm_le (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι)
    (M : ℝ) (hM : 0≤M) (hF : ‖F (D*finiteTupleProduct v)‖≤M) :
    ‖sourceModifier A₁ A₂ D F v‖≤M := by
  by_cases hh : ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1))
  · by_cases hs : Squarefree (A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1))
    · simpa [sourceModifier,ordinaryHoleIndicator,coupledFactor,squarefreeIndicator,hh,hs] using hF
    · simpa [sourceModifier,ordinaryHoleIndicator,coupledFactor,squarefreeIndicator,hh,hs] using hM
  · simpa [sourceModifier,ordinaryHoleIndicator,hh] using hM

theorem sourceModifier_nonzero (A₁ A₂ D : Ideal O) (F : Ideal O→ℂ) (v : Tuple ι)
    (h : sourceModifier A₁ A₂ D F v≠0) :
    ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1)) ∧
    Squarefree (A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)) ∧ F (D*finiteTupleProduct v)≠0 := by
  have hh : ordinarySmallHole (A₁*v (Sum.inr 0)) (A₂*v (Sum.inr 1)) := by
    by_contra hn
    exact h (by simp [sourceModifier,ordinaryHoleIndicator,hn])
  have hs : Squarefree (A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1)) := by
    by_contra hn
    exact h (by simp [sourceModifier,coupledFactor,squarefreeIndicator,hn])
  refine ⟨hh,hs,?_⟩
  simpa [sourceModifier,ordinaryHoleIndicator,coupledFactor,squarefreeIndicator,hh,hs] using h

theorem sourceModifier_common_allocation (A₁ A₂ D C : Ideal O) (F : Ideal O→ℂ)
    (B : Tuple ι) (hB : finiteTupleProduct B=C) (v : Tuple (liveIndices B)) :
    pulledModifier B (sourceModifier A₁ A₂ D F) v=
      sourceModifier (A₁*B (Sum.inr 0)) (A₂*B (Sum.inr 1)) (D*C) F v := by
  unfold pulledModifier sourceModifier
  rw [coupledFactor_extract A₁ A₂ D C F B (restoreTuple B v) hB (restore_frozen B v),
    remaining_restore]
  simp only [restoreTuple,Sum.elim_inr,mul_assoc]

theorem modifiedLiveProfile_sourceModifier (A₁ A₂ D C R : Ideal O) (F : Ideal O→ℂ)
    (B : Tuple ι) (hB : finiteTupleProduct B=C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (v : Tuple (liveIndices B)) :
    modifiedLiveProfile (sourceModifier A₁ A₂ D F) B C R ν Wslot P
      W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v=
      ordinaryHoleIndicator ((A₁*B (Sum.inr 0))*v (Sum.inr 0))
        ((A₂*B (Sum.inr 1))*v (Sum.inr 1))*
        coupledLiveProfile A₁ A₂ D F B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v := by
  unfold modifiedLiveProfile
  rw [sourceModifier_common_allocation A₁ A₂ D C F B hB v]
  unfold sourceModifier coupledLiveProfile
  ring

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.sourceModifier_eq_literal
#print axioms OAI.SevenEighths.Record1252270103Source.sourceModifier_common_allocation
#print axioms OAI.SevenEighths.Record1252270103Source.modifiedLiveProfile_sourceModifier
