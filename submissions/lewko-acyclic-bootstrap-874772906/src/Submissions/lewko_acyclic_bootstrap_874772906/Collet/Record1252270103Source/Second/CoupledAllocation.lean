/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Divisor-masked second allocation with the original retained tuple modifier.
No unmodified column or moment is substituted. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.CoupledRetained
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.ModifierEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Record1252270103Source CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentSourceProfileMass CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationLiveMask
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentHeckeColumnWindow
open CanonicalQuadraticSieve HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def modifiedMaskedLiveProfile (modifier : Tuple ι→ℂ) (B : Tuple ι) (C R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : Tuple (liveIndices B)→ℂ :=
  fun v=>pulledModifier B modifier v*
    maskedLiveProfile B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

theorem modified_live_column_mask (modifier : Tuple ι→ℂ) (B : Tuple ι)
    (S : Finset (Tuple (liveIndices B))) (C R L I : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient S
      (modifiedMaskedLiveProfile modifier B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=
    finiteColumnCoefficient S
      (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*
        (if L∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  unfold modifiedMaskedLiveProfile modifiedLiveProfile maskedLiveProfile liveProfile
  rw [profile_mask,(Finset.mem_filter.mp hv).2]
  ring

theorem modified_live_divisor_energy (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (hB : ∀i,B i≠0)
    (C R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O→ℂ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB)
        (modifiedLiveProfile modifier B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
      (fun I=>(if L∣I then 1 else 0)*f I) W K=
    sourceRestrictedEnergy keep (finiteColumns (liveBox S B hB))
      (finiteColumnCoefficient (liveBox S B hB)
        (modifiedMaskedLiveProfile modifier B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  rw [modified_live_column_mask]
  ring

/-- Complete allocation count, unchanged row selector, and literal divisor
mask. The finite modifier remains inside each completed positive norm. -/
theorem original_modified_divisor_energy (modifier : Tuple ι→ℂ)
    (S : (ι⊕Fin 2)→Finset (Ideal O))
    (hS : ∀i,∀I∈S i,I≠0) (hp : ∀i,∀I∈S (Sum.inl i),Prime I)
    (C R seed L : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O→ℂ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I=>if IsCoprime C I ∧ L∣I then finiteColumnCoefficient (Fintype.piFinset S)
        (fun v=>modifier v*profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v) (C*I) else 0)
      f W K≤((actualAllocations S C).card:ℝ)*∑B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (modifiedMaskedLiveProfile modifier B C R L ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K := by
  have h := original_modified_restricted_energy modifier S hS hp C R seed hC hseed
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (fun I=>(if L∣I then 1 else 0)*f I) keep W K hK hW
  simp_rw [modified_live_divisor_energy] at h
  refine le_trans ?_ h
  apply le_of_eq
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

theorem modified_child_column (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (modifiedMaskedLiveProfile modifier B C R L s.ν s.W s.P s.W₁ s.W₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      coefficient (child s C R B τ t) (pulledModifier B modifier) (R*C) L := by
  have hp : modifiedMaskedLiveProfile modifier B C R L s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1=
      QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient
        (child s C R B τ t) (pulledModifier B modifier) (R*C) L := by
    funext v
    unfold modifiedMaskedLiveProfile QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient
    rw [child_profile s C R L B τ t]
    rfl
  rw [hp,child_tuplePool s C R B τ t]
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
  apply congrArg (fun T=>finiteColumnCoefficient T _)
  ext v
  simp only [Fintype.mem_piFinset]

theorem modified_child_columns (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      finiteColumns (Fintype.piFinset (child s C R B τ t).pools) := by
  rw [child_tuplePool s C R B τ t]
  apply congrArg finiteColumns
  ext v
  simp only [Fintype.mem_piFinset]

def childDivisorEnergy (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset (child s C R B τ t).pools))
    (coefficient (child s C R B τ t) (pulledModifier B modifier) (R*C) L)
    (heightCoeff τ t) W K

def allocatedDivisorEnergy (s : Input ι) (modifier : Tuple ι→ℂ) (C R L : Ideal O)
    (τ : Character) (t : ℝ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*∑B : actualAllocations s.pools C,
    ‖frozenCoefficient B C R s.ν s.W s.P‖^2*
      childDivisorEnergy s modifier C R L B τ t keep W K

theorem allocatedDivisorEnergy_eq_live (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R L : Ideal O) (τ : Character) (t : ℝ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    allocatedDivisorEnergy s modifier C R L τ t keep W K=
      ((actualAllocations s.pools C).card:ℝ)*∑B : actualAllocations s.pools C,
        ‖frozenCoefficient B C R s.ν s.W s.P‖^2*
          sourceRestrictedEnergy keep
            (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
              (modifiedMaskedLiveProfile modifier B C R L s.ν s.W s.P s.W₁ s.W₂
                s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)) (heightCoeff τ t) W K := by
  unfold allocatedDivisorEnergy
  apply congrArg (fun x : ℝ=>((actualAllocations s.pools C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  unfold childDivisorEnergy
  rw [modified_child_column s modifier C R L B τ t,modified_child_columns s C R B τ t]

/-- The ordinary second divisor source is bounded by actual modified child
inputs, including their residual pools and pulled-back modifier. -/
theorem actual_allocated_divisor_energy (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R seed L : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (keep : O→Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools)))
      (fun I=>if IsCoprime C I ∧ L∣I then coefficient s modifier R seed (C*I) else 0)
      (heightCoeff τ t) W K≤allocatedDivisorEnergy s modifier C R L τ t keep W K := by
  rw [allocatedDivisorEnergy_eq_live]
  exact original_modified_divisor_energy modifier s.pools s.pools_ne s.prime C R seed L hC hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 (heightCoeff τ t) keep W K hK hW

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.original_modified_divisor_energy
#print axioms OAI.SevenEighths.Record1252270103Second.modified_child_column
#print axioms OAI.SevenEighths.Record1252270103Second.actual_allocated_divisor_energy
