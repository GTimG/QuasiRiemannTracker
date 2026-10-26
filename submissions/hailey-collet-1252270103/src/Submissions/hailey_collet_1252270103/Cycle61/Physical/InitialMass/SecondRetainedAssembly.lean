import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondActualSources
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance secondRetainedAssemblyDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev ActualSecondBlockIndex {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ) :=
  (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)) ×
    (U : Finset (CommonIndex p.val.val.1 p.val.val.2)) ×
      SourceBlocks p.val.val.1 p.val.val.2 U K (frequencyRadius Tsec Z ξ) (sourceRadius s)

variable {α : Type*} [Fintype α] [DecidableEq α]

def actualSecondBlockDatum (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    SecondInputDatum α :=
  actualSecondInputDatum slots s R seed hseed hz₁ hz₂ q.1.val q.2.1
    (frequencyRadius Tsec Z ξ)
    (sourceRows q.1.val.val.1 q.1.val.val.2 q.2.1 (frequencyRadius Tsec Z ξ))
    (sourceRows_nonzero _ _ _ _) K hK (fun i=>(q.2.2 i:ℤ))

def actualSecondBlockWeight {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : ℂ :=
  heightCoeff s.η s.t q.1.val.val.1*star (heightCoeff s.η s.t q.1.val.val.2)

/-- Exact retained-energy expansion into the original-input blocks. The
source cap follows from the actual coefficients, and active-pool removal
preserves the polynomial used by the allocation extraction. -/
theorem actual_original_retained_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ=
      ∑q : ActualSecondBlockIndex s R seed K Tsec Z ξ,
        actualSecondBlockWeight s R seed K Tsec Z ξ q*
          (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W := by
  rw [original_live_blocks s.η s.t _ _ W K Tsec Z ξ (sourceRadius s) hK
    (fun I _ hI=>(original_column_norm s R seed I hz₁ hz₂ hI).2)]
  rw [Fintype.sum_sigma]
  conv_lhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [actualSecondBlockWeight,actualSecondBlockDatum,actualSecondInputDatum,
    SecondInputDatum.block,originalSecondBlock,SecondBlockSource.value]
  apply congrArg (fun x : ℂ=>heightCoeff s.η s.t p.val.val.1*
    star (heightCoeff s.η s.t p.val.val.2)*x)
  exact (physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _).symm

/-- Heterogeneous original sources retain a single joint block sum. The
outer weights may include the first allocation and amplification scalars. -/
theorem actual_joint_retained_assembly {Label : Type*} [Fintype Label]
    (slots : Label→Finset α) (s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O) (hseed : ∀l,Squarefree (seed l))
    (hz₁ : ∀l,(s l).W₁ 0=0) (hz₂ : ∀l,(s l).W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec : Label→ℝ) (Z ξ : ℝ) (hK : ∀l,0<K l)
    (weight : Label→ℂ) :
    (∑l,weight l*secondRetainedEnergy (s l).η (s l).t
      (finiteColumns (Fintype.piFinset (s l).pools)) (coefficient (s l) (R l) (seed l))
        W (K l) (Tsec l) Z ξ)=
      ∑q : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ,
        (weight q.1*actualSecondBlockWeight (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)*
          (actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
            (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2).block.value W := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  rw [actual_original_retained_assembly (slots l) (s l) (R l) (seed l)
    (hseed l) (hz₁ l) (hz₂ l) W (K l) (Tsec l) Z ξ (hK l),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (mul_assoc _ _ _).symm

/-- Seed and source-size gates for every block in the actual expansion. -/
theorem actual_retained_block_gates (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    d.seed∣d.C ∧ d.seed∣d.D ∧
      (d.C.absNorm:ℝ)≤sourceRadius s ∧ (d.D.absNorm:ℝ)≤sourceRadius s := by
  have h := actual_common_gates s R seed hseed hz₁ hz₂ _ _ q.1.val.property
  exact ⟨h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_retained_assembly

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_retained_assembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_retained_block_gates
