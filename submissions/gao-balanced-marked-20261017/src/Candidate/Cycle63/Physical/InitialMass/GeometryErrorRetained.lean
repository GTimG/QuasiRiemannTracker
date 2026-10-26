import Candidate.Cycle63.Physical.InitialMass.SecondRetainedAssembly

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondLocalization
local notation "O" => HeckeFamily.O
local instance errorRetainedDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Canceled physical blocks are removed before absolute values or column
estimates. Every surviving block supplies the nonvanishing field required
by the extracted-prime geometry theorem. -/
theorem actual_nonzero_retained_assembly (slots : Finset α)(s : Input slots)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ))(K Tsec Z ξ : ℝ)(hK : 0<K) :
    let datum := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
    let blocks := Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      (datum q).block.value W≠0)
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ=
      ∑q : blocks,actualSecondBlockWeight s R seed K Tsec Z ξ q.val*(datum q.val).block.value W := by
  intro datum blocks
  rw [actual_original_retained_assembly slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK]
  symm
  rw [Finset.sum_coe_sort blocks (fun q=>actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W)]
  dsimp only [blocks]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  change (if (datum q).block.value W≠0 then actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W else 0)=actualSecondBlockWeight s R seed K Tsec Z ξ q*(datum q).block.value W
  by_cases hz : (datum q).block.value W=0
  · simp only [hz,ne_eq,not_true_eq_false,ite_false,mul_zero]
  · simp only [hz,ne_eq,not_false_eq_true,ite_true]

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_nonzero_retained_assembly
