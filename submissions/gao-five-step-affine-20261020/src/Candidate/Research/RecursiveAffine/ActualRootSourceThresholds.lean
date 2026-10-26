/- Genuine bare-root native fit and finite presentation thresholds. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootSelectedSourceGates
import Candidate.Research.RecursiveAffine.SourceContextThreshold

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153ActualRootSourceGates
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily Cycle63InitialMass Cycle153SourceSchedule Cycle153.RegionalSchedule

/-- The actual fixed root conductor and all constants used by its native
width/prefix constructors fit the chosen μ before any moving state or
selected row. No finite-fit or source-width premise is requested. -/
theorem eventually_actual_root_native_thresholds (etaSeed : Character)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      Real.logb Z (etaSeed.modulus.absNorm:ℝ) ≤ nativeMu/16 ∧
      Real.logb Z 4+2*(budget:ℝ)*Real.logb Z (9/4)+(nativeMu/64)/2 ≤ 1 ∧
      Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
        2*(budget:ℝ)*Real.logb Z (9/4)+Real.logb Z 1+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ (nativeMu/8)/2 ∧
      0 ≤ nativeDriverRate budget ∧ nativeDriverRate budget ≤ 1 ∧
      nativeMu/64 ≤ 1/1000000000000000 :=by
  let rate:=nativeMu/(64*(2*(budget:ℝ)+4))
  have hn : (0:ℝ) ≤ budget:=Nat.cast_nonneg budget
  have hr : 0<rate:=by dsimp only [rate];exact div_pos nativeMu_pos (by positivity)
  have heq : rate*(64*(2*(budget:ℝ)+4))=nativeMu:=by
    dsimp only [rate]
    exact div_mul_cancel₀ _ (by positivity)
  have hfixed:=eventually_rebased_native_fixed_log CenteredMomentFirstPhysicalSource.fixedPresentationCost
    rate CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos.le hr
  have hfactor:=eventually_rebased_native_fixed_log (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))
    rate (by positivity) hr
  filter_upwards [hfixed,hfactor,eventually_rebased_native_fixed_log (9/4) rate (by norm_num) hr,
    eventually_rebased_native_fixed_log 4 rate (by norm_num) hr,
    eventually_root_fixed_source_fit etaSeed 1] with Z h1 h2 h3 h4 hfit
  have hcost1:=h1.2 1 (by norm_num)
  have hcost2:=h2.2 1 (by norm_num)
  have hcost3:=h3.2 1 (by norm_num)
  have hcost4:=h4.2 1 (by norm_num)
  rw [Real.rpow_one] at hcost1 hcost2 hcost3 hcost4
  have hb:=mul_le_mul_of_nonneg_left hcost3 (show (0:ℝ) ≤ 2*(budget:ℝ) by positivity)
  have hcap : (2*(budget:ℝ)+2)*rate ≤ nativeMu/16 :=by nlinarith only [heq,hr]
  have hcapSmall : (2*(budget:ℝ)+1)*rate ≤ nativeMu :=by nlinarith only [heq,hr]
  have hmu : nativeMu+nativeMu/128 ≤ 1 :=by norm_num [nativeMu,primitiveError]
  have hdriver:=nativeDriverRate_budgets budget
  refine ⟨h1.1,?_,?_,?_,hdriver.1.le,?_,?_⟩
  · linarith only [hfit.2.1]
  · linarith only [hcost4,hb,hcapSmall,hmu]
  · rw [Real.logb_one]
    linarith only [hcost1,hcost2,hb,hcap]
  · exact hdriver.2.1.trans (by norm_num [nativeMu,primitiveError])
  · norm_num [nativeMu,primitiveError]
end
end OAI.SevenEighths.Cycle153ActualRootSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualRootSourceGates.eventually_actual_root_native_thresholds
