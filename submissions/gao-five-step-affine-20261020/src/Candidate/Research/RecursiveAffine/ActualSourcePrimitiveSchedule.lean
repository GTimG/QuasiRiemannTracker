/- The actual chosen native source schedule pays the primitive fine gates.
Copyright (c) 2026 Zhongpai Gao. Native bounds by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.SourceContextThreshold
import Candidate.Research.RecursiveAffine.SourceContextFee
import Candidate.Research.RecursiveAffine.FiniteSourceUniformization
import Candidate.Research.RecursiveAffine.NativeSelectedPaidSource

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentSectorLocalization
open Cycle63InitialMass Cycle153SourceSchedule Cycle153SourceUniform Cycle153.RegionalSchedule

def actualSideError (Z : ℝ)(budget : ℕ) : ℝ :=3*nativeDriverRate budget+6*Real.logb Z 2

/-- The same mu, first-mass dictionary rate, frequency loss and six-bit
bin slack are small at every actual moving base. The threshold precedes
the source unit, source configuration, first bin and selected source row. -/
theorem eventually_actual_source_small (budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀U : ℝ,(1/50:ℝ) ≤ U→
      0 ≤ frequencyLoss (Z^U) 32 (nativeMu/64)+nativeMu/8 ∧
      frequencyLoss (Z^U) 32 (nativeMu/64)+nativeMu/8 ≤ 1/(10:ℝ)^15 ∧
      0 ≤ nativeDriverRate budget ∧ nativeDriverRate budget ≤ 1/(10:ℝ)^15 ∧
      actualSideError (Z^U) budget ≤ 1/(10:ℝ)^15 := by
  obtain ⟨Z0,hZ0,hfreq⟩:=CenteredMomentFirstPhysicalLedger.frequency_loss_eventually 32 (nativeMu/64)
    (by norm_num) (div_pos nativeMu_pos (by norm_num))
  have hlocal : ∀ᶠY : ℝ in atTop,1<Y ∧ frequencyLoss Y 32 (nativeMu/64)<nativeMu/64 := by
    filter_upwards [eventually_ge_atTop Z0] with Y hY
    exact hfreq Y hY
  have hglobal:=eventually_all_rebased_sources _ hlocal
  filter_upwards [hglobal,eventually_rebased_fixed_log 2 (1/(10:ℝ)^17) (by norm_num)] with Z hf hl
  refine ⟨hf.1,?_⟩
  intro U hU
  have hfl:=hf.2 U hU
  have hlog:=hl.2 U hU
  rw [show max (1:ℝ) 2=2 by norm_num] at hlog
  have h0:=frequencyLoss_nonneg (Z^U) 32 (nativeMu/64) hfl.1 (by norm_num)
    (div_pos nativeMu_pos (by norm_num)).le
  have hd:=nativeDriverRate_budgets budget
  have hmu:=nativeMu_pos
  refine ⟨by linarith only [h0,hmu],?_,hd.1.le,?_,?_⟩
  · have hp : nativeMu/64+nativeMu/8 ≤ 1/(10:ℝ)^15 :=by norm_num [nativeMu,primitiveError]
    linarith only [hfl.2,hp]
  · have hp : nativeMu/128 ≤ 1/(10:ℝ)^15 :=by norm_num [nativeMu,primitiveError]
    exact hd.2.1.trans hp
  · have hp : 3*(nativeMu/128)+6*(1/(10:ℝ)^17) ≤ 1/(10:ℝ)^15 :=by norm_num [nativeMu,primitiveError]
    dsimp only [actualSideError]
    linarith only [hd.2.1,hlog,hp]

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.eventually_actual_source_small
