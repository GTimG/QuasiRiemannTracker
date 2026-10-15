import Candidate.Cycle62.Physical.InitialMass.MarkedParameters
import Candidate.Cycle62.Physical.InitialMass.GeometryAffineFinalSchedule
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical ContDiff
open Cycle62Moment Cycle62InitialMass
theorem geometry_loss_below_marked_cap (εaffine : ℝ) :
    geometryLossUnit 1 εaffine≤(1/100000000:ℝ) := by
  have h := (min_le_right (εaffine/128) _).trans
    (min_le_left (((7/30000000:ℝ)*1)/128) (min ((1:ℝ)/128) (1/128)))
  change geometryLossUnit 1 εaffine≤_ at h
  exact h.trans (by norm_num)


theorem existing_schedule_marked_gates
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ→ℝ)
    (hμ : 0<μ) (hμcap : μ≤1/100000000) (hB : 0≤B) (hL : 0≤L)
    (hbΦ : 0≤bΦ) (hτ : 0<τ) (hbound : ∀k,0≤bound k) :
    let P := geometryAffineFinalHighSchedule W hWs hW μ B L bΦ τ N bound
      hμ hB hL hbΦ hτ hbound
    P.e≤μ/294912 ∧
      12*P.e*((22:ℝ)+2)+8*markedWitnessRate+2*markedWitnessRate≤ markedRate/2 ∧
      2*P.εslot*P.d≤ markedBinWidth*markedTinyWidth N ∧
      (2*P.εslot*P.d)*(N:ℝ)≤μ/32 := by
  intro P
  have he : P.e≤μ/294912 := by
    change highBuffer 1 1 _ (geometryFinalPlainRate μ 31)≤μ/294912
    have hh := (min_le_right (1/2000:ℝ) _).trans
      (min_le_right (geometryFinalDictionaryRate μ 31 3 4 3 B L N/(32*(1+1)))
        (geometryFinalPlainRate μ 31/(48*(1+2))))
    change highBuffer 1 1 _ _≤_ at hh
    convert hh using 1 <;> norm_num [geometryFinalPlainRate] <;> ring
  have hs := marked_slot_loss_gate μ (geometryFinalDictionaryRate μ 31 3 4 3 B L N) N hμcap
    (min_le_right _ _)
  have hr := geometry_final_dictionary_budgets μ 31 3 4 3 B L N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  rcases hr with ⟨hδ,hδc,hδcap,hplain,hlow,hhigh,hslot,hplainbudget,hjoined⟩
  refine ⟨he,marked_buffer_budget μ P.e hμcap he,hs,?_⟩
  change (2*geometryFinalDictionaryRate μ 31 3 4 3 B L N*31)*(N:ℝ)≤μ/32
  simpa only [mul_assoc] using hslot

end
end OAI.SevenEighths.Cycle62MarkedPlain
