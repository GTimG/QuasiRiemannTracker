import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.MarkedParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical ContDiff
open Cycle63Moment Cycle63InitialMass
theorem geometry_loss_below_marked_cap (εaffine : ℝ) :
    geometryLossUnit 1 εaffine≤Cycle63.Optimization.geometryLossCap := by
  have h := (min_le_right (εaffine/128) _).trans
    (min_le_left (((Cycle63.Arithmetic.lowReserve:ℝ)*1)/128) (min ((1:ℝ)/128) (1/128)))
  change geometryLossUnit 1 εaffine≤_ at h
  refine h.trans ?_
  have hr := Cycle63.Arithmetic.lowRegionRatio_bounds.1
  have hd : (1/2:ℝ)/Cycle63.Optimization.slotPrice ≤ 7/10 := by
    rw [div_le_iff₀ Cycle63.Optimization.slotPrice_pos]
    linarith [Cycle63.Optimization.slotPrice_mem.1]
  unfold Cycle63.Arithmetic.lowReserve Cycle63.Optimization.lowReserveAt Cycle63.Optimization.geometryLossCap
    Cycle63.Optimization.lowReserveWeight Cycle63.Optimization.allowanceUnit
  simp only [mul_one]
  linarith

theorem existing_schedule_marked_gates
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (μ B L bΦ τ : ℝ) (N : ℕ) (bound : ℕ→ℝ)
    (hμ : 0<μ) (hμcap : μ≤Cycle63.Optimization.geometryLossCap) (hB : 0≤B) (hL : 0≤L)
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
    convert hh using 1; norm_num [geometryFinalPlainRate]; ring
  have hs := marked_slot_loss_gate μ (geometryFinalDictionaryRate μ 31 3 4 3 B L N) N hμcap
    (min_le_right _ _)
  have hr := geometry_final_dictionary_budgets μ 31 3 4 3 B L N hμ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hB hL
  rcases hr with ⟨hδ,hδc,hδcap,hplain,hlow,hhigh,hslot,hplainbudget,hjoined⟩
  refine ⟨he,marked_buffer_budget μ P.e hμcap he,hs,?_⟩
  change (2*geometryFinalDictionaryRate μ 31 3 4 3 B L N*31)*(N:ℝ)≤μ/32
  simpa only [mul_assoc] using hslot

end
end OAI.SevenEighths.Cycle63MarkedPlain

end Record1252270103Bootstrap.PR67
