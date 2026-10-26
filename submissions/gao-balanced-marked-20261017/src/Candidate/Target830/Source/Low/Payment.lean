import Candidate.Target830.Source.Low.Main
import Candidate.Target830.Source.Schedule
import Candidate.Cycle63.Moment.LowBranch.Payment

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.LowBranch
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch
variable (P : SourcePlane)

/-- Joint width and capacity deletion retain the exact new source reserve. -/
theorem low_paid_excess_bound {b M nominal width delta total padding : ℝ}
    (hb : widthLower≤b ∧ b≤widthUpper) (hM : 0≤M)
    (hwidth : width-nominal≤delta) (hdelta : 0≤delta) (hpad : 0≤padding)
    (htotal : total-nominal≤M*P.gap b+6*(M*P.amp b)+padding) :
    width+(P.q/(6*incumbentKappa))*max (total-width) 0≤
      nominal+delta+M*P.amp b-M*lowReserve+(P.q/(6*incumbentKappa))*padding := by
  have hprice : 0≤P.q/(6*incumbentKappa) := by cases P <;> norm_num [SourcePlane.q,incumbentKappa,kappa0]
  have hpriceHi : P.q/(6*incumbentKappa)≤1 := by cases P <;> norm_num [SourcePlane.q,incumbentKappa,kappa0]
  have heq := low_payment_identity P b
  change P.amp b-P.q/(6*incumbentKappa)*(P.gap b+6*P.amp b)=lowReserve at heq
  have hmul := congrArg (fun x : ℝ=>M*x) heq
  have hguard := source_guards P hb
  have ha0 : 0≤P.amp b := by
    have hamin := hguard.2.1
    have hamp := hguard.2.2.1
    linarith
  have ha : lowReserve≤P.amp b := by
    have hp := mul_nonneg hprice (show 0≤P.gap b+6*P.amp b by linarith [hguard.1])
    linarith
  by_cases hm : total≤width
  · rw [max_eq_right (by linarith : total-width≤0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0≤total-width)]
    nlinarith [mul_le_mul_of_nonneg_left htotal hprice,
      mul_nonneg (sub_nonneg.mpr hpriceHi) (sub_nonneg.mpr hwidth)]

theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : widthLower≤b ∧ b≤widthUpper) (hM : 0≤M)
    (hwidth : width-nominal≤δ) (hdelta : 0≤δ) (hpad : 0≤padding)
    (htotal : total-nominal≤M*P.gap b+6*(M*P.amp b)+padding) :
    width+εold+buffer+(P.q/(6*incumbentKappa))*max (total-width) 0+P.q*mesh≤
      nominal+δ+M*P.amp b-M*lowReserve+εold+buffer+
        (P.q/(6*incumbentKappa))*padding+P.q*mesh := by
  linarith [low_paid_excess_bound P hb hM hwidth hdelta hpad htotal]

end
end OAI.SevenEighths.Target830.Source.LowBranch
#print axioms OAI.SevenEighths.Target830.Source.LowBranch.low_paid_excess_bound
#print axioms OAI.SevenEighths.Target830.Source.LowBranch.paid_low_exponent_shifted
