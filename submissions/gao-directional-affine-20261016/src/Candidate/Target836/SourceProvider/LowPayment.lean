import Candidate.Target836.SourceProvider.LowMain
import Candidate.Cycle63.Moment.LowBranch.Payment

set_option autoImplicit false
namespace Target874836.SourceProvider.LowBranch
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Cycle63Moment.LowBranch

/-- Joint width and capacity deletion retain the exact new source reserve. -/
theorem low_paid_excess_bound {b M nominal width delta total padding : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hM : 0≤M)
    (hwidth : width-nominal≤delta) (hdelta : 0≤delta) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Named.gap b+6*(M*Named.amp b)+padding) :
    width+(Named.q/(6*incumbentKappa))*max (total-width) 0≤
      nominal+delta+M*Named.amp b-M*Named.lowReserve+(Named.q/(6*incumbentKappa))*padding := by
  have hprice : 0≤Named.q/(6*incumbentKappa) := by norm_num [Named.q,incumbentKappa]
  have hpriceHi : Named.q/(6*incumbentKappa)≤1 := by norm_num [Named.q,incumbentKappa]
  have heq := Named.low_exact b
  change Named.amp b-Named.q/(6*incumbentKappa)*(Named.gap b+6*Named.amp b)=Named.lowReserve at heq
  have hmul := congrArg (fun x : ℝ=>M*x) heq
  have ha : Named.lowReserve≤Named.amp b := by
    have hg : 0≤Named.gap b := by
      norm_num [Named.gap,Named.B,Named.lam,Named.kappa,incumbentKappa] at *
      linarith [hb.1]
    nlinarith [(Named.basic_bounds b hb).1]
  by_cases hm : total≤width
  · rw [max_eq_right (by linarith : total-width≤0)]
    nlinarith
  · rw [max_eq_left (by linarith : 0≤total-width)]
    nlinarith [mul_le_mul_of_nonneg_left htotal hprice,
      mul_nonneg (sub_nonneg.mpr hpriceHi) (sub_nonneg.mpr hwidth)]

theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hM : 0≤M)
    (hwidth : width-nominal≤δ) (hdelta : 0≤δ) (hpad : 0≤padding)
    (htotal : total-nominal≤M*Named.gap b+6*(M*Named.amp b)+padding) :
    width+εold+buffer+(Named.q/(6*incumbentKappa))*max (total-width) 0+Named.q*mesh≤
      nominal+δ+M*Named.amp b-M*Named.lowReserve+εold+buffer+
        (Named.q/(6*incumbentKappa))*padding+Named.q*mesh := by
  linarith [low_paid_excess_bound hb hM hwidth hdelta hpad htotal]

end
end Target874836.SourceProvider.LowBranch
#print axioms Target874836.SourceProvider.LowBranch.low_paid_excess_bound
#print axioms Target874836.SourceProvider.LowBranch.paid_low_exponent_shifted
