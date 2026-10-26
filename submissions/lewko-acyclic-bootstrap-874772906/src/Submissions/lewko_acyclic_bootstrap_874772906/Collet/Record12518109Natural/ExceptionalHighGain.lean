/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite-core and tiny-radius counts in the same physical HIGH coordinates. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighBins

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Natural
open LocalMoment
noncomputable section

def exceptionalHighGain (fixed : Bool) (ν S tinyCut q : ℝ) : ℝ :=
  if fixed then (unmarkedDensity ν-1/6)*q+(ν-1)*S
  else unmarkedDensity ν*q-tinyCut+(ν-1)*S

lemma exceptional_high_count_exponent (fixed : Bool)(ν S tinyCut q : ℝ) :
    unmarkedDensity ν*q+ν*S-exceptionalHighGain fixed ν S tinyCut q=
      (if fixed then q/6 else tinyCut)+S := by
  cases fixed <;> simp only [exceptionalHighGain,Bool.false_eq_true,ite_false,ite_true] <;> ring

lemma exceptional_high_gain_monotone (fixed : Bool)(ν S tinyCut : ℝ)(hν : ν≤3/4) :
    Monotone (exceptionalHighGain fixed ν S tinyCut) := by
  have hr:=unmarkedDensity_ge_two_sevenths hν
  intro q r hqr
  cases fixed <;> simp only [exceptionalHighGain, Bool.false_eq_true,ite_false,ite_true]
  · nlinarith
  · nlinarith

end
end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.exceptional_high_gain_monotone
