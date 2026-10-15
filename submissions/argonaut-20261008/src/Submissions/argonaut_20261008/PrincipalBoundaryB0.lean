import Submissions.argonaut_20261008.ParametersHighDataPerturbed

/- Additive source-engineering candidate.  Kernel/elaboration status: NOT_RUN. -/
namespace OAI.SevenEighths
noncomputable section

/-- The analytic x-boundary used by the principal chain. -/
abbrev analyticBoundaryB0 : ℝ := 3499999 / 4000000

lemma analyticBoundaryB0_eq_constructor :
    analyticBoundaryB0 = Parameters.perturbedBoundary := by
  norm_num [analyticBoundaryB0, Parameters.perturbedBoundary, Parameters.perturbedRho]

lemma analyticBoundaryB0_eq_sevenEighths_sub :
    analyticBoundaryB0 = (7 / 8 : ℝ) - 1 / 4000000 := by
  norm_num [analyticBoundaryB0]

lemma seventyNineHundredths_le_analyticBoundaryB0 :
    (79 / 100 : ℝ) ≤ analyticBoundaryB0 := by
  norm_num [analyticBoundaryB0]

lemma eightySevenHundredths_lt_analyticBoundaryB0 :
    (87 / 100 : ℝ) < analyticBoundaryB0 := by
  norm_num [analyticBoundaryB0]

lemma fiveSixths_lt_analyticBoundaryB0 :
    (5 / 6 : ℝ) < analyticBoundaryB0 := by
  norm_num [analyticBoundaryB0]

lemma analyticBoundaryB0_lt_sevenEighths :
    analyticBoundaryB0 < (7 / 8 : ℝ) := by
  norm_num [analyticBoundaryB0]

lemma analyticBoundaryB0_le_one :
    analyticBoundaryB0 ≤ 1 := by
  norm_num [analyticBoundaryB0]

lemma analyticBoundaryB0_lt_one :
    analyticBoundaryB0 < 1 := by
  norm_num [analyticBoundaryB0]

lemma analyticBoundaryB0_le_fortySevenFiftieths :
    analyticBoundaryB0 ≤ (47 / 50 : ℝ) := by
  norm_num [analyticBoundaryB0]

lemma analyticBoundaryB0_pos :
    0 < analyticBoundaryB0 := by
  norm_num [analyticBoundaryB0]

/-- Every point of a closed strip whose left edge is strictly to the right of
`analyticBoundaryB0` lies in the required open half-plane. -/
lemma analyticBoundaryB0_lt_of_strip
    {a x : ℝ} (ha : analyticBoundaryB0 < a) (hx : a ≤ x) :
    analyticBoundaryB0 < x :=
  ha.trans_le hx

/-- The w-contour endpoint lies strictly inside the wider finite Euler
holomorphy half-plane. -/
lemma nineTenths_lt_nineteenTwentieths :
    (9 / 10 : ℝ) < 19 / 20 := by
  norm_num

/-- The z-contour endpoint lies strictly inside the wider finite Euler
holomorphy half-plane. -/
lemma fourTwentyFifths_lt_thirtyThreeTwoHundredths :
    (4 / 25 : ℝ) < 33 / 200 := by
  norm_num

end
end OAI.SevenEighths
