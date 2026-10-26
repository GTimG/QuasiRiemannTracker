import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Bernstein.Feedback
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Count.Crossing
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Physical

open Arithmetic Arithmetic.Bernstein

noncomputable section

-- These predecessor results are variable-κ arithmetic, with no moment premise.

theorem coefficient_eq_old {κ p : ℝ} (hk : 7 / 10 ≤ κ) :
    countingCoefficient κ p = OAI.SevenEighths.Cycle25DetectorRowCount.coefficient p κ := by
  simpa only [OAI.SevenEighths.Cycle25DetectorRowCount.coefficient,
    OAI.SevenEighths.Cycle25DetectorRowCount.primeWeight,
    OAI.SevenEighths.Cycle25DetectorRowCount.denominator,
    OAI.SevenEighths.Cycle25DetectorRowCount.b, mul_div_assoc] using
      canonical_counting_formula hk

end

end Cycle63.Physical

end Record1252270103Bootstrap.PR67
