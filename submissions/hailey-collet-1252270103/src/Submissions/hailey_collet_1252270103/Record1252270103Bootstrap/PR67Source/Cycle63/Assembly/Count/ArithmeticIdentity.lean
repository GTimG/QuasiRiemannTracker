import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.WitnessGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Count.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
namespace Cycle63.Assembly.Count
noncomputable section
open Arithmetic.Bernstein
open OAI.SevenEighths.Cycle25DetectorRowCount

theorem rowCount_eq {κ delta p : ℝ} (hk : 7/10≤κ) :
    rowCount delta p κ = countingROld κ delta p := by
  simp only [rowCount, countingROld, V, rowDen, Physical.coefficient_eq_old hk]
end
end Cycle63.Assembly.Count

end Record1252270103Bootstrap.PR67
