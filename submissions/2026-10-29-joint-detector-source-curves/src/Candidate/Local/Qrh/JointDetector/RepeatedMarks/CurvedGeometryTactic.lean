/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedGeometry

/-- Expand the common exact geometry proof once, keeping finite stage
source files compact. The resulting proof still checks every quadratic. -/
macro "curved_geometry" : tactic => `(tactic| (
  constructor
  · constructor <;> norm_num
  all_goals first
    | solve | norm_num [Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.matchedCut,
        Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.cutNumerator,
        Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.cutIntercept,
        Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.crossing,
        QRH.SilDensitySplit.Hybrid.cross]
    | (intro i
       fin_cases i <;> solve
         | (left; norm_num [Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.QuadraticSigns,
             Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.geometryCoeff,
             Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.crossing,
             QRH.SilDensitySplit.Hybrid.cross])
         | (right; norm_num [Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.QuadraticSigns,
             Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.geometryCoeff,
             Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.crossing,
             QRH.SilDensitySplit.Hybrid.cross]))))
