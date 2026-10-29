/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceStepAffine

/-- Compact syntax for the same literal finite affine geometry checks. -/
macro "source_geometry" : tactic => `(tactic| refine {
 face := by constructor <;> norm_num
 B0_pos := by norm_num
 A_pos := by norm_num
 A_lt := by norm_num
 q_mem := by constructor <;> norm_num
 width_pos := by norm_num [Qrh.JointDetector.RepeatedMarks.SourceStep.crossing,
   QRH.SilDensitySplit.Hybrid.cross]
 low_payment := by norm_num
 low_overshoot := by norm_num
 endpoints := by
   constructor <;> intro i <;> fin_cases i <;>
     norm_num [Qrh.JointDetector.RepeatedMarks.SourceStep.affineIntercepts,
       Qrh.JointDetector.RepeatedMarks.SourceStep.affineSlopes,
       Qrh.JointDetector.RepeatedMarks.SourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross] })
