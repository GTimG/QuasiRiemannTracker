/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.Common
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ActualPhysicalCoreCount
namespace Qrh.JointDetector.RestartSourceChains
noncomputable section

/-- The concrete natural-row count discharges the sole explicit inlet used
by the generated finite source chains. No analytic premise remains. -/
theorem actualParentCores : ParentCoreProvider := by
 intro floor B L c hf hfhi hBmin hB hL hc0 hc hparent hβ
 exact RepeatedMarks.physicalCoreCount_of_globalSource floor B L c
   hf hfhi hBmin hB hL hc0 hc hparent hβ

#print axioms actualParentCores
end
end Qrh.JointDetector.RestartSourceChains
