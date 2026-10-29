/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.LowRestartBank.First
import Candidate.Local.Qrh.JointDetector.LowRestartBank.Second
import Candidate.Local.Qrh.JointDetector.LowRestartBank.Curved
import Submissions.density_split_fine_chain.Source.ChainK15

namespace Qrh.JointDetector.LowRestartBank
noncomputable section
open OAI.SevenEighths QRH.Record1252270103Source

/-- The first restart uses the existing native intermediate face, before its
later density-chain weakening. -/
theorem first_source
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (87393871/100000000:ℝ)) :
    GlobalSource (99999/100000:ℝ) (1283620970349/500000000000:ℝ) (1/10:ℝ) := by
  apply First.source hβ hceiling
  simpa only [QRH.SilDensitySplit.Face.Source, QRH.SilDensitySplit.K15.bootFace] using
    QRH.SilDensitySplit.K15.boot_source hβ

/-- A direct native seed followed by the second finite LOW restart. -/
theorem second_source
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (43691837/50000000:ℝ)) :
    GlobalSource (999999999/1000000000:ℝ) (513373181897/200000000000:ℝ) (1/10:ℝ) := by
  apply Second.source hβ hceiling
  exact NativeDirectSource.global_source _ (by norm_num) hβ

/-- The final curved round starts with a separate native seed and the
already established preceding global Hecke ceiling. -/
theorem curved_source
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ (1747671527/2000000000:ℝ)) :
    GlobalSource (999999999/1000000000:ℝ) (2566860586289/1000000000000:ℝ) (1/10:ℝ) := by
  apply Curved.source hβ hceiling
  exact NativeDirectSource.global_source _ (by norm_num) hβ

#print axioms first_source
#print axioms second_source
#print axioms curved_source
end
end Qrh.JointDetector.LowRestartBank
