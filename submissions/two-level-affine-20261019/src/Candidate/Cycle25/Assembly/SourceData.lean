import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.MomentFinalAssemblyData
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.Cycle25ProbeFinalAssembly
open ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

instance sourceDataNeZero {D : WeightedQRH.MomentData} (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance sourceDataFinite {D : WeightedQRH.MomentData} (F : OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

end SevenEighths.Cycle25ProbeFinalAssembly
end
end OAI

/- Actual source data adapted unchanged from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
The legacy count-parameter existence helper is not a Cycle25 count estimate. -/
