import OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Cycle25.Assembly.Count.MomentDetectorEnergyInitialState
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorPlainSlotProfile Cycle25ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
variable {D:Cycle25.Weighted.MomentData}

lemma weighted_conjugate_source_support (F:Cycle25ProbeFinalAssembly.WeightedSourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

end SevenEighths.Cycle25CenteredMomentDetectorPlainSlotProfile

end

end OAI
