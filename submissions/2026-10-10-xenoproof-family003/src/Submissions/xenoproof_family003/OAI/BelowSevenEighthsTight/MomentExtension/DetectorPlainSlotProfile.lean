/- UNVERIFIED adapters retaining original physical plain moment objects. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainSlotProfile
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {Δ total margin recordMesh : ℝ}{D:_root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin recordMesh}

lemma conjugate_source_support_retuned (F:_root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

end SevenEighths.CenteredMomentDetectorPlainSlotProfile

end

end OAI

#print axioms OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile.conjugate_source_support_retuned
