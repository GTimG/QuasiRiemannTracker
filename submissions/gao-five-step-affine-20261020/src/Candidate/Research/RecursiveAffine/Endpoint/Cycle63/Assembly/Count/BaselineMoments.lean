import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Count.BaselineGeometry
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Count.MomentGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorBudget
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.Parameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Candidate.Cycle25.Assembly.SourceData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.MomentDetectorInverseFields
import Candidate.Cycle25.Assembly.Count.MomentDetectorPlainMarkedFineField
import Candidate.Research.RecursiveAffine.Endpoint.Cycle25.Assembly.Count.PlainInput
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.CountAffine.SourceMoments

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Count_BaselineMoments : Cycle63.AffineLedger := Cycle153.Root.rootLedger


namespace OAI.SevenEighths.Cycle153EndpointDetectorCount
noncomputable section
open scoped Classical
open Filter HeckeFamily

/-- The source window/exclusions are the genuine original physical source data.
Only the pure slot/moment contract is reused; it has no endpoint geometry. -/
abbrev BaselineSourceData (D : BaselineData) :=
  OAI.SevenEighths.ProbeFinalAssembly.WeightedSourceData D.toMomentData

def baselineSource (D : BaselineData) (F : BaselineSourceData D) : SourceData where
  S:=F.S
  exclusions:=F.exclusions
  maximal:=F.maximal
  w:=F.w
  smooth:=F.smooth
  compact:=F.compact
  support:=F.support
  positive_support:=F.positive_support
  bounded:=F.bounded
  nonzero:=F.nonzero

theorem exists_baseline_source (D : BaselineData) : Nonempty (BaselineSourceData D) :=
  OAI.SevenEighths.ProbeFinalAssembly.weighted_exists_source_data D.toMomentData

/-- Genuine original MI/MP0 and κ-marked MP inputs on the new exact slot lengths, and
Collet's affine marked plain moment on every detector fiber. The polynomial degree is chosen
for each character, since the affine moment's degree is uniform only over finite families. -/
theorem actual_baseline_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : Cycle153EndpointProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200)
    (mesh : ℝ → ℝ) (hdet : Cycle153EndpointProbeFinalAssemblyCertifiedBands.DetectorAffineInputAt mesh)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hfineA : ∀j,D.length j≤ mesh D.t/200) :
    ∀η:Character,∃J:ℝ,0≤J ∧ ∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤1→
      ∀ᶠZ:ℝ in atTop,SourceMomentBound D.toData (baselineSource D F) counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle153EndpointProbeFinalAssembly.weighted_actual_source_moments_A F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hβ hκβ counts hfine (hdet F hβ hβhi hfineA)
end
end OAI.SevenEighths.Cycle153EndpointDetectorCount
