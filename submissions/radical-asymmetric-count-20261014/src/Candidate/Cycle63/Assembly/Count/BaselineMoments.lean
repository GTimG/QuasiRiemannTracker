import Candidate.Cycle63.Assembly.Count.BaselineGeometry
import Candidate.Cycle63.Assembly.Count.MomentGates
import Candidate.Cycle25.Assembly.Count.ActualMoments

namespace OAI.SevenEighths.Cycle63DetectorCount
noncomputable section
open scoped Classical
open Filter HeckeFamily

/-- The source window/exclusions are the genuine original physical source data.
Only the pure slot/moment contract is reused; it has no endpoint geometry. -/
abbrev BaselineSourceData (D : BaselineData) :=
  Cycle25ProbeFinalAssembly.WeightedSourceData D.toMomentData

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
  Cycle25ProbeFinalAssembly.weighted_exists_source_data D.toMomentData

/-- Genuine original MI/MP0 and κ-marked MP inputs on the new exact slot lengths,
from the completed parameterized κ certificate. No affine interior estimate or
improved quartic endpoint is used. -/
theorem actual_baseline_source_moments (D : BaselineData) (F : BaselineSourceData D)
    (counts : Cycle25ProbeHighRowFamily.CountParameters (baselineSource D F).modulus ⊤ D.t)
    (hβ : 51/100≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) :
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧ ∀τ:ℝ,0<τ→τ≤1→
      ∀ᶠZ:ℝ in atTop,SourceMomentBound D.toData (baselineSource D F) counts η Z τ
        (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact Cycle25ProbeFinalAssembly.weighted_actual_source_moments F D.momentKappa
    D.momentKappa_lo D.momentKappa_hi hβ hκβ counts hfine
end
end OAI.SevenEighths.Cycle63DetectorCount
