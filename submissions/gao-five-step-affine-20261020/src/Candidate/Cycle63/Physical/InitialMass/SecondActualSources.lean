import Candidate.Cycle63.Physical.InitialMass.SecondEncoding
import Candidate.Cycle63.Physical.InitialMass.SecondPhysicalWindows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass
open CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentCanonicalFirst
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondActiveCount
local instance secondActualSourcesDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev ActualSecondPair {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O) :=
  ↥(commonLabels
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)))
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))))

/-- A second input is constructed from actual active common labels. Its
character family is supplied by the proved finite-character construction. -/
def actualSecondInputDatum (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ActualSecondPair s R seed) (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (dyad : Fin 4→ℤ) : SecondInputDatum α :=
  let hp := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed))
      _ _ p.property
  let hg := actual_common_gates s R seed hseed hz₁ hz₂ _ _ p.property
  let hf := exists_row_budgeted_second_family s.η _ _ hp.1 hp.2 hg.2.2.1 U
  {slots:=slots,input:=s,R:=R,seed:=seed,C:=p.val.1,D:=p.val.2,
    hC:=hp.1,hD:=hp.2,sameSupport:=hg.2.2.1,inactive:=U,
    radius:=radius,rows:=rows,rows_ne:=hrows,K:=K,K_pos:=hK,dyad:=dyad,
    τ:=Classical.choose hf,family:=(Classical.choose_spec hf).1,
    rowBudget:=(Classical.choose_spec hf).2}

end
end OAI.SevenEighths.Cycle63InitialMass
