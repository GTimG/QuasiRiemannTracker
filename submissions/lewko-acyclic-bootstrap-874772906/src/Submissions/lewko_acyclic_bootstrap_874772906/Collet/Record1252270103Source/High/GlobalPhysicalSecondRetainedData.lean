/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual modified retained second transform is a family of row data,
with the original complete-block zero filter preserved exactly. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSectors CenteredMomentSecondRetainedAggregate
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondRetainedRows CenteredMomentSecondLiveBlock
open CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow
open CenteredMomentSecondLocalization
open Cycle61InitialMass Record1252270103Second
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance secondRetainedDataSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def modifiedRetainedDatum (slots : Finset α) (s : Input slots) (modifier : Tuple slots→ℂ)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : BlockIndex s modifier R seed K Tsec Z ξ) :
    SecondInputDatum α :=
  modifiedSecondDatum slots s modifier R seed hseed hz₁ hz₂ q.1.val q.2.1
    (frequencyRadius Tsec Z ξ) (blockRows _ _ q.2.1 (frequencyRadius Tsec Z ξ))
    (fun z hz=>(liveRows_geometry _ _ _ _ _ z hz).2.1)
    K hK (fun i=>(q.2.2 i:ℤ))

theorem modified_retained_block (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : BlockIndex s modifier R seed K Tsec Z ξ)
    (W : 𝓢(ℝ,ℂ)) :
    let d:=modifiedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    (modifiedDatumBlock d modifier).value W=
      Record1252270103Second.originalBlock s modifier R seed W K Tsec Z ξ q := rfl

/-- The common row geometry is supplied by actual modified columns, and
every value in this equality still uses the full modified coefficient. -/
theorem actual_modified_retained_batch (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (W : 𝓢(ℝ,ℂ)) :
    let d:=fun q=>modifiedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    secondRetainedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed) W K Tsec Z ξ=
      ∑q∈(Finset.univ:Finset (BlockIndex s modifier R seed K Tsec Z ξ)).filter
        (fun q=>(modifiedDatumBlock (d q) modifier).value W≠0),
        blockWeight s modifier R seed K Tsec Z ξ q*(modifiedDatumBlock (d q) modifier).value W := by
  exact actual_retained_original_nonzero s modifier R seed hz₁ hz₂ W K Tsec Z ξ hK

/-- Bounds and seed divisibility are inherited from the actual modified
common-label witnesses; no ordinary column nonvanishing is asserted. -/
theorem modified_retained_seed_and_caps (slots : Finset α) (s : Input slots)
    (modifier : Tuple slots→ℂ) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (K Tsec Z ξ : ℝ) (hK : 0<K) (q : BlockIndex s modifier R seed K Tsec Z ξ) :
    let d:=modifiedRetainedDatum slots s modifier R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    d.seed∣d.C ∧ d.seed∣d.D ∧
      (d.C.absNorm:ℝ)≤sourceRadius s ∧ (d.D.absNorm:ℝ)≤sourceRadius s :=
  original_block_seed_and_caps s modifier R seed hseed hz₁ hz₂ K Tsec Z ξ q

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_retained_block
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_modified_retained_batch
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_retained_seed_and_caps
