/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Second-row geometry for the actual modified coefficient. The ordinary datum
is used only as a carrier of geometric fields; its coefficient is replaced
before forming any physical block or column norm. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondSectors
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondRowState

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstSectors
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondRetainedRows CenteredMomentSecondLiveBlock
open CenteredMomentSecondRetainedAggregate
open CenteredMomentSectorLocalization CenteredMomentHeckeColumnWindow
open Cycle61InitialMass Record1252270103Second
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance secondDataSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

abbrev ModifiedSecondPair {ι : Type*} [Fintype ι] (s : Input ι)
    (modifier : Tuple ι→ℂ) (R seed : Ideal O) :=
  ↥(commonLabels
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)))
    (supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed))))

/-- Construct the actual row family from modified active columns. No map to
the active columns of the ordinary coefficient is used. -/
def modifiedSecondDatum (slots : Finset α) (s : Input slots) (modifier : Tuple slots→ℂ)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ModifiedSecondPair s modifier R seed)
    (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (dyad : Fin 4→ℤ) : SecondInputDatum α :=
  let hp := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CoupledFirst.coefficient s modifier R seed)) _ _ p.property
  let hg := CoupledFirst.actual_common_gates s modifier R seed hseed hz₁ hz₂ _ _ p.property
  let hf := exists_row_budgeted_second_family s.η _ _ hp.1 hp.2 hg.2.2.1 U
  { slots:=slots,input:=s,R:=R,seed:=seed,C:=p.val.1,D:=p.val.2,
    hC:=hp.1,hD:=hp.2,sameSupport:=hg.2.2.1,inactive:=U,
    radius:=radius,rows:=rows,rows_ne:=hrows,K:=K,K_pos:=hK,dyad:=dyad,
    τ:=Classical.choose hf,family:=(Classical.choose_spec hf).1,
    rowBudget:=(Classical.choose_spec hf).2 }

/-- The actual block keeps every geometric field and the full modified
finite-column coefficient. -/
def modifiedDatumBlock (d : SecondInputDatum α) (modifier : Tuple d.slots→ℂ) :
    SecondBlockSource :=
  { d.block with beta:=CoupledFirst.coefficient d.input modifier d.R d.seed }

theorem modified_datum_block_value (d : SecondInputDatum α)
    (modifier : Tuple d.slots→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (modifiedDatumBlock d modifier).value W=
      physicalBlock d.input.η d.input.t (finiteColumns (Fintype.piFinset d.input.pools))
        (CoupledFirst.coefficient d.input modifier d.R d.seed)
        d.C d.D d.hC d.hD d.inactive d.radius d.rows W d.K d.dyad := rfl

theorem modified_second_seed_and_caps
    (slots : Finset α) (s : Input slots) (modifier : Tuple slots→ℂ)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (p : ModifiedSecondPair s modifier R seed)
    (U : Finset (CommonIndex p.val.1 p.val.2))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (dyad : Fin 4→ℤ) :
    let d:=modifiedSecondDatum slots s modifier R seed hseed hz₁ hz₂ p U radius rows hrows K hK dyad
    d.seed∣d.C ∧ d.seed∣d.D ∧
      (d.C.absNorm:ℝ)≤sourceRadius s ∧ (d.D.absNorm:ℝ)≤sourceRadius s := by
  exact (CoupledFirst.actual_common_gates s modifier R seed hseed hz₁ hz₂ _ _ p.property).2.2.2

/-- The second row and projector types do not depend on the coefficient.
In particular these are equalities of the actual finite sets, not bounds
obtained by deleting a projector or contracting coefficients. -/
theorem modified_second_live_rows {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) :
    secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l))=
      secondLiveRows (fun l=>(d l).block) := rfl

theorem modified_second_active_sectors {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) :
    secondActiveSectors (fun l=>modifiedDatumBlock (d l) (modifier l))=
      secondActiveSectors (fun l=>(d l).block) := rfl

theorem modified_second_encoded_row {Label : Type*} [Fintype Label]
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (first : Label→Cycle61Moment.FirstSourceLabel)
    (r : secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l))) :
    secondEncodedRow (fun l=>modifiedDatumBlock (d l) (modifier l)) first r=
      secondEncodedRow (fun l=>(d l).block) first r := rfl

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_datum_block_value
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_seed_and_caps
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_live_rows
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_active_sectors
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.modified_second_encoded_row
