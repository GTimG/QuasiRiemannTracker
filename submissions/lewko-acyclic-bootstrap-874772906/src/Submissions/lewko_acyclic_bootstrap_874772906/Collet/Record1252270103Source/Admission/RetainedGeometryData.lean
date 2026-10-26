/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual modified MAIN children as retained second families in the original
ambient slot type. All finite coefficients, seeds and masks are literal. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalSecondRetainedData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilySingletons
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FirstFamilyGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalAllocationMain
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.RetainedGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentSectorLocalization Cycle61InitialMass Record1252270103Second
open Record1252270103Source.Collision QRH.Record1252270103Low
open High.GlobalPhysical
local notation "O"=>ActualEisensteinCubic.O
local notation "source"=>High.CoupledFirst.geometryFirstSource
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable (reflected : Bool) (s : Input ι) (modifier : Tuple ι→ℂ)
  (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
  (j : FirstColumnIndex (source s modifier R seed K Z ξ hK key))
local notation "Cj"=>FirstFamily.columnIdeal reflected s modifier R seed K Z ξ hK key j
local notation "τj"=>FirstFamily.columnCharacter reflected s modifier R seed K Z ξ hK key j
variable (A₁ A₂ D Kmark : Ideal O) (F : Ideal O→ℂ) (P : Finset (Ideal O)) (t H Tsec : ℝ)

/-- The correction counts the current residual modulus. Accumulated ordinary
factors, D*Cj in F, and the frozen marked product all remain. -/
def mainModifier (B : actualAllocations s.pools Cj) : Tuple (liveIndices B.val)→ℂ :=
  markedSourceModifier (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) 1
    (Kmark*markedProduct B.val)
    (fun J=>(((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P J).card)):ℂ)*F ((D*Cj)*J))

abbrev Child (B : actualAllocations s.pools Cj) := child s Cj R B τj t

/-- No active-source replacement occurs: the second block index uses the
full corrected coefficient of the actual first common child. -/
def Label := Σ B : actualAllocations s.pools Cj,
  BlockIndex (Child reflected s modifier R seed K Z ξ hK key j t B)
    (mainModifier reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P B)
    (R*Cj) j.2.1.val H Tsec Z ξ

local notation "Labels"=>Label reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec
instance : Fintype Labels := by unfold Label;infer_instance

variable (V : Fin 4→ℝ→ℂ) (hj : j∈firstLiveColumns (source s modifier R seed K Z ξ hK key) V)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hH : 0<H)

def datum (q : Labels) : SecondInputDatum ι :=
  modifiedRetainedDatum (liveIndices q.1.val)
    (Child reflected s modifier R seed K Z ξ hK key j t q.1)
    (mainModifier reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P q.1)
    (R*Cj) j.2.1.val
    (FirstFamily.live_projector_squarefree s modifier R seed K Z ξ hK key V j hj)
    hz₁ hz₂ H Tsec Z ξ hH q.2

local notation "data"=>datum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec V hj hz₁ hz₂ hH

def first (_q : Labels) : Cycle61Moment.FirstSourceLabel :=
  FirstFamily.firstLabel s modifier R seed K Z ξ hK key j

theorem datum_fields (q : Labels) :
    (data q).slots=liveIndices q.1.val ∧
    (data q).input=Child reflected s modifier R seed K Z ξ hK key j t q.1 ∧
    (data q).input.η=τj ∧ (data q).R=R*Cj ∧ (data q).seed=j.2.1.val ∧
    (data q).radius=frequencyRadius Tsec Z ξ ∧ (data q).dyad=(fun i=>(q.2.2.2 i:ℤ)) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem datum_R_comm (q : Labels) : (data q).R=Cj*R := mul_comm R Cj

theorem datum_block (q : Labels) (W : 𝓢(ℝ,ℂ)) :
    (modifiedDatumBlock (data q)
      (mainModifier reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P q.1)).value W=
      Record1252270103Second.originalBlock
        (Child reflected s modifier R seed K Z ξ hK key j t q.1)
        (mainModifier reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P q.1)
        (R*Cj) j.2.1.val W H Tsec Z ξ q.2 := rfl

theorem datum_seed_and_caps (q : Labels) :
    (data q).seed∣(data q).C ∧ (data q).seed∣(data q).D ∧
    ((data q).C.absNorm:ℝ)≤sourceRadius (data q).input ∧
    ((data q).D.absNorm:ℝ)≤sourceRadius (data q).input :=
  modified_retained_seed_and_caps _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem first_at_row (r : secondLiveRows (fun q=>(data q).block)) :
    first reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec r.val.1=
      FirstFamily.firstLabel s modifier R seed K Z ξ hK key j := rfl

end
end QRH.Record1252270103Source.Admission.RetainedGeometry
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_fields
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_R_comm
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_block
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_seed_and_caps
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.first_at_row
