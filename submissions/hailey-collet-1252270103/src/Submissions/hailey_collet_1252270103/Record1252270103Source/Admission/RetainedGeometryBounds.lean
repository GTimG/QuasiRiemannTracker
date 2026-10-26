/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedGeometryData
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondChildCaps
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
open High.GlobalPhysical CenteredMomentAmplificationChildSourceCaps
open CenteredMomentWholeSlotDeletion CenteredMomentEnergyReindex CenteredMomentHeckeSlots Record1252270103Second QRH.Record1252270103Low
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


local notation "Labels"=>Label reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec
variable (V : Fin 4→ℝ→ℂ) (hj : j∈firstLiveColumns (source s modifier R seed K Z ξ hK key) V)
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hH : 0<H)
local notation "data"=>datum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec V hj hz₁ hz₂ hH

theorem datum_card (q : Labels) : Fintype.card (data q).slots≤Fintype.card ι := live_card_le q.1.val

theorem datum_slots_original (q : Labels) (i : (data q).slots) :
    (data q).input.slots i=s.slots i.val ∧
    restoredSlotCoeff (data q).input i=restoredSlotCoeff s i.val ∧
    (data q).input.P i=s.P i.val := ⟨rfl,rfl,rfl⟩

theorem datum_full_slots_image {J : Type*} [Fintype J] (q : Labels)
    (f : J↪(data q).slots) (η : Character) (m A z : O) (height : ℝ) :
    (∏k,normalizedSlot η m A z ((data q).input.slots (f k))
      (restoredSlotCoeff (data q).input (f k)) height ((data q).input.P (f k)))=
    ∏i : slotRange (FirstFamily.childEmbedding q.1.val f),normalizedSlot η m A z
      (s.slots i) (restoredSlotCoeff s i) height (s.P i) :=
  FirstFamily.child_full_slots_image s Cj R q.1 τj t f η m A z height

/-- Original parent volume and endpoint controls give both actual child
caps. The only allocation gate is its literal nonzero frozen scalar. -/
theorem datum_volume_and_radius (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (hcard : Fintype.card ι≤N) (he : Endpoints b bs bs s) (q : Labels)
    (hf : frozenCoefficient q.1.val Cj R s.ν s.W s.P≠0) :
    volume (data q).input≤b^N*volume s/((Cj).absNorm:ℝ) ∧
    sourceRadius (data q).input≤geometry N b bs bs*volume s/((Cj).absNorm:ℝ) :=
  ⟨common_volume_le N b hb s hcard he.1 Cj R q.1 τj t hf,
    actual_common_child_source_cap N b bs hb hbs s hcard he Cj R q.1 τj t hf⟩

def SupportedLabel := {q : Labels // frozenCoefficient q.1.val Cj R s.ν s.W s.P≠0}
local notation "SupportedLabels"=>SupportedLabel reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec
instance : Fintype SupportedLabels := by unfold SupportedLabel;infer_instance
def supportedDatum (q : SupportedLabels) : SecondInputDatum ι := data q.val
local notation "sdata"=>supportedDatum reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P t H Tsec V hj hz₁ hz₂ hH

theorem supported_row_caps (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (hcard : Fintype.card ι≤N) (he : Endpoints b bs bs s)
    (r : secondLiveRows (fun q=>(sdata q).block)) :
    let d:=sdata r.val.1
    Fintype.card d.slots≤N ∧
    volume d.input≤b^N*volume s/((Cj).absNorm:ℝ) ∧
    sourceRadius d.input≤geometry N b bs bs*volume s/((Cj).absNorm:ℝ) ∧
    (d.C.absNorm:ℝ)≤geometry N b bs bs*volume s/((Cj).absNorm:ℝ) ∧
    (d.D.absNorm:ℝ)≤geometry N b bs bs*volume s/((Cj).absNorm:ℝ) := by
  intro d
  have hc:=datum_volume_and_radius reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P
    t H Tsec V hj hz₁ hz₂ hH N b bs hb hbs hcard he r.val.1.val r.val.1.property
  have hn:=datum_seed_and_caps reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P
    t H Tsec V hj hz₁ hz₂ hH r.val.1.val
  exact ⟨(datum_card reflected s modifier R seed K Z ξ hK key j A₁ A₂ D Kmark F P
    t H Tsec V hj hz₁ hz₂ hH r.val.1.val).trans hcard,hc.1,hc.2,
    hn.2.2.1.trans hc.2,hn.2.2.2.trans hc.2⟩

/-- The MAIN secondary scale dominates the square of the actual child
volume divided by the same positive MAIN radius. -/
theorem supported_row_nominal (N : ℕ) (b : ℝ) (hb : 1≤b)
    (hcard : Fintype.card ι≤N) (he : s.upper≤b)
    (r : secondLiveRows (fun q=>(sdata q).block)) :
    (volume (sdata r.val.1).input)^2/H≤(b^N*volume s/((Cj).absNorm:ℝ))^2/H := by
  have hh:=common_volume_le N b hb s hcard he Cj R r.val.1.val.1 τj t r.val.1.property
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (volume_pos (sdata r.val.1).input).le hh 2) hH.le

end
end QRH.Record1252270103Source.Admission.RetainedGeometry
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_card
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_slots_original
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_full_slots_image
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.datum_volume_and_radius
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.supported_row_caps
#print axioms QRH.Record1252270103Source.Admission.RetainedGeometry.supported_row_nominal
