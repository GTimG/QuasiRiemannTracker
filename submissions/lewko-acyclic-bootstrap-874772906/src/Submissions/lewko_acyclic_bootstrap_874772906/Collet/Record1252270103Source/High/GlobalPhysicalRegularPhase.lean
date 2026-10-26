/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular CompleteFamily supplies the scalar phase inlet to both
source branches, with the original parent-volume normalization. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularAbsoluteData
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical CenteredMomentSecondInputCapacitySource
open CenteredMomentSectorLocalization Cycle61InitialMass Cycle61Moment Record1252270103Second
open Admission.SelectedRegularSourceData Admission.SelectedSecondPhase Admission.SelectedHighPaid
local notation "O"=>HeckeFamily.O
local instance regularPhaseDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {α Label:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}(F:Family a Label)

def regularFamilyKeep:Admission.SelectedRegularAbsolute.Keep F:=
  Admission.SelectedSecondNatural.regularKeep F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ F.χ₀ F.Q F.m

def regularFamilyWeight (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)(ell:ℝ):
    F.Complete→ℂ:=
  Admission.SelectedRegularAbsolute.effectivePhase F W P H0 radius ell (regularFamilyKeep F)

theorem regular_family_datum (q:F.Complete):
    Admission.SelectedRegularAbsolute.datum F (regularFamilyKeep F) q=F.datum q:=rfl

/-- No bound on a phase or effective row weight is an input here. -/
theorem actual_regular_phase (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (hN:Fintype.card α≤N)(hlower:lo≤F.s.lower)
    (hW₁:∀x,F.s.W₁ x≠0→ap≤x)(hW₂:∀x,F.s.W₂ x≠0→ap≤x)
    (W:𝓢(ℝ,ℂ))(P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)(ell:ℝ)
    (hell:0<ell)(hrad:∀l,0≤radius l+6*F.amp l)
    {Row:Type}(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)(r:rows):
    PhaseBound F.s F.modifier F.R F.seed W F.D Z F.ξ (F.amp (G.row r).val.1.1)
      F.reserve F.hK F.bin F.reflected second (G.column r)
      (G.datum r).C (G.datum r).D (G.datum r).inactive (G.sel r)
      (mainExtra F.s (F.stage (G.row r).val.1.1).common (P (G.row r).val.1.1)
        (H0 (G.row r).val.1.1) (radius (G.row r).val.1.1) (F.amp (G.row r).val.1.1) ell)
      (lowerFactor N lo ap)
      (residualWeight F.datum (regularFamilyWeight F W P H0 radius ell) (G.row r).val):=by
  let amplitude:=Admission.SelectedRegularAbsolute.amplitude F W P H0 radius ell
  let phase:=Admission.SelectedRegularAbsolute.phase F W P H0 radius ell (regularFamilyKeep F)
  have ha(l:Label):0≤amplitude l:=
    Admission.SelectedRegularAbsolute.amplitude_nonneg F W P H0 radius ell hell hrad l
  have hw(q:F.Complete):‖phase q‖≤amplitude q.1/volume F.s:=
    actual_family_weight_parent F.slots F.input F.childModifier F.mask F.childSeed ballProfile
      F.Hmain F.Tsec (fun _=>Z) (fun _=>F.ξ) (fun _=>volume F.s) amplitude
      (fun _=>volume_pos F.s) ha (regularFamilyKeep F) q
  have hh:=actual_effective_weight_parent_bound N lo ap hlo hap F.datum
    (fun q=>F.childModifier q.1) phase ballProfile hN
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂)
    (fun q=>amplitude q.1) (fun _=>volume F.s) (fun _=>volume_pos F.s) hw (G.row r).val
  change _≤(amplitude (G.row r).val.1.1/volume F.s)*(F.Hmain (G.row r).val.1.1/lowerFactor N lo ap)*
    normalizer (G.datum r).C (G.datum r).D (G.datum r).inactive at hh
  simpa only [PhaseBound,G.first_allocation r,amplitude,Admission.SelectedRegularAbsolute.amplitude,
    FirstStage.height,FirstStage.common,Family.first,Anchor.label,Selected.column,Selected.datum,
    Family.Hmain,regularFamilyWeight,Admission.SelectedRegularAbsolute.effectivePhase,
    Admission.SelectedRegularAbsolute.datum,regular_family_datum,phase,residualWeight,
    CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_family_datum
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_regular_phase
