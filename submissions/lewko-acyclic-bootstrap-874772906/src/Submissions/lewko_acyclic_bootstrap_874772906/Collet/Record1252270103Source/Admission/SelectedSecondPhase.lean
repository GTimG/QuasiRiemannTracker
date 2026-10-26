/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual complete second family supplies the paid-HIGH phase gate.
Parent volume, first allocation and MAIN radius are literal; every keep predicate
and its complement use the same original whole-block nonzero carrier. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighPaidComparison
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedSecondPhase
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical CenteredMomentSecondInputCapacitySource
open CenteredMomentSectorLocalization Cycle61InitialMass Cycle61Moment Record1252270103Second
open OAI.SevenEighths.Record1252270103Source
open High High.GlobalPhysical SecondSectorDatum
open SelectedHighCofactorFamily SelectedHighPaid
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- The chosen first allocation is fixed before second block and row selection. -/
structure FirstStage {α:Type}[Fintype α](s:Input α)(reflected:Bool)(R:Ideal O)(l:FirstSourceLabel) where
  B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1)
  τ : Character
  t : ℝ

namespace FirstStage
variable {α:Type}[Fintype α]{s:Input α}{reflected:Bool}{R:Ideal O}{l:FirstSourceLabel}
def common (_v:FirstStage s reflected R l) : Ideal O:=if reflected then l.1.2 else l.1.1
def input (v:FirstStage s reflected R l) : Input (liveIndices v.B.val):=child s v.common R v.B v.τ v.t
def height (_v:FirstStage s reflected R l) (Z D amp ξ reserve:ℝ):ℝ:=
  firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve l
theorem height_pos (v:FirstStage s reflected R l) (Z D amp ξ reserve:ℝ)(hZ:0<Z):0<v.height Z D amp ξ reserve:=
  first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*amp) reserve hZ l
end FirstStage

/-- The actual original support gates descend definitionally to the child.
This holds for every raw row and arbitrary keep, including its complement;
finite and ratio restrictions require only specializing the same row argument. -/
theorem actual_second_phase_bound {α Label:Type}[Fintype α][Fintype Label]
    (N:ℕ)(lo ap:ℝ)(hlo:0<lo)(hap:0<ap)
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (D Z ξ reserve:ℝ)(hZ:0<Z)(hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected:Bool)
    (column:Label→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (hN:Fintype.card α≤N)(hlower:lo≤s.lower)
    (hW₁:∀x,s.W₁ x≠0→ap≤x)(hW₂:∀x,s.W₂ x≠0→ap≤x)
    (hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (stage:∀l,FirstStage s reflected R (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)))
    (childModifier:∀l,Tuple (liveIndices (stage l).B.val)→ℂ)
    (hseed:∀l,Squarefree (column l).2.1.val)(Tsec amp:Label→ℝ)
    (P:Label→Finset (Ideal O))(H0 radius:Label→ℝ)(ell:ℝ)(hell:0<ell)
    (hrad:∀l,0≤radius l+6*amp l)
    (keep:∀l,BlockIndex (stage l).input (childModifier l) (R*(stage l).common)
      (column l).2.1.val ((stage l).height Z D (amp l) ξ reserve) (Tsec l) Z ξ→O→Prop):
    let extra:=fun l=>mainExtra s (stage l).common (P l) (H0 l) (radius l) (amp l) ell
    let amplitude:=fun l=>
      ‖CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) (column l)‖^2*
      extra l*‖frozenCoefficient (stage l).B.val (stage l).common R s.ν s.W s.P‖^2
    let datum:=familyDatum (fun l=>liveIndices (stage l).B.val) (fun l=>(stage l).input)
      childModifier (fun l=>R*(stage l).common) (fun l=>(column l).2.1.val) hseed (fun _=>hz₁) (fun _=>hz₂)
      ballProfile (fun l=>(stage l).height Z D (amp l) ξ reserve) Tsec (fun _=>Z) (fun _=>ξ)
      (fun l=>(stage l).height_pos Z D (amp l) ξ reserve hZ) keep
    let phase:=familyWeight (fun l=>liveIndices (stage l).B.val) (fun l=>(stage l).input)
      childModifier (fun l=>R*(stage l).common) (fun l=>(column l).2.1.val)
      ballProfile (fun l=>(stage l).height Z D (amp l) ξ reserve) Tsec
      (fun _=>Z) (fun _=>ξ) (fun _=>volume s) amplitude keep
    let block:=fun q=>modifiedDatumBlock (datum q) (childModifier q.1)
    ∀(r:SecondRow block)(second:Bool)
      (sel:Selection s reflected second
        (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column r.1.1))
        (datum r.1).C (datum r.1).D R),
    sel.B₁=(stage r.1.1).B→
    PhaseBound s modifier R seed W D Z ξ (amp r.1.1) reserve hK bin reflected second
      (column r.1.1) (datum r.1).C (datum r.1).D (datum r.1).inactive sel
      (extra r.1.1) (lowerFactor N lo ap)
      (‖secondEffectiveWeight block phase ballProfile r.1‖*(datum r.1).block.outside*
        volume (datum r.1).input) := by
  intro extra amplitude datum phase block r second sel hB₁
  have he (l:Label):0≤extra l:=by
    dsimp only [extra,mainExtra]
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg (hrad l) hell.le)
  have ha (l:Label):0≤amplitude l:=
    mul_nonneg (mul_nonneg (sq_nonneg _) (he l)) (sq_nonneg _)
  have hweight (q:CompleteFamily (fun l=>liveIndices (stage l).B.val) (fun l=>(stage l).input)
      childModifier (fun l=>R*(stage l).common) (fun l=>(column l).2.1.val) ballProfile
      (fun l=>(stage l).height Z D (amp l) ξ reserve) Tsec (fun _=>Z) (fun _=>ξ)):
      ‖phase q‖≤amplitude q.1/volume s:=
    actual_family_weight_parent (fun l=>liveIndices (stage l).B.val) (fun l=>(stage l).input)
      childModifier (fun l=>R*(stage l).common) (fun l=>(column l).2.1.val) ballProfile
      (fun l=>(stage l).height Z D (amp l) ξ reserve) Tsec
      (fun _=>Z) (fun _=>ξ) (fun _=>volume s) amplitude (fun _=>volume_pos s) ha keep q
  have hh:=actual_effective_weight_parent_bound N lo ap hlo hap datum
    (fun q=>childModifier q.1) phase ballProfile hN
    (fun _=>hlower) (fun _=>hW₁) (fun _=>hW₂)
    (fun q=>amplitude q.1) (fun _=>volume s) (fun _=>volume_pos s) hweight r
  change _≤(amplitude r.1.1/volume s)*((stage r.1.1).height Z D (amp r.1.1) ξ reserve/lowerFactor N lo ap)*
    normalizer (datum r.1).C (datum r.1).D (datum r.1).inactive at hh
  simpa only [PhaseBound,hB₁,amplitude,FirstStage.height,FirstStage.common,block,
    CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hh

end
end QRH.Record1252270103Source.Admission.SelectedSecondPhase
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondPhase.FirstStage.height_pos
#print axioms QRH.Record1252270103Source.Admission.SelectedSecondPhase.actual_second_phase_bound
