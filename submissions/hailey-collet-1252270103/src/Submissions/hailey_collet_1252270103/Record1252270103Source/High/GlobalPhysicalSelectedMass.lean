/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal selected two-stage weights enter the same balanced first mass and
second allocation coefficient used by the checked cofactor suppliers. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSectorWeight
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalHighMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedHighCofactorFamilyData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstSourceReduction Cycle61InitialMass Cycle61Moment Record1252270103Second
open OAI.SevenEighths.Record1252270103Source
open Admission.SelectedHighCofactorFamily Admission.SelectedHighCofactorCoordinates
local notation "O"=>HeckeFamily.O
local instance selectedMassDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

/-- This is the literal weight left by the second allocation/forced choice;
the forced allocation was already paid by its uniform inverse-seed mass. -/
def selectedPaidWeight {α:Type}[Fintype α]{s:Input α}{reflected second:Bool}
    {l:FirstSourceLabel}{C₂ D₂ R:Ideal O}(sel:Selection s reflected second l C₂ D₂ R)(ω:ℝ):ℝ :=
  let s₁:=sel.firstInput
  let Cchosen:=if second then D₂ else C₂
  let s₂:=child s₁ Cchosen (R*(if reflected then l.1.2 else l.1.1)) sel.B₂ sel.τ₂ sel.t₂
  ((actualAllocations s₁.pools Cchosen).card:ℝ)^2*
    ‖frozenCoefficient sel.B₂.val Cchosen (R*(if reflected then l.1.2 else l.1.1))
      s₁.ν s₁.W s₁.P‖^2*(volume s₂/volume s₁)*forcedProfileCost s₂*ω

/-- No free cofactor coefficient or volume budget appears. The original
phase and the actual second-allocation coefficient are definitionally those
used in the uniform selected HIGH family theorem. -/
theorem actual_selected_paid_weight {α:Type}[Fintype α]
    (s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))
    (D Z ξ amp reserve ε:ℝ)(hZ:0<Z)(hK:0<Z^D)(hε:0≤ε)
    (bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ)(he:0≤extra)(hl:0<lower)
    (hω:ω≤
      (‖CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j‖^2*
      extra*‖frozenCoefficient sel.B₁.val
        (if reflected then (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.2
          else (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.1)
        R s.ν s.W s.P‖^2/volume s)*
      (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
        (Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j)/lower)*
      normalizer C₂ D₂ U):
    selectedPaidWeight sel ω≤
      (extra*((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)^2*
        Z^amp/lower*forcedProfileCost s)*
      CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ ε hK bin j*
      sel.raw U Z D amp ξ reserve := by
  let l:=Admission.FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j
  let scalar:=CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
    (Real.logb Z (volume s)) hK bin
    (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j
  have hmain:0≤firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve l:=
    (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*amp) reserve hZ l).le
  have hh:=selected_two_allocation_weight s (if reflected then l.1.2 else l.1.1) R sel.B₁
    sel.τ₁ sel.t₁ C₂ D₂ hC₂ U second sel.B₂ sel.τ₂ sel.t₂ scalar extra
    ((actualAllocations sel.firstInput.pools (if second then D₂ else C₂)).card:ℝ)
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve l)
    lower Z amp ε ω he hmain hl hZ hε hω
  have hideal:CoupledFirst.geometryColumnIdeal reflected s modifier R seed (Z^D) Z ξ hK bin j=
      if reflected then l.1.2 else l.1.1:=by cases reflected <;> rfl
  unfold CoupledFirst.balancedFirstHighMass
  rw [hideal]
  dsimp only [selectedPaidWeight,Selection.raw,secondAllocationCoefficient,Selection.firstInput]
  simpa only [scalar,l,Selection.firstInput,CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume,mul_assoc] using hh

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_selected_paid_weight
