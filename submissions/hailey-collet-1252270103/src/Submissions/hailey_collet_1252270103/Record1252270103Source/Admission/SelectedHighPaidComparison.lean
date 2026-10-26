/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite phase weight is paid uniformly before every selected family.
Both allocation cardinalities, the annular bands and genuine pool reciprocal remain literal. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSelectedMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainPrefactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighPaid
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentAddedZeroUniform CenteredMomentFirstAnnularMajorant
open Cycle61InitialMass Cycle61Moment Record1252270103Second
open CenteredMomentSecondCanonicalScalar Record12518109Natural.MarkedPlain
open CenteredMomentAmplificationChildSourceCaps
open OAI.SevenEighths.Record1252270103Source
open High High.GlobalPhysical SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open Pool
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

def mainExtra {α:Type}[Fintype α](s:Input α)(C:Ideal O)(P:Finset (Ideal O))
    (H0 radius amp ell:ℝ):ℝ :=
  ((bands H0).card:ℝ)*((actualAllocations s.pools C).card:ℝ)^2/(P.card:ℝ)*((radius+6*amp)/ell)

def PhaseBound {α:Type}[Fintype α](s:Input α)(modifier:Tuple α→ℂ)(R seed:Ideal O)
    (W:𝓢(ℝ,ℂ))(D Z ξ amp reserve:ℝ)(hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool)
    (j:FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
    (C₂ D₂:Ideal O)(U:Finset (CommonIndex C₂ D₂))
    (sel:Selection s reflected second (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j) C₂ D₂ R)
    (extra lower ω:ℝ):Prop :=
  ω≤(‖CoupledFirst.balancedColumnScalar reflected s modifier R seed (Z^D) Z ξ D
    (Real.logb Z (volume s)) hK bin
    (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R seed W (Z^D) Z ξ q)) j‖^2*
    extra*‖frozenCoefficient sel.B₁.val
      (if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.2
        else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j).1.1)
      R s.ν s.W s.P‖^2/volume s)*
    (firstMainRadius reflected (Z^D) (volume s) Z ξ (3*amp) reserve
      (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin j)/lower)*normalizer C₂ D₂ U

theorem selected_raw_nonneg {α:Type}[Fintype α]{s:Input α}{reflected second:Bool}
    {l:FirstSourceLabel}{C₂ D₂ R:Ideal O}(sel:Selection s reflected second l C₂ D₂ R)
    (hC₂:Supported C₂)(U:Finset (CommonIndex C₂ D₂))(Z D amp ξ reserve:ℝ)(hZ:0<Z):
    0≤sel.raw U Z D amp ξ reserve := by
  dsimp only [Selection.raw,secondAllocationCoefficient]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (Real.rpow_nonneg hZ.le _)
      (div_nonneg (first_main_radius_pos reflected (Z^D) (volume s) Z ξ (3*amp) reserve hZ l).le
        (volume_pos _).le)) (normalizer_pos C₂ D₂ hC₂ U).le) (sq_nonneg _))
      (div_nonneg (volume_pos _).le (volume_pos _).le)) (forcedProfileCost_nonneg _)

/-- The constant precedes all source Inputs, row families, selected children,
scales and actual prime pools. The cost may contain the complete literal
Newton cofactor square; this theorem only compares the exact finite weights. -/
theorem uniform_selected_paid_sum (N:ℕ)(B₁ B₂ ε ell lower radiusMax:ℝ)
    (hB₁:0≤B₁)(hB₂:0≤B₂)(hε:0<ε)(hell:0<ell)(hlower:0<lower)(hmax:0≤radiusMax):
    ∃C:ℝ,0<C ∧ ∀{α:Type}[Fintype α](s:Input α),Fintype.card α≤N→
    ∀(modifier:Tuple α→ℂ)(R seed:Ideal O)(W:𝓢(ℝ,ℂ))(D Z ξ reserve εmass:ℝ)
      (hK:0<Z^D)(bin:ℤ×(Fin 5→ℤ))(reflected second:Bool),0≤εmass→
    ∀{κ:Type}(labels:Finset κ)
      (column:κ→FirstColumnIndex (CoupledFirst.geometryFirstSource s modifier R seed (Z^D) Z ξ hK bin))
      (C₂ D₂:κ→Ideal O)(U:∀l,Finset (CommonIndex (C₂ l) (D₂ l)))
      (sel:∀l,Selection s reflected second
        (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)) (C₂ l) (D₂ l) R)
      (P:κ→Finset (Ideal O))(amp H0 radius mesh loss BD Bsource:κ→ℝ)(depth:κ→ℕ)
      (lossMax:ℝ)(ω cost:κ→ℝ),
      (∀l∈labels,Supported (C₂ l))→
      (∀l∈labels,((if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
        else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1).absNorm:ℝ)≤Z^B₁)→
      (∀l∈labels,((if second then D₂ l else C₂ l).absNorm:ℝ)≤Z^B₂)→
      (∀l∈labels,FixedCellPoolData (P l) Z (amp l) ell (mesh l) (loss l) (BD l) (Bsource l) (depth l))→
      (∀l∈labels,0<H0 l)→(∀l∈labels,0≤radius l+6*amp l)→
      (∀l∈labels,radius l+6*amp l≤radiusMax)→(∀l∈labels,loss l≤lossMax)→
      (∀l∈labels,PhaseBound s modifier R seed W D Z ξ (amp l) reserve hK bin reflected second
        (column l) (C₂ l) (D₂ l) (U l) (sel l)
        (mainExtra s (if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
          else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1)
          (P l) (H0 l) (radius l) (amp l) ell) lower (ω l))→
      (∀l∈labels,0≤cost l)→
      (∑l∈labels,cost l*selectedPaidWeight (sel l) (ω l))≤
      (C*Z^(ε+lossMax)*forcedProfileCost s)*
      ∑l∈labels,CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column l)*
        cost l*(sel l).raw (U l) Z D (amp l) ξ reserve := by
  obtain ⟨C,hC,hpref⟩:=MarkedMainPrefactor.uniform_main_prefactor N B₁ B₂ ε ell lower radiusMax
    hB₁ hB₂ hε hell hlower hmax
  refine ⟨C,hC,?_⟩
  intro α _ s hN modifier R seed W D Z ξ reserve εmass hK bin reflected second hεmass
    κ labels column C₂ D₂ U sel P amp H0 radius mesh loss BD Bsource depth lossMax ω cost
    hC₂ hcap₁ hcap₂ hpool hH hrad0 hrad hloss hphase hcost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  let C₁:=if reflected then (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.2
    else (FirstFamily.firstLabel s modifier R seed (Z^D) Z ξ hK bin (column l)).1.1
  let extra:=mainExtra s C₁ (P l) (H0 l) (radius l) (amp l) ell
  have hz:0<Z:=zero_lt_one.trans (hpool l hl).scale_gt_one
  have he:0≤extra:=by
    dsimp only [extra,mainExtra]
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _))
      (div_nonneg (hrad0 l hl) hell.le)
  have hp:=hpref s (sel l).firstInput hN ((live_card_le (sel l).B₁.val).trans hN)
    C₁ (if second then D₂ l else C₂ l) (P l) Z (amp l) (mesh l) (loss l) (BD l) (Bsource l) (depth l)
    (allocation_ne s C₁ (sel l).B₁) (allocation_ne (sel l).firstInput _ (sel l).B₂)
    (hcap₁ l hl) (hcap₂ l hl) (hpool l hl) (H0 l) (radius l) (hH l hl) (hrad0 l hl) (hrad l hl)
  have hpay:extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
      Z^(amp l)/lower≤C*Z^(ε+lossMax) := by
    have heq:extra*((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
        Z^(amp l)/lower=
        ((bands (H0 l)).card:ℝ)*((actualAllocations s.pools C₁).card:ℝ)^2*
        ((actualAllocations (sel l).firstInput.pools (if second then D₂ l else C₂ l)).card:ℝ)^2*
        (Z^(amp l)/(P l).card)*((radius l+6*amp l)/ell)/lower := by
      dsimp only [extra,mainExtra];ring
    rw [heq]
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hpool l hl).scale_gt_one.le (add_le_add_right (hloss l hl) ε)) hC.le)
  have hh:=actual_selected_paid_weight s modifier R seed W D Z ξ (amp l) reserve εmass hz hK hεmass
    bin reflected second (column l) (C₂ l) (D₂ l) (hC₂ l hl) (U l) (sel l) extra lower (ω l) he hlower (hphase l hl)
  have hm:0≤CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column l):=by
    unfold CoupledFirst.balancedFirstHighMass
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hr:=selected_raw_nonneg (sel l) (hC₂ l hl) (U l) Z D (amp l) ξ reserve hz
  have hh':selectedPaidWeight (sel l) (ω l)≤(C*Z^(ε+lossMax)*forcedProfileCost s)*
      CoupledFirst.balancedFirstHighMass reflected s modifier R seed W D Z ξ εmass hK bin (column l)*
      (sel l).raw (U l) Z D (amp l) ξ reserve :=
    hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpay (forcedProfileCost_nonneg s)) hm) hr)
  exact (mul_le_mul_of_nonneg_left hh' (hcost l hl)).trans_eq (by ring)

end
end QRH.Record1252270103Source.Admission.SelectedHighPaid
#print axioms QRH.Record1252270103Source.Admission.SelectedHighPaid.selected_raw_nonneg
#print axioms QRH.Record1252270103Source.Admission.SelectedHighPaid.uniform_selected_paid_sum
