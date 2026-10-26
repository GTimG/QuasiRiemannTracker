/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All three LOW erasure branches are paid by the literal four-coordinate
weight and its actual first-label radius deficit. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalLowCoordinates
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61HighGeometry Cycle61InitialMass Cycle61Moment
open Record12518109Natural Record12518109Raw Record1252270103CommonGeometry
open QRH.Record12518109Source QRH.Record1252270103Low
local notation "O"=>HeckeFamily.O

theorem low_first_deficit_gates (reflected:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (Z:ℝ)(hZ:1<Z):
    let delta:=max (labelD reflected l Z-labelC reflected l Z) 0
    0≤delta ∧ delta≤labelC reflected l Z ∧ delta≤lowTypePenalty reflected l Z ∧
      0≤lowTypePenalty reflected l Z := by
  intro delta
  have hc:=commonPart_eq_left l.1.1 l.1.2 hC.1 heq
  have hd:=commonPart_eq_left l.1.2 l.1.1 hD.1 heq.symm
  have hcl:=left_common_width Z l.1.1 l.1.2 hbC hbD
  have hdr:=right_common_width Z l.1.1 l.1.2 hbC hbD
  rw [hc] at hcl
  rw [hd] at hdr
  have hn m n:=stratumWidth_nonneg Z hZ l.1.1 l.1.2 m n
  have hg:=first_source_deficit_bounds (!reflected) l hC hD heq hbC hbD Z hZ
  have hdc:delta≤labelC reflected l Z := by
    cases reflected <;> exact hg.1
  refine ⟨le_max_right _ _,hdc,?_,?_⟩
  · cases reflected <;> dsimp only [delta,labelD,labelC,lowTypePenalty,Bool.false_eq_true,ite_false,ite_true]
    · change max (normLog Z l.1.2-normLog Z l.1.1) 0≤stratumWidth Z l.1.1 l.1.2 1 2
      rw [hcl,hdr]
      exact max_le (by linarith [hn 2 1]) (hn 1 2)
    · change max (normLog Z l.1.1-normLog Z l.1.2) 0≤stratumWidth Z l.1.1 l.1.2 2 1
      rw [hcl,hdr]
      exact max_le (by linarith [hn 1 2]) (hn 2 1)
  · cases reflected <;> exact hn _ _

theorem actual_low_coordinate_payment (reflected second:Bool)(l:FirstSourceLabel)
    (hC:Supported l.1.1)(hD:Supported l.1.2)
    (heq:primeSupport l.1.1=primeSupport l.1.2)
    (hbC:ValuationAtMostTwo l.1.1)(hbD:ValuationAtMostTwo l.1.2)
    (C D:Ideal O)(hC₂:Supported C)(hD₂:Supported D)(heq₂:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D))
    (Z M A a ξ reserve err errv q B lam h F t b c f loss rho mesh erased g radial radialRound:ℝ)
    (hZ:1<Z)(hq:0≤q)(hB0:0≤B)(hB:B≤1)(hlam:1<lam)
    (hc:labelC reflected l Z≤c)(hf:0≤f)(hh:0≤h)(hqh:q*h≤1)
    (hgap:g=a-q*(b+(t-B*F)/lam))(hcap:(B*F-t)/lam≤h*F)
    (hloss:0≤loss)(hrho:0≤rho)
    (herased:erased≤max 0 (max
      (b-f-(B*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-max (labelD reflected l Z-labelC reflected l Z) 0-rho)))+mesh)
    (hrad:radial≤(childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U
      Z M A a ξ reserve err) errv) 2+radialRound):
    let x:=childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C D U Z M A a ξ reserve err) errv
    x 0+x 1+radial-labelSide reflected l Z A-labelSurplus reflected l Z+q*erased≤
      -min a g+q*(max ((B*rho+loss)/lam) (h*rho)+mesh)+err+errv+radialRound := by
  intro x
  obtain ⟨hd0,hdc,hdpen,hpen⟩:=low_first_deficit_gates reflected l hC hD heq hbC hbD Z hZ
  have hcc:0≤c:=hd0.trans (hdc.trans hc)
  have hsecond:0≤lowSecondPenalty second C D U Z:=actual_raw_second_nonneg second C D hC₂ hD₂ heq₂ U Z hZ
  have he:0≤labelE l Z := by
    apply Real.logb_nonneg hZ
    exact_mod_cast firstCommonSubsetNorm_pos l.1.1 l.1.2 hC l.2.val
  have hrest:0≤stratumWidth Z l.1.1 l.1.2 2 2+labelE l Z+lowSecondPenalty second C D U Z :=
    add_nonneg (add_nonneg (stratumWidth_nonneg Z hZ _ _ _ _) he) hsecond
  have hp:=actual_erasure_three_branch_payment a g q B lam h F t b c
    (max (labelD reflected l Z-labelC reflected l Z) 0) f
    (lowTypePenalty reflected l Z)
    (stratumWidth Z l.1.1 l.1.2 2 2+labelE l Z+lowSecondPenalty second C D U Z)
    loss rho mesh erased hq hB0 hB hlam hcc hd0 (hdc.trans hc) hpen hdpen hrest hf hh hqh hgap hcap hloss hrho herased
  have hi:=actual_low_coordinate_identity reflected second l hC hD heq hbC hbD C D U Z M A a ξ reserve err errv hZ
  change x 0+x 1+x 2-_-_=_ at hi
  change radial≤x 2+radialRound at hrad
  linarith only [hp,hi,hrad]

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.low_first_deficit_gates
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_low_coordinate_payment
