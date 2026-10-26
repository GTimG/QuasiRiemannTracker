/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed coordinate box for actual selected cofactors, including all forced
and singleton losses. Only original polynomial geometry enters. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalPaidSome
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentAddedZeroUniform
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonProfile CenteredMomentSecondHeightFamily
open Cycle61Moment Cycle61InitialMass Record12518109Natural.MarkedPlain
open CenteredMomentAmplificationChildSourceCaps CenteredMomentSectorLocalization
open Admission.SelectedHighCofactorFamily Admission.SelectedHighCofactorCoordinates HighScalar
local notation "O"=>HeckeFamily.O
local instance cofactorBoxDecidable {α:Type*}:DecidableEq α:=Classical.decEq _

theorem lost_width_coordinate_box (x:Fin 4→ℝ)(B loss L:ℝ)
    (h:∀i,-B≤x i ∧ x i≤B)(hl:|loss|≤L) :
    ∀i,-(B+L)≤lostWidthCoordinates x loss i ∧ lostWidthCoordinates x loss i≤B+L := by
  have hl0:0≤L:=(abs_nonneg _).trans hl
  have ha:=abs_le.mp hl
  intro i
  have hi:=h i
  fin_cases i <;> dsimp [lostWidthCoordinates] at hi ⊢ <;> constructor <;> linarith

/-- All complete child pools are retained. The singleton subset only affects
coordinate three; its width is bounded by the original width without counting it. -/
theorem selected_cofactor_coordinate_box {α:Type}[Fintype α]
    (s:Input α)(reflected second:Bool)(l:FirstSourceLabel)(C₂ D₂ R:Ideal O)
    (sel:Selection s reflected second l C₂ D₂ R)(U:Finset (CommonIndex C₂ D₂))
    (Z M amp ξ reserve err errv annular wmin B Bforced b Acap:ℝ)(w:α→ℝ)(T:Finset α)
    (hZ:1<Z)(hB:0≤B)(hC:Supported l.1.1)(hD:Supported l.1.2)
    (hC₂:Supported C₂)(hD₂:Supported D₂)(heq:primeSupport C₂=primeSupport D₂)
    (hfirst:(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B)
    (hsecond:(C₂.absNorm:ℝ)≤Z^B ∧ (D₂.absNorm:ℝ)≤Z^B)
    (hM:|M|≤B)(hA:|Real.logb Z (volume s)|≤B)(ha:|amp|≤B)
    (homega:|frequencyLoss Z 32 ξ+reserve|≤B)(herr:|err|≤B)
    (hforced:(sel.Cf.absNorm:ℝ)≤Z^Bforced)(hw:∀i,0≤w i)(hwidth:(∑i,w i)≤b)
    (hann0:0≤annular)(hann:annular≤Acap) :
    ∀i,-(32*B+|errv|+Bforced+2*b+Acap)≤sel.coordinate U Z M amp ξ reserve err errv annular w wmin T i ∧
      sel.coordinate U Z M amp ξ reserve err errv annular w wmin T i≤32*B+|errv|+Bforced+2*b+Acap := by
  have hx:=child_high_coordinate_box _ (32*B) errv
    (actual_high_coordinate_box reflected (!reflected) second l hC hD C₂ D₂ hC₂ hD₂ heq U
      Z M (Real.logb Z (volume s)) amp ξ reserve err B hZ hB hfirst hsecond hM hA ha homega herr)
  have hf:=ideal_log_box sel.Cf (allocation_ne _ _ sel.Bf) Z Bforced hZ hforced
  have hs (S:Finset α):0≤∑i∈S,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hs' (S:Finset α):(∑i∈S,w i)≤b:=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _=>hw i)).trans hwidth
  have hsmall:=hs (largeSlots T w wmin)
  have hsmall':=hs' (largeSlots T w wmin)
  have hlive:=hs (largeSlots sel.full w wmin)
  have hlive':=hs' (largeSlots sel.full w wmin)
  have hl:|sel.forced Z+sel.live w wmin-(∑i∈largeSlots T w wmin,w i)-annular|≤Bforced+2*b+Acap:=by
    dsimp only [Selection.forced,Selection.live]
    apply abs_le.mpr
    constructor <;> linarith [hf.1,hf.2]
  have hb:=lost_width_coordinate_box _ (32*B+|errv|) _ (Bforced+2*b+Acap) hx hl
  intro i
  simpa only [Selection.coordinate,cofactorCoordinates,add_assoc] using hb i
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.lost_width_coordinate_box
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_cofactor_coordinate_box
