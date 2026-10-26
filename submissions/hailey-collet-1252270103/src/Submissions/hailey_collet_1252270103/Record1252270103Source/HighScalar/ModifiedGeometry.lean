/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Four-type and balanced-side bindings for the actual modified first source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalGeometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FirstFamilyLabels
import Submissions.hailey_collet_1252270103.Record1252270103Source.HighScalar.FirstCommon
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.HighScalar
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge
open Record12518109Natural Record1252270103CommonGeometry Cycle61HighGeometry Cycle61InitialMass
open CenteredMomentCommonRadialData CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceMass
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical
open CenteredMomentRankinRadical Cycle61Moment CenteredMomentSourceLiveColumn
open Record1252270103Source.Collision Admission
local notation "O" => HeckeFamily.O
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Membership in the actual common-label image supplies two nonzero modified
columns. No nonzero claim about an ordinary column is made. -/
theorem modified_coordinate_valuations (s : Input ι) (A₁ A₂ D K R seed : Ideal O)
    (F : Ideal O→ℂ) (H Z ξ : ℝ)
    (q : High.CoupledFirst.SourceCoordinate s (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ) :
    ValuationAtMostTwo q.1.val.1 ∧ValuationAtMostTwo q.1.val.2 := by
  obtain ⟨⟨I,J⟩,hp,he⟩:=Finset.mem_image.mp q.1.property
  obtain ⟨hI,hJ⟩:=Finset.mem_product.mp hp
  obtain ⟨hI,hIs⟩:=Finset.mem_filter.mp hI
  obtain ⟨hJ,hJs⟩:=Finset.mem_filter.mp hJ
  have hi:= (mem_activeSource _ _ _).mp hI
  have hj:= (mem_activeSource _ _ _).mp hJ
  have hv:=High.GlobalPhysical.marked_common_valuations s A₁ A₂ D K R seed I J F hIs hJs hi.2 hj.2
  obtain ⟨hc,hd⟩:=Prod.mk.inj he
  simpa only [hc,hd] using hv

theorem modified_first_label_valuations (s : Input ι) (A₁ A₂ D K R seed : Ideal O)
    (F : Ideal O→ℂ) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s
      (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ hH key)) :
    let l:=FirstFamily.firstLabel s (markedSourceModifier A₁ A₂ D K F) R seed H Z ξ hH key j
    ValuationAtMostTwo l.1.1 ∧ValuationAtMostTwo l.1.2 :=
  modified_coordinate_valuations s A₁ A₂ D K R seed F H Z ξ j.1.val

lemma modified_geometry_surplus (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed H Z ξ hH key))
    (reflected : Bool) :
    labelSurplus reflected (FirstFamily.firstLabel s modifier R seed H Z ξ hH key j) Z=
      QRH.Record12518109Assembly.surplus
        (High.CoupledFirst.geometryExponents s modifier R seed H Z ξ j.1.val) := by
  cases reflected <;>
    dsimp [labelSurplus,labelC,labelD,labelR,labelP,QRH.Record12518109Assembly.surplus,
      QRH.Record12518109Assembly.Scalar.surplus,QRH.Record12518109Assembly.Scalar.side,
      High.CoupledFirst.geometryExponents,High.CoupledFirst.geometryNorms,
      High.CoupledFirst.geometryIdeals,FirstFamily.firstLabel] <;> ring

theorem modified_balanced_side (s : Input ι) (modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
    (R seed : Ideal O) (H Z ξ : ℝ) (hH : 0<H) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed H Z ξ hH key))
    (reflected : Bool) (A : ℝ) :
    let l:=FirstFamily.firstLabel s modifier R seed H Z ξ hH key j
    balancedGeometrySide reflected A (High.CoupledFirst.geometryExponents s modifier R seed H Z ξ j.1.val)=
      labelSide reflected l Z A+labelSurplus reflected l Z := by
  intro l
  have hs:=modified_geometry_surplus s modifier R seed H Z ξ hH key j reflected
  change labelSurplus reflected l Z=_ at hs
  rw [hs]
  have he : Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}=
      firstProjectorRadical l.1.1 l.1.2 l.2.val := by
    rw [primeSubsetGenerator,span_idealGenerator]
    rfl
  change Ideal.span {primeSubsetGenerator
    (fun P : CommonIndex j.1.val.1.val.1 j.1.val.1.val.2=>P.val) j.1.val.2.1.val}=_ at he
  cases reflected <;>
    simp only [balancedGeometrySide,Bool.false_eq_true,ite_false,ite_true,
      QRH.Record12518109Assembly.left_eq_old,QRH.Record12518109Assembly.right_eq_old]
  all_goals
    dsimp [labelSide,labelP,labelC,labelD,labelR,labelE,l,FirstFamily.firstLabel,
      High.CoupledFirst.geometryExponents,High.CoupledFirst.geometryNorms,
      High.CoupledFirst.geometryIdeals,Cycle61InitialMass.leftExponent,Cycle61InitialMass.rightExponent]
    rw [he]
    rfl

end
end QRH.Record1252270103Source.HighScalar
#print axioms QRH.Record1252270103Source.HighScalar.modified_coordinate_valuations
#print axioms QRH.Record1252270103Source.HighScalar.modified_first_label_valuations
#print axioms QRH.Record1252270103Source.HighScalar.modified_balanced_side
