import Candidate.Target836.SourceProvider.HighCoordinates
import Candidate.Cycle63.Physical.InitialMass.GeometryHighShell
import Candidate.Cycle63.Physical.InitialMass.SecondHighBox
import Candidate.Cycle63.Physical.InitialMass.SecondChildHighPayment
import Candidate.Cycle63.Physical.InitialMass.SecondFrequencyBudget

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.TargetHigh836
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Fixed geometric support supplies the arithmetic gates for both signs.
The remaining hypotheses are scalar caps, not analytic density estimates. -/
theorem actual_geometry_high_coordinate_gates {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α)(Rseed seed : Ideal O)(K Z ξ : ℝ)(hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : FirstColumnIndex (geometryFirstSource s Rseed seed K Z ξ hK bin))
    (d₂ : SecondInputDatum α)(reflected left second : Bool)
    (U : Finset (CommonIndex d₂.C d₂.D))
    (M A a reserve ε εv B b δ : ℝ)(hZ : 1<Z)(hB : 0 ≤ B)
    (hfirst : ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.1.absNorm:ℝ) ≤ Z^B ∧
      ((geometryFirstLabel s Rseed seed K Z ξ hK bin column).1.2.absNorm:ℝ) ≤ Z^B)
    (hsecond : (d₂.C.absNorm:ℝ) ≤ Z^B ∧ (d₂.D.absNorm:ℝ) ≤ Z^B)
    (hMbox : |M| ≤ B)(hAbox : |A| ≤ B)(habox : |a| ≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve| ≤ B)(hε : |ε| ≤ B)
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25)
    (hδ : Named.q ≤ δ ∧ δ ≤ 3/4)(hM : 0 ≤ M)
    (hA : A ≤ M*Named.total b)(ha : a ≤ M*Named.amp b) :
    let l:=geometryFirstLabel s Rseed seed K Z ξ hK bin column
    let x:=childHighCoordinates (actualHighCoordinates reflected left second l d₂.C d₂.D U
      Z M A a ξ reserve ε) εv
    let c:=Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d:=Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E:=Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p:=Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    ((firstSourceMissing left l).absNorm:ℝ)=Z^(x 1) ∧
      (∀j,-(32*B+|εv|) ≤ x j ∧ x j ≤ 32*B+|εv|) ∧
      highExponentValue δ x ≤ p+A-c+R+E+max (3*c-5*d-R) 0/6-
        M*Named.high b δ-Named.gamma δ*(c+Real.logb Z ((if second then d₂.D else d₂.C).absNorm:ℝ))+(1-unmarkedDensity δ)*(frequencyLoss Z 32 ξ+reserve)+
          unmarkedDensity δ*ε+εv := by
  intro l x c d R E p
  have hC : Supported l.1.1 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s Rseed seed K Z ξ hK bin column.1).sameSupport
  refine ⟨actual_child_high_missing reflected left second l hC hD d₂.C d₂.D U
    Z M A a ξ reserve ε εv hZ,?_,?_⟩
  · exact child_high_coordinate_box _ (32*B) εv
      (actual_high_coordinate_box reflected left second l hC hD d₂.C d₂.D d₂.hC d₂.hD
        d₂.sameSupport U Z M A a ξ reserve ε B hZ hB hfirst hsecond hMbox hAbox habox hω hε)
  · have hh:=Target874836.SourceProvider.actual_high_coordinate_valuation_payment reflected left second l hC hD heq
      d₂.C d₂.D d₂.hC d₂.hD d₂.sameSupport U Z b δ M A a ξ reserve ε hZ hb hδ hM hA ha
    rw [child_high_exponent_value]
    exact add_le_add hh (le_refl εv)


end
end OAI.SevenEighths.TargetHigh836
#print axioms OAI.SevenEighths.TargetHigh836.actual_geometry_high_coordinate_gates
