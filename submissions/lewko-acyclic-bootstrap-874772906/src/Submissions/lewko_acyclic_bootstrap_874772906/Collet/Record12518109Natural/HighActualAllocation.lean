/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighAllocation

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace OAI.SevenEighths.Record12518109Natural
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry Cycle61InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle61FinalCapacity
local notation "O" => HeckeFamily.O

theorem actual_label_common (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z delta : ℝ) (hZ : 1<Z) (hdelta : 31/50≤delta) (hdelta' : delta≤3/4) :
    labelFirstCommon reflected l Z delta-labelSurplus reflected l Z≤
      -Valuation.commonGamma delta*labelC reflected l Z := by
  simpa [labelFirstCommon,labelSurplus,labelC,labelD,labelR,labelE,labelP,
    Valuation.surplus] using
    Valuation.actual_first_common_gamma reflected l hC hD heq Z delta hZ hdelta hdelta'

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_balanced_common_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv delta : ℝ) (hZ : 1<Z)
    (hdelta : 31/50≤delta) (hdelta' : delta≤3/4) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv) side
    highExponentValue delta x≤
      (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv-
        (D*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        Valuation.commonGamma delta*labelC reflected l Z-delta*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
  have hC := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have heq := (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport
  have hc := actual_label_common reflected (geometryFirstLabel s R seed K Z xi hK bin j)
    hC hD heq Z delta hZ hdelta hdelta'
  exact actual_geometry_balanced_high_payment s R seed K Z xi hK bin j d2 reflected second U
    D A a reserve err errv delta (Valuation.commonGamma delta) hZ hc

end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_label_common
#print axioms OAI.SevenEighths.Record12518109Natural.actual_geometry_balanced_common_payment
