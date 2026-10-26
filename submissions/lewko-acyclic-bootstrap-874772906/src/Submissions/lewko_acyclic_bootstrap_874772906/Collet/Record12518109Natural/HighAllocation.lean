/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.GeometryHighPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighFrequency
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.Valuation
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Assembly.BalancedPayment

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
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

def highJointExcess (M A a delta c d p R E Bc Lc R0 b2 g2 t2 : ℝ) : ℝ :=
  M*(unmarkedDensity delta-1)+delta*A+a*(5-6*unmarkedDensity delta)+
    (1-unmarkedDensity delta)*max (c-d) 0-delta*c-(1+unmarkedDensity delta)*R-E-Bc+
    unmarkedDensity delta*Lc+R0+g2-t2-(1+delta)*b2

def labelE (l : FirstSourceLabel) (Z : ℝ) : ℝ :=
  Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
def labelP (l : FirstSourceLabel) (Z : ℝ) : ℝ :=
  Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
def labelSurplus (reflected : Bool) (l : FirstSourceLabel) (Z : ℝ) : ℝ :=
  (labelC reflected l Z+labelD reflected l Z-labelR l Z-2*labelP l Z-
    max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6-
    max (3*labelD reflected l Z-5*labelC reflected l Z-labelR l Z) 0/6)/2

def labelFirstCommon (reflected : Bool) (l : FirstSourceLabel) (Z delta : ℝ) : ℝ :=
  Valuation.firstCommon (unmarkedDensity delta) delta
    (labelC reflected l Z) (labelD reflected l Z) (labelR l Z) (labelE l Z)
    (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
    (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))

def labelSide (reflected : Bool) (l : FirstSourceLabel) (Z A : ℝ) : ℝ :=
  labelP l Z+A-labelC reflected l Z+labelR l Z+labelE l Z+
    max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6

def balancedGeometrySide (reflected : Bool) (A : ℝ) (v : Fin 5→ℝ) : ℝ :=
  if reflected then QRH.Record12518109Assembly.balancedRight A v else QRH.Record12518109Assembly.balancedLeft A v

theorem actual_high_coordinate_excess_identity (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z δ M A a ξ reserve ε : ℝ)
    (hZ : 1<Z) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    highExponentValue δ (actualHighCoordinates reflected left second l C₂ D₂ U Z M A a ξ reserve ε)=
      S+(1-ρ)*ω+ρ*ε+highJointExcess M A a δ c d p R E
        (max (3*c-5*d-R) 0/6) Lc
        (Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm:ℝ)) b₂
        (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  dsimp only
  dsimp [highExponentValue,actualHighCoordinates,highJointExcess]
  rw [actual_missing_log left l hC Z]
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)];ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))];ring
  linear_combination hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))


/-- The first allocation cone is explicit; the second allocation contributes
its genuine removed width and nonnegative selected-projector cost. -/
theorem actual_high_joint_balanced_valuation (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a gamma : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z≤
      -gamma*labelC reflected l Z) :
    highJointExcess M A a delta
      (labelC reflected l Z) (labelD reflected l Z) (labelP l Z) (labelR l Z) (labelE l Z)
      (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
      (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
      (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
      (Real.logb Z ((if second then D2 else C2).absNorm:ℝ))
      (Real.logb Z (normValue (commonFrequencyGenerator C2 D2)))
      (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ))-labelSurplus reflected l Z≤
      M*(unmarkedDensity delta-1)+delta*A+a*(5-6*unmarkedDensity delta)-
        gamma*labelC reflected l Z-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hg2 : Real.logb Z (normValue (commonFrequencyGenerator C2 D2))≤
      Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (commonFrequencyGenerator_ne_zero C2 D2 hC2))
    cases second
    · exact actual_common_norm_le C2 D2 hC2 hD2 heq2
    · exact actual_common_norm_le_right C2 D2 hC2 hD2 heq2
  have ht2 := Cycle61FinalCapacity.actual_unit_log_nonneg C2 D2 hC2 U Z hZ
  dsimp [highJointExcess,labelFirstCommon,Valuation.firstCommon] at *
  linarith

/-- Literal first-label and second-child coordinates, with physical orientation
left=!reflected throughout. No historical rho<=.4 estimate is used. -/
theorem actual_high_coordinate_balanced_payment (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a xi reserve err gamma : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z≤
      -gamma*labelC reflected l Z) :
    highExponentValue delta
      (actualHighCoordinates reflected (!reflected) second l C2 D2 U Z M A a xi reserve err)≤
      labelSide reflected l Z A+labelSurplus reflected l Z+
        (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err-
        (M*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        gamma*labelC reflected l Z-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hid := actual_high_coordinate_excess_identity
    reflected (!reflected) second l hC hD heq C2 D2 hC2 hD2 heq2 U Z delta M A a xi reserve err hZ
  have hh := actual_high_joint_balanced_valuation reflected second l hC hD C2 D2 hC2 hD2 heq2
    U Z delta M A a gamma hZ hfirst
  dsimp only at hid
  dsimp [labelC,labelD,labelR,labelE,labelP,labelSide] at hh ⊢
  rw [hid]
  linarith

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem geometry_label_surplus_eq (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ)
    (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin)) (reflected : Bool) :
    labelSurplus reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z=
      QRH.Record12518109Assembly.surplus (geometryExponents s R seed K Z xi j.1.val) := by
  cases reflected <;>
    dsimp [labelSurplus,labelC,labelD,labelR,labelP,QRH.Record12518109Assembly.surplus,
      QRH.Record12518109Assembly.Scalar.surplus,QRH.Record12518109Assembly.Scalar.side,
      geometryExponents,geometryNorms,geometryIdeals,geometryFirstLabel] <;> ring

theorem balanced_geometry_side_eq (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ)
    (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin)) (reflected : Bool) (A : ℝ) :
    balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)=
      geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)+
        labelSurplus reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z := by
  rw [geometry_label_surplus_eq]
  cases reflected <;>
    simp [balancedGeometrySide,geometryHighSide,QRH.Record12518109Assembly.left_eq_old,QRH.Record12518109Assembly.right_eq_old]

/-- Actual compensated HIGH coordinates after the column surplus is retained.
The actual oriented first-common cone remains the single explicit argument. -/
theorem actual_geometry_balanced_high_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv delta gamma : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z delta-
      labelSurplus reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z≤
      -gamma*labelC reflected (geometryFirstLabel s R seed K Z xi hK bin j) Z) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv) side
    highExponentValue delta x≤
      (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv-
        (D*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        gamma*labelC reflected l Z-delta*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport
  have hh := actual_high_coordinate_balanced_payment reflected second l hC hD heq
    d2.C d2.D d2.hC d2.hD d2.sameSupport U Z delta D A a xi reserve err gamma hZ hfirst
  have he := actual_geometry_high_side_identity s R seed K Z xi hK bin j reflected A
  have hside := balanced_geometry_side_eq s R seed K Z xi hK bin j reflected A
  change side=geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)+
    labelSurplus reflected l Z at hside
  change geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)=labelSide reflected l Z A at he
  rw [he] at hside
  rw [←hside] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  linarith only [hh]

end OAI.SevenEighths.Record12518109Natural
#print axioms OAI.SevenEighths.Record12518109Natural.actual_high_joint_balanced_valuation
#print axioms OAI.SevenEighths.Record12518109Natural.actual_high_coordinate_balanced_payment
#print axioms OAI.SevenEighths.Record12518109Natural.geometry_label_surplus_eq
#print axioms OAI.SevenEighths.Record12518109Natural.balanced_geometry_side_eq
#print axioms OAI.SevenEighths.Record12518109Natural.actual_geometry_balanced_high_payment
