import Candidate.Target830.High.Allocation

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
local notation "O" => HeckeFamily.O

/-- No fixed historical omega allowance is inserted into the live-frequency
ledger. The actual amplifier and chosen positive allowance remain explicit. -/
theorem raw_frequency_moving (M c d b2 a R Lc omega err raw amp omegaCap : ℝ)
    (hc : 0≤c) (hd : 0≤d) (hb2 : 0≤b2) (hR : R≤c) (hLc : 0≤Lc)
    (ha : a≤M*amp) (hOmega : omega≤M*omegaCap) (herr : 0≤err)
    (hraw : raw=M-R-max (c-d) 0+Lc-6*a-omega+err) :
    M*(1-6*amp-omegaCap)-2*(c+b2)≤raw := by
  have hm : max (c-d) 0≤c := max_le (by linarith) hc
  nlinarith

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Actual balanced two-allocation coordinates retain the moving volume
and full compensated frequency before any scalar source certificate. -/
theorem actual_geometry_balanced_moving_frequency
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv amp omegaCap core : ℝ) (hZ : 1<Z)
    (ha : a≤D*amp) (hOmega : frequencyLoss Z 32 xi+reserve≤D*omegaCap)
    (herr : 0≤err) (hcore : 0≤core) (hcore' : core≤1) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv) side
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    0≤c ∧ 0≤b2 ∧ x 3=A-(c+b2) ∧
      core*D*(1-6*amp-omegaCap)-2*(c+b2)≤core*x 2 := by
  intro l side x c b2
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have hc : 0≤c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hd : 0≤labelD reflected l Z := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.2 hD.1
    · exact norm_ge_one l.1.1 hC.1
  have hb2 : 0≤b2 := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d2.C d2.hC.1
    · exact norm_ge_one d2.D d2.hD.1
  have hg := Cycle63HighGeometry.actual_first_gates (!reflected) l hC hD Z hZ
  have hR : labelR l Z≤c := by
    cases reflected
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.1
    · exact hg.2.2.2.2.2.1.trans hg.2.2.2.2.1
  have hLc : 0≤Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ) :=
    Real.logb_nonneg hZ (normValue_ge_one _ (first_source_numerator_ne_zero (!reflected) l hC))
  refine ⟨hc,hb2,?_,?_⟩
  · dsimp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c,b2,labelC]
    ring
  · have hraw := raw_frequency_moving D c (labelD reflected l Z) b2 a (labelR l Z)
      (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
      (frequencyLoss Z 32 xi+reserve) err (x 2) amp omegaCap hc hd hb2 hR hLc ha hOmega herr
      (by simp [x,compensatedHighCoordinates,childHighCoordinates,actualHighCoordinates,c,labelC,labelD,labelR])
    have hm := mul_le_mul_of_nonneg_left hraw hcore
    have hs := mul_nonneg (by linarith : 0≤1-core) (add_nonneg hc hb2)
    nlinarith only [hm,hs]

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.raw_frequency_moving
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_balanced_moving_frequency
