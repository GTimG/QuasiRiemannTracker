/- Copyright (c) 2026 Hailey Collet; source-price binding (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.LowChildFactsRow
import Candidate.Cycle63.Physical.InitialMass.LowChildSideExponent

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open Cycle63FinalCapacity Cycle63Moment Cycle63InitialMass

/-- Retain the literal physical row scale at EVERY recursive stage.
In particular there is no replacement by unit one and no extra positive
part of 1-Mrow. The native common saving and all four coordinates stay
in the inequality. -/
theorem actual_raw_row_payment
    (reflected second : Bool) (l : FirstSourceLabel) (hC : Supported l.1.1)
    (hD : Supported l.1.2) (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (inactive : Finset (CommonIndex C2 D2))
    (Z delta Mrow A amp xi reserve eps : ℝ) (hZ : 1<Z)
    (hdelta : Cycle63.Arithmetic.q0 ≤ delta ∧ delta ≤ 3/4) :
    let rho := LocalMoment.unmarkedDensity delta
    let gamma := ValuationCone.commonRate delta *
      (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
        Real.logb Z ((if second then D2 else C2).absNorm:ℝ))
    highExponentValue delta (actualHighCoordinates reflected (!reflected) second l C2 D2 inactive
      Z Mrow A amp xi reserve eps) ≤
      lowLabelSide reflected Z A l-
        (Mrow*(1-rho)-delta*A-amp*(5-6*rho))-gamma+
        (1-rho)*(frequencyLoss Z 32 xi+reserve)+rho*eps := by
  simpa only [lowLabelSide,lowConeSurplus] using
    actual_high_coordinate_allocation_payment_reserve_E reflected second l hC hD heq
      C2 D2 hC2 hD2 heq2 inactive Z delta Mrow A amp xi reserve eps hZ hdelta

/-- The ACTUAL first geometry bin chooses a lower side and upper label
exponent whose difference is six binary widths. Consequently the native
first-mass loss `massError-sideLower` cancels the leading label side.
This licenses the cancellation of E0's mass-dyad loss in the recursive
price; it is not an assumption that every source fee is small. -/
theorem actual_first_bin_side_cancellation
    {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (s : Input alpha) (R seed : Ideal O) (K Z xi B A : ℝ) (hK : 0<K)
    (hZ : 1<Z) (hseed : Squarefree seed) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (hsource : sourceRadius s ≤ Z^B) (key : ℤ×(Fin 5→ℤ)) (reflected : Bool) :
    ∃ exponent sideLower : ℝ,
      ((key.2 2:ℝ)+1)*Real.logb Z 2+exponent-sideLower=6*Real.logb Z 2 ∧
      ∀j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK key),
        let first := geometryFirstLabel s R seed K Z xi hK key j
        ((commonRadical first.1.1 first.1.2).absNorm:ℝ) ≤
          Z^(((key.2 2:ℝ)+1)*Real.logb Z 2) ∧
        lowSideExponent reflected Z A first ≤ exponent ∧
        sideLower ≤ geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val) ∧
        ∀ massError : ℝ,
          (massError-sideLower)+lowLabelSide reflected Z A first ≤ massError+6*Real.logb Z 2 := by
  obtain ⟨exponent,sideLower,hledger,hgate⟩ := actual_geometry_low_bin_gate_side
    s R seed K Z xi B A hK hZ hseed hz1 hz2 hsource key reflected
  refine ⟨exponent,sideLower,hledger,?_⟩
  intro j first
  obtain ⟨hrad,hgeom,hside⟩ := hgate j
  have hC : Supported first.1.1 := (geometryFirstSource s R seed K Z xi hK key j.1).hC
  have hlabel := lowLabelSide_le reflected Z A
    (((key.2 2:ℝ)+1)*Real.logb Z 2) exponent first hZ hrad hgeom 1 one_ne_zero (one_dvd _) hC
  simp only [map_one,Nat.cast_one,Real.logb_one,sub_zero] at hlabel
  refine ⟨hrad,hgeom,hside,?_⟩
  intro massError
  linarith only [hledger,hlabel]

/-- A source-side budget cancels the mass dyad before the physical path
payment is iterated. The reserve remains at the literal Mrow, and X1's
historical missing radical retains coefficient one in highExponentValue. -/
theorem actual_shifted_raw_row_payment
    (reflected second : Bool) (l : FirstSourceLabel) (hC : Supported l.1.1)
    (hD : Supported l.1.2) (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (inactive : Finset (CommonIndex C2 D2))
    (Z delta Mrow A amp xi reserve eps loss sideError : ℝ) (hZ : 1<Z)
    (hdelta : Cycle63.Arithmetic.q0 ≤ delta ∧ delta ≤ 3/4)
    (hside : loss+lowLabelSide reflected Z A l ≤ sideError) :
    let rho := LocalMoment.unmarkedDensity delta
    let gamma := ValuationCone.commonRate delta *
      (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
        Real.logb Z ((if second then D2 else C2).absNorm:ℝ))
    loss+highExponentValue delta (actualHighCoordinates reflected (!reflected) second l C2 D2 inactive
      Z Mrow A amp xi reserve eps) ≤
      sideError-(Mrow*(1-rho)-delta*A-amp*(5-6*rho))-gamma+
        (1-rho)*(frequencyLoss Z 32 xi+reserve)+rho*eps := by
  have h := actual_raw_row_payment reflected second l hC hD heq C2 D2 hC2 hD2 heq2
    inactive Z delta Mrow A amp xi reserve eps hZ hdelta
  dsimp only at h ⊢
  linarith only [h,hside]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_raw_row_payment
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_first_bin_side_cancellation
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_shifted_raw_row_payment
