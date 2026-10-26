import Candidate.Target836.SourceProvider.ActualValuation
import Candidate.Target836.SourceProvider.ScalarValuation
import Candidate.Cycle63.Physical.InitialMass.MarkedHighCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSectorLocalization CenteredMomentRankinRadical Cycle63FinalCapacity
open CenteredMomentSecondCanonicalNonunit CenteredMomentCommonHarmonicMass
local notation "O" => HeckeFamily.O

def commonRate (rho delta : ℝ) : ℝ :=
  delta-max (4*rho-1) ((2+22*rho)/21)

/-- A parameter-free physical HIGH allocation estimate. The numerator facet
and both original radical gates remain explicit. -/
theorem high_valuation_saving (rho delta M A a c d p R E Bc Lc R0 b2 g2 t2 : ℝ)
    (hrho : 1/4 ≤ rho) (hrhohi : rho ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR0 : 0 ≤ R0) (hLc : Lc ≤ 5*(R-R0))
    (hnorm : 4*Lc ≤ 5*(c+d)) (hBc : max (3*c-5*d-R) 0/6 ≤ Bc)
    (hE : 0 ≤ E) (ht2 : 0 ≤ t2) (hg2 : g2 ≤ b2) :
    M*(rho-1)+delta*A+a*(5-6*rho)+(1-rho)*max (c-d) 0-delta*c-
      (1+rho)*R-E-Bc+rho*Lc+R0+g2-t2-(1+delta)*b2 ≤
      M*(rho-1)+delta*A+a*(5-6*rho)-commonRate rho delta*c-delta*b2 := by
  have hh := ValuationGain.first_common_symmetric rho delta c d p R E Lc R0
    hrho hrhohi hp hpC hpD hRp hR0 hLc hnorm
  unfold ValuationGain.firstCommon commonRate at *
  linarith

/-- The new facet and original gates are supplied by the actual canonical
source label in either reflection orientation; no synthetic source norm is
substituted for the uncancelled numerator. -/
theorem actual_high_joint_valuation_saving (reflected left second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2 = primeSupport D2)
    (U : Finset (CommonIndex C2 D2)) (Z delta M A a : ℝ) (hZ : 1 < Z)
    (hrho : 1/4 ≤ LocalMoment.unmarkedDensity delta)
    (hrhohi : LocalMoment.unmarkedDensity delta ≤ 2/5) :
    let rho := LocalMoment.unmarkedDensity delta
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm : ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm : ℝ)
    let R0 := Real.logb Z ((cancelledRadical left l.1.1 l.1.2).absNorm : ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm : ℝ)
    let b2 := Real.logb Z ((if second then D2 else C2).absNorm : ℝ)
    let g2 := Real.logb Z (normValue (commonFrequencyGenerator C2 D2))
    let t2 := Real.logb Z ((∏ P ∈ U, P.val).absNorm : ℝ)
    Cycle63.Physical.highJointExcess M A a delta c d p R E
      (max (3*c-5*d-R) 0/6) Lc R0 b2 g2 t2 ≤
      M*(rho-1)+delta*A+a*(5-6*rho)-commonRate rho delta*c-delta*b2 := by
  dsimp only
  obtain ⟨hp,hE,hR0,hpc,hpd,hRp,hLc⟩ := actual_first_gates left l hC hD Z hZ
  have hnorm := FirstNumeratorValuation.actual_firstSourceNumerator_log_bound
    left l hC hD.1 Z hZ
  have hg2 : Real.logb Z (normValue (commonFrequencyGenerator C2 D2)) ≤
      Real.logb Z ((if second then D2 else C2).absNorm : ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (commonFrequencyGenerator_ne_zero C2 D2 hC2))
    cases second
    · exact actual_common_norm_le C2 D2 hC2 hD2 heq2
    · exact actual_common_norm_le_right C2 D2 hC2 hD2 heq2
  have ht2 := actual_unit_log_nonneg C2 D2 hC2 U Z hZ
  unfold Cycle63.Physical.highJointExcess
  cases reflected
  · exact high_valuation_saving _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrho hrhohi
      hp hpc hpd hRp hR0 hLc hnorm le_rfl hE ht2 hg2
  · simp only [Bool.true_eq, ite_true, ite_false]
    apply high_valuation_saving _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrho hrhohi
      hp hpd hpc hRp hR0 hLc _ le_rfl hE ht2 hg2
    linarith

/-- Generic conserved-width payment. Every actual frequency and width is
retained; the source designer supplies only the three scalar endpoint caps. -/
theorem marked_width_payment (gamma delta rate tau q0 supplied removed frozen live freq saving : ℝ)
    (hgamma : 0 ≤ gamma) (hdelta : gamma ≤ delta) (hrate : 0 ≤ rate)
    (htau : 0 ≤ tau) (hremoved : 0 ≤ removed) (hfrozen : 0 ≤ frozen)
    (hlive : 0 ≤ live) (hsupply : supplied ≤ removed+frozen+live)
    (hfrequency : q0-2*removed ≤ freq)
    (hslope : 2*rate*tau ≤ gamma)
    (hcommon : saving ≤ gamma*supplied) (hmarked : saving ≤ rate*supplied)
    (hcapped : saving ≤ rate*tau*q0) :
    saving ≤ gamma*removed+delta*frozen+rate*min live (tau*freq) := by
  have hf := mul_le_mul_of_nonneg_right hdelta hfrozen
  by_cases hsmall : live ≤ tau*freq
  · rw [min_eq_left hsmall]
    by_cases hgr : gamma ≤ rate
    · nlinarith [mul_le_mul_of_nonneg_left hsupply hgamma,
        mul_nonneg (sub_nonneg.mpr hgr) hlive]
    · have hrg : rate ≤ gamma := le_of_not_ge hgr
      have hrd : rate ≤ delta := hrg.trans hdelta
      nlinarith [mul_le_mul_of_nonneg_left hsupply hrate,
        mul_nonneg (sub_nonneg.mpr hrg) hremoved,
        mul_nonneg (sub_nonneg.mpr hrd) hfrozen]
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hfreq := mul_le_mul_of_nonneg_left hfrequency (mul_nonneg hrate htau)
    nlinarith [mul_nonneg (sub_nonneg.mpr hslope) hremoved,
      mul_nonneg (hgamma.trans hdelta) hfrozen]

/-- The large sixth-power tail uses the same paid frequency lower bound. -/
theorem tail_width_payment (gamma delta tail q0 removed frozen freq saving : ℝ)
    (hdelta : 0 ≤ delta) (htail : 0 ≤ tail)
    (hremoved : 0 ≤ removed) (hfrozen : 0 ≤ frozen)
    (hfrequency : q0-2*removed ≤ freq) (hslope : 2*tail ≤ gamma)
    (hcap : saving ≤ tail*q0) :
    saving ≤ gamma*removed+delta*frozen+tail*freq := by
  have hfreq := mul_le_mul_of_nonneg_left hfrequency htail
  nlinarith [mul_nonneg (sub_nonneg.mpr hslope) hremoved,
    mul_nonneg hdelta hfrozen]

/-- Lowering the incumbent capacity changes its removal price as well.
The formula retains both terms and exposes the exact positive reserve. -/
theorem low_payment_identity (k q defect alpha : ℝ) (hk : k ≠ 0) (hkq : k-q ≠ 0) :
    let amp := q/(6*(k-q))*defect+alpha
    amp-(q/(6*k))*(defect+6*amp) = alpha*(1-q/k) := by
  dsimp only
  field_simp
  <;> ring

end
end Target874836.SourceProvider

#print axioms Target874836.SourceProvider.high_valuation_saving
#print axioms Target874836.SourceProvider.actual_high_joint_valuation_saving
#print axioms Target874836.SourceProvider.marked_width_payment
#print axioms Target874836.SourceProvider.tail_width_payment
#print axioms Target874836.SourceProvider.low_payment_identity
