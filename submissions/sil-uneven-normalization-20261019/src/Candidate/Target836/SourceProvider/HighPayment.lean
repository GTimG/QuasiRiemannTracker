import Mathlib.Tactic
import Candidate.Cycle63.Moment.CanonicalFirstNorm
import Candidate.Cycle63.Moment.FirstSourceCount
import Candidate.Cycle63.Physical.InitialMass.MarkedHighCoordinates

/- Original module: Candidate.Target836.SourceProvider.ScalarValuation. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
Scalar consequences of the exact directional common-prime valuation facets.

UNIMPLEMENTED HERE: transporting the actual ideal numerators to the hypotheses
`hdir`.  The proposed left/right ideal divisibilities are respectively
  numerator * activeRadical^2 * cancelledRadical^3 | C * D^2
and
  numerator * activeRadical^2 * cancelledRadical^3 | C^2 * D.
This file proves no new physical source theorem or fixed-strip endpoint.
-/

namespace ValuationGain
noncomputable section

def firstCommon (ρ δ c d R E Lc R₀ : ℝ) : ℝ :=
  (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
    max (3*c-5*d-R) 0/6+ρ*Lc+R₀

/-- On the `c ≥ d` branch either actual signed orientation has the same safe
rate.  The second directional facet is the extremal one on this branch. -/
theorem first_common_directional_hi (ρ δ c d R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5) (hcd : d ≤ c)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-(4+35*ρ)/36)*c-E := by
  have hnew : Lc ≤ 2*c+d-2*R-3*R₀ := by
    rcases hdir with hleft | hright
    · linarith
    · exact hright
  have hfac := mul_le_mul_of_nonneg_left hnew
    (show 0 ≤ 19*ρ-4 by linarith)
  have hcoarse := mul_le_mul_of_nonneg_left hLc
    (show 0 ≤ 17*ρ+4 by linarith)
  have hpen := mul_le_mul_of_nonneg_left
    (le_max_left (3*c-5*d-R) 0) (show 0 ≤ 8-11*ρ by linarith)
  have hpenExtra := mul_nonneg (show 0 ≤ 11*ρ-2 by linarith)
    (le_max_right (3*c-5*d-R) 0)
  have hcancel := mul_nonneg (show 0 ≤ 142*ρ-28 by linarith) hR₀
  unfold firstCommon
  rw [max_eq_left (sub_nonneg.mpr hcd)]
  nlinarith

/-- Exact scalar common-part improvement, keeping the natural inactive
projector loss `E`, the positive-part penalty, and cancelled radical `R₀`.
The piecewise rate is necessary: `δ+1-4ρ` alone fails near `δ=7/10`. -/
theorem first_common_exact (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-max (4*ρ-1) ((4+35*ρ)/36))*c-E := by
  have hc : 0 ≤ c := hp.trans hpC
  by_cases hcd : d ≤ c
  · have hh := first_common_directional_hi ρ δ c d R E Lc R₀
      hρ hρmax hcd hR₀ hLc hdir
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_right (4*ρ-1) ((4+35*ρ)/36)) hc
    nlinarith
  · have hnum := mul_le_mul_of_nonneg_left hLc (show 0 ≤ ρ by linarith)
    have hrad := mul_le_mul_of_nonneg_left (hRp.trans hpC)
      (show 0 ≤ 4*ρ-1 by linarith)
    have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
    have hpen := le_max_right (3*c-5*d-R) 0
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_left (4*ρ-1) ((4+35*ρ)/36)) hc
    unfold firstCommon
    rw [max_eq_right (show c-d ≤ 0 by linarith)]
    nlinarith

/-- Uniform scalar rate over the proposed `q = 27/40` source interval. -/
theorem first_common_uniform_27_40 (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 28/73) (hδ : 27/40 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hdir : Lc ≤ c+2*d-2*R-3*R₀ ∨ Lc ≤ 2*c+d-2*R-3*R₀) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(411/2920)*c-E := by
  have hh := first_common_exact ρ δ c d p R E Lc R₀ hρ (by linarith)
    hp hpC hpD hRp hR₀ hLc hdir
  have hmax : max (4*ρ-1) ((4+35*ρ)/36) ≤ 39/73 := by
    apply max_le <;> linarith
  have hgap := mul_nonneg
    (show 0 ≤ δ-max (4*ρ-1) ((4+35*ρ)/36)-411/2920 by linarith)
    (hp.trans hpC)
  nlinarith

/-- The symmetric norm facet combines with the cancelled-radical bound before
either signed orientation is discarded. -/
theorem symmetric_radical_facet (ρ c d R Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hnorm : 4*Lc ≤ 5*(c+d)) :
    21*ρ*Lc+21*R₀ ≤ (19*ρ-4)*(c+d)+(16+29*ρ)*R := by
  have hnorm' := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ 19*ρ-4 by linarith)
  have hrad := mul_le_mul_of_nonneg_left hLc
    (show 0 ≤ 16+29*ρ by linarith)
  have hcancel := mul_nonneg (show 0 ≤ 29*ρ-5 by linarith) hR₀
  nlinarith

theorem first_common_symmetric_hi (ρ δ c d R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5) (hcd : d ≤ c)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(δ-(2+22*ρ)/21)*c-E := by
  have hfacet := symmetric_radical_facet ρ c d R Lc R₀ hρ hR₀ hLc hnorm
  have hpen := mul_le_mul_of_nonneg_left
    (le_max_left (3*c-5*d-R) 0) (show 0 ≤ 5-8*ρ by linarith)
  have hpenExtra := mul_nonneg (show 0 ≤ 16*ρ-3 by linarith)
    (le_max_right (3*c-5*d-R) 0)
  unfold firstCommon
  rw [max_eq_left (sub_nonneg.mpr hcd)]
  nlinarith

/-- Source-consumable scalar improvement: unlike `first_common_exact`, this
requires only the symmetric norm facet proved for the actual numerator in
`FirstNumeratorValuation.lean`, with no directional transport assumption. -/
theorem first_common_symmetric (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (_hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤
      -(δ-max (4*ρ-1) ((2+22*ρ)/21))*c-E := by
  have hc : 0 ≤ c := hp.trans hpC
  by_cases hcd : d ≤ c
  · have hh := first_common_symmetric_hi ρ δ c d R E Lc R₀
      hρ hρmax hcd hR₀ hLc hnorm
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_right (4*ρ-1) ((2+22*ρ)/21)) hc
    nlinarith
  · have hnum := mul_le_mul_of_nonneg_left hLc (show 0 ≤ ρ by linarith)
    have hrad := mul_le_mul_of_nonneg_left (hRp.trans hpC)
      (show 0 ≤ 4*ρ-1 by linarith)
    have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
    have hpen := le_max_right (3*c-5*d-R) 0
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_left (4*ρ-1) ((2+22*ρ)/21)) hc
    unfold firstCommon
    rw [max_eq_right (show c-d ≤ 0 by linarith)]
    nlinarith

theorem first_common_symmetric_uniform_27_40 (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 28/73) (hδ : 27/40 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hnorm : 4*Lc ≤ 5*(c+d)) :
    firstCommon ρ δ c d R E Lc R₀ ≤ -(411/2920)*c-E := by
  have hh := first_common_symmetric ρ δ c d p R E Lc R₀ hρ (by linarith)
    hp hpC hpD hRp hR₀ hLc hnorm
  have hmax : max (4*ρ-1) ((2+22*ρ)/21) ≤ 39/73 := by
    apply max_le <;> linarith
  have hgap := mul_nonneg
    (show 0 ≤ δ-max (4*ρ-1) ((2+22*ρ)/21)-411/2920 by linarith)
    (hp.trans hpC)
  nlinarith

/-- A literal feasible mixture disproves the unqualified `δ+1-4ρ` rate.
The right signed types `(1,5)` and `(3,1)` realize these normalized totals. -/
theorem gamma_only_counterexample :
    firstCommon (19/54) (7/10) 1 (19/36) (13/36) 0 (65/36) 0 +
      (7/10+1-4*(19/54)) = 89/1944 := by
  norm_num [firstCommon]

end
end ValuationGain

#print axioms ValuationGain.first_common_directional_hi
#print axioms ValuationGain.first_common_exact
#print axioms ValuationGain.first_common_uniform_27_40
#print axioms ValuationGain.symmetric_radical_facet
#print axioms ValuationGain.first_common_symmetric
#print axioms ValuationGain.first_common_symmetric_uniform_27_40
#print axioms ValuationGain.gamma_only_counterexample
end

/- Original module: Candidate.Target836.SourceProvider.ActualValuation. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
Literal first-numerator valuation transport, checked against cached accepted
source modules.  This is a source inequality, not an endpoint theorem.
Arbitrary positive common-prime valuations are allowed; no sixth-free or
equal-support hypothesis is used.
-/

namespace OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic CompletedGauss
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentSecondCanonical
open Cycle63Moment
local notation "O" => HeckeFamily.O

def sourceExponent (left : Bool) (i j : ℕ) : ℕ :=
  if netExponent i j = 0 then 0 else
    if left then
      if 1+netExponent i j = 6 then 0 else 1+netExponent i j
    else
      if 7-netExponent i j = 6 then 0 else 7-netExponent i j

theorem sourceExponent_budget (left : Bool) (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    4*sourceExponent left i j ≤ 5*(i+j) := by
  have hk := netExponent_lt_six i j
  have he : sourceExponent left i j ≤ 5 := by
    cases left <;> unfold sourceExponent <;> split_ifs <;> omega
  by_cases hs : 4 ≤ i+j
  · omega
  · have hi2 : i ≤ 2 := by omega
    have hj2 : j ≤ 2 := by omega
    interval_cases i <;> interval_cases j <;> cases left <;>
      norm_num [sourceExponent, netExponent] at *

theorem numerator_norm_product (left : Bool) (C D : Ideal O) (hC : Supported C) :
    (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm =
      ∏ P : CommonIndex C D,
        P.val.absNorm ^ sourceExponent left (leftExponent C D P) (rightExponent C D P) := by
  cases left
  · rw [show (if false then firstLeftUncancelled C D else firstRightUncancelled C D) =
        firstRightUncancelled C D by rfl]
    rw [firstRightUncancelled, powered_numerator_norm]
    simp_rw [firstSignedPrime_span C D hC]
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      if 7-activeExponent C D P ≠ 6 then (activePrime C D P).absNorm^(7-activeExponent C D P)
      else 1) = _
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(7-netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1) P.val) = _
    rw [Finset.prod_coe_sort
      (s := CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
        (leftExponent C D) (rightExponent C D))
      (f := fun Q : CommonIndex C D =>
        if 7-netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(7-netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1)]
    simp only [ActiveIndex, CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, CenteredMomentCanonicalFirst.activeExponent, activePrime, h]
  · rw [show (if true then firstLeftUncancelled C D else firstRightUncancelled C D) =
        firstLeftUncancelled C D by rfl]
    rw [firstLeftUncancelled, powered_numerator_norm]
    simp_rw [firstSignedPrime_span C D hC]
    rw [Finset.prod_filter]
    change (∏ P : ActiveIndex C D,
      if 1+activeExponent C D P ≠ 6 then (activePrime C D P).absNorm^(1+activeExponent C D P)
      else 1) = _
    change (∏ P : ActiveIndex C D,
      (fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(1+netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1) P.val) = _
    rw [Finset.prod_coe_sort
      (s := CenteredMomentActive.activeSupport (Finset.univ : Finset (CommonIndex C D))
        (leftExponent C D) (rightExponent C D))
      (f := fun Q : CommonIndex C D =>
        if 1+netExponent (leftExponent C D Q) (rightExponent C D Q) ≠ 6 then
          Q.val.absNorm^(1+netExponent (leftExponent C D Q) (rightExponent C D Q))
        else 1)]
    simp only [ActiveIndex, CenteredMomentActive.activeSupport, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro P _
    by_cases h : netExponent (leftExponent C D P) (rightExponent C D P) = 0
    · simp [sourceExponent, h]
    · simp [sourceExponent, CenteredMomentCanonicalFirst.activeExponent, activePrime, h]

theorem literal_numerator_norm_bound (left : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : D ≠ 0) :
    (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm^4 ≤
      (C.absNorm*D.absNorm)^5 := by
  have hcommon :
      (Ideal.span {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm^4 ≤
        ((commonPart C D).absNorm*(commonPart D C).absNorm)^5 := by
    rw [numerator_norm_product left C D hC, ← Finset.prod_pow]
    have hprod : ((commonPart C D).absNorm*(commonPart D C).absNorm)^5 =
        ∏ P : CommonIndex C D,
          P.val.absNorm^(5*(leftExponent C D P+rightExponent C D P)) := by
      rw [commonPart_left_product, commonPart_right_product, map_prod, map_prod,
        ← Finset.prod_mul_distrib, ← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro P _
      rw [map_pow, map_pow, ← pow_add, ← pow_mul]
      congr 1
      omega
    rw [hprod]
    apply Finset.prod_le_prod
    intro P _
    rw [← pow_mul]
    apply pow_le_pow_right'
      (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (commonPrime_supported_ideal C D hC P).1))
    simpa only [Nat.mul_comm] using sourceExponent_budget left
      (leftExponent C D P) (rightExponent C D P)
      (leftExponent_pos C D P) (rightExponent_pos C D P)
  exact hcommon.trans (Nat.pow_le_pow_left
    (Nat.mul_le_mul (absNorm_commonPart_le C D hC.1) (absNorm_commonPart_le D C hD)) 5)

theorem literal_numerator_log_bound (left : Bool) (C D : Ideal O)
    (hC : Supported C) (hD : D ≠ 0) (Z : ℝ) (hZ : 1<Z) :
    4*Real.logb Z ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ) ≤
      5*(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)) := by
  have hnum : 0 < (Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm := by
    cases left <;>
      exact powered_numerator_norm_pos _ _ _ (fun P _ => firstSignedPrime_supported C D hC P)
  have hn := Real.logb_le_logb_of_le hZ
    (show (0:ℝ) < ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ)^4 by
      positivity)
    (show ((Ideal.span
      {if left then firstLeftUncancelled C D else firstRightUncancelled C D}).absNorm:ℝ)^4 ≤
      ((C.absNorm:ℝ)*D.absNorm)^5 by exact_mod_cast literal_numerator_norm_bound left C D hC hD)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_mul
    (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
    (by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hD)] at hn
  simpa only [Nat.cast_ofNat] using hn

/-- The requested source-label statement, independent of the inactive subset. -/
theorem actual_firstSourceNumerator_log_bound (left : Bool) (label : FirstSourceLabel)
    (hC : Supported label.1.1) (hD : label.1.2 ≠ 0) (Z : ℝ) (hZ : 1<Z) :
    4*Real.logb Z ((Ideal.span {firstSourceNumerator left label}).absNorm:ℝ) ≤
      5*(Real.logb Z (label.1.1.absNorm:ℝ)+Real.logb Z (label.1.2.absNorm:ℝ)) := by
  exact literal_numerator_log_bound left label.1.1 label.1.2 hC hD Z hZ

end
end OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation

#print axioms OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation.sourceExponent_budget
#print axioms OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation.literal_numerator_norm_bound
#print axioms OAI.SevenEighths.Cycle63Moment.FirstNumeratorValuation.actual_firstSourceNumerator_log_bound
end

/- Original module: Candidate.Target836.SourceProvider.HighPayment. -/
section

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
end
