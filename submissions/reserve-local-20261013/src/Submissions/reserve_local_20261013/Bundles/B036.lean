/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B009
import Submissions.reserve_local_20261013.Bundles.B012
import Submissions.reserve_local_20261013.Bundles.B013
import Submissions.reserve_local_20261013.Bundles.B024
import Submissions.reserve_local_20261013.Bundles.B025
import Submissions.reserve_local_20261013.Bundles.B029
import Submissions.reserve_local_20261013.Bundles.B032
import Submissions.reserve_local_20261013.Bundles.B033
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount

/- BEGIN ORIGINAL MODULE Cycle25.Energy.ReferenceRobustPower ; sha256 3b4dc4742241bd1b5494e97e0cdaa166e03e1954e8d1f6f5e969f473c593ce5d -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/ReferenceRobustPower.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustPower
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyReferenceRobustOriginal CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 7/10≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-rho/100≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+13*(rho/100)/8≤ s.width/16:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hg:=Cycle25CenteredMomentEnergyLiveClippingDefect.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤ Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.Cycle25CenteredMomentEnergyReferenceRobustPower

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.ReferenceRobustPower -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.FreeScalarBound ; sha256 88235f1bcc0d0e697f35aeda9df81ecb3e3ab54c098e75b6daa4250ccec5cc10 -/
section




/-! The calibrated scalar left after the quotient-free numerator expansion.
It contains no correction packet and consequently incurs no correction norm cost. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical
open HeckeInverseAmplification HeckeReciprocalGrowth ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

/-- The detector's actual next-bin bound controls the reciprocal uniformly in
all source exclusions; the remaining principal L-factor lies on Re s = 2.04. -/
theorem numeratorFreeRowScalar_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps) :
    ∃C : ℝ,0 < C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S)
      (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤ C*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0 ≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr,by positivity,?_⟩
  intro S hS hmax η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖ ≤ L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ) < 2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖ ≤ 1 := by
    rw [norm_star]
    exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold numeratorFreeRowScalar
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (1*(L+1))*(Cr*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps) :=
      mul_le_mul (mul_le_mul hcal hl (norm_nonneg _) (by norm_num)) hrec
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Exact arithmetic and height costs for the numerator-free scalar. In
particular the row norm exponent is 2 eps rather than the old 3 eps. -/
theorem numeratorFreeRowScalar_arithmetic_bound (e eps : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (heps : 0 < eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι]
      (ψ : ι→Character) (B a H : ℝ) (i : ℕ),
      2 < B → 51/100 ≤ a → a ≤ 1 → H ≤ (3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B) < a+2*e →
      ∀x z : ℂ,x.re=a+16*e → z.re=17/50 → |x.im| ≤ H →
      ‖numeratorFreeRowScalar S hS hmax η u x z‖ ≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := numeratorFreeRowScalar_bound e eps he he' heps
  have hF : 0 < (fixedConductorConstant S:ℝ) := by
    exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x z hx hz hxi
  have hh : 0 ≤ H := (abs_nonneg _).trans hxi
  apply (hbound S hS hmax η u ψ B a H i hB ha ha1 hH hbin x z hx hz hxi).trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  apply (mul_le_mul_of_nonneg_left hc hC.le).trans_eq
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.FreeScalarBound -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorPacket ; sha256 1f47ea1eda6274e15c4bb0a2ea6173428ab7780a41fee215d00717bae64cd399 -/
section



/-! Actual correction times arbitrary finite error slots as one absolutely
convergent coefficient series on both reconstruction lines. -/
noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators NNReal Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ProbeRow
local notation "O" => HeckeFamily.O

def ErrorPacketIndex (S : Finset (Ideal O)) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :=
  (T → Fin 4) × CorrectionIndex (markExclusions S T) u

def errorPacketCoefficient (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀ P ∈ T, Supported P.val) (x z : ℂ) (e : ErrorPacketIndex S u T) : ℂ :=
  errorTupleCoefficient η u T hT x z e.1 *
    correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e.2

def errorPacketScale (S : Finset (Ideal O)) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (e : ErrorPacketIndex S u T) : ℝ≥0 :=
  errorTupleScale T e.1 * correctionScale (markExclusions S T) u e.2

theorem errorPacketScale_one_le (S : Finset (Ideal O)) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (e : ErrorPacketIndex S u T) : 1 ≤ errorPacketScale S u T e := by
  unfold errorPacketScale errorTupleScale
  exact one_le_mul_of_one_le_of_one_le
    (finiteScale_one_le (fun P : T => primeScale P.val) (fun P => primeScale_one_le P.val) e.1)
    (correctionScale_one_le (markExclusions S T) u e.2)

def errorProductSize (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  ∏ P : T, 2880 * errorSize u P.val

def errorProductDeficit (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  ∏ P : T, (repeatedDeficit u P.val : ℝ)

theorem errorProductSize_nonneg (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    0 ≤ errorProductSize u T := by
  apply Finset.prod_nonneg
  intro P hP
  unfold errorSize
  split_ifs <;> positivity

theorem errorProductDeficit_one_le (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    1 ≤ errorProductDeficit u T := by
  apply Finset.one_le_prod₀
  intro P hP
  exact_mod_cast repeatedDeficit_one_le u P.val

theorem error_product_mass_factor (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (rho : ℝ) :
    (∏ P : T, 2880 * errorSize u P.val * (repeatedDeficit u P.val : ℝ)^rho) =
      errorProductSize u T * errorProductDeficit u T ^ rho := by
  rw [Finset.prod_mul_distrib]
  unfold errorProductSize errorProductDeficit
  congr 1
  exact (Real.finsetProd_rpow Finset.univ (fun P : T => (repeatedDeficit u P.val : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) rho)

theorem error_packet_coefficient_mass (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x z : ℂ) (alpha eps rho : ℝ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (halpha : (51 / 100 : ℝ) ≤ alpha) (halpha1 : alpha ≤ 1)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 1000)
    (hx : x.re = alpha + 16 * eps) (hz : z.re = 17 / 50)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hline : 1 - alpha - 6 * eps ≤ 1 / 2 - rho)
    (hleft : -(1 / 100 : ℝ) ≤ 1 / 2 - rho)
    (hmargin : 1 + firsteps ≤ x.re + (1 / 2 - rho)) :
    Summable (fun e : ErrorPacketIndex S u T => ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 - rho))) ∧
    (∑' e : ErrorPacketIndex S u T, ‖errorPacketCoefficient S hS η u T hT x z e‖ *
      (errorPacketScale S u T e : ℝ)^(-(1 / 2 - rho))) ≤
      (579 ^ (ramifiedPrimes (markExclusions S T) u).card * Real.exp (1 / 2)) *
        errorProductSize u T * errorProductDeficit u T ^ rho := by
  have hx' : (51 / 100 : ℝ) ≤ x.re := by rw [hx]; linarith
  obtain ⟨hH,hHm⟩ := continuedCorrection_coefficient_mass firsteps (1 / 2 - rho)
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx' hz.ge hleft hmargin
  have hE := error_product_coefficient_mass η u T hT hη x z alpha eps rho hQ
    halpha halpha1 heps heps1 hx hz hrho hrho1 hline
  rw [error_product_mass_factor] at hE
  have hEs := (hasSum_fintype (fun j : T → Fin 4 =>
    ‖errorTupleCoefficient η u T hT x z j‖ * (errorTupleScale T j : ℝ)^(-(1 / 2 - rho)))).summable
  refine ⟨weighted_product_summable _ _ _ _ (1 / 2 - rho) hEs hH, ?_⟩
  change (∑' e : (T → Fin 4) × CorrectionIndex (markExclusions S T) u,
    ‖errorTupleCoefficient η u T hT x z e.1 *
      correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e.2‖ *
    ((errorTupleScale T e.1 * correctionScale (markExclusions S T) u e.2 : ℝ≥0) : ℝ)^(-(1 / 2 - rho))) ≤ _
  rw [weighted_product_mass _ _ _ _ (1 / 2 - rho) hEs hH,tsum_fintype]
  exact (mul_le_mul hE hHm (tsum_nonneg (fun _ => by positivity))
    (mul_nonneg (errorProductSize_nonneg u T) (Real.rpow_nonneg
      (le_trans zero_le_one (errorProductDeficit_one_le u T)) rho))).trans_eq (by ring)

theorem error_packet_expansion (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, Supported P.val)
    (hη : ∀ P ∈ T, IsCoprime P.val η.modulus)
    (x w z : ℂ) (hQ : ∀ P ∈ T, (4 : ℝ) ≤ P.val.absNorm)
    (hx : (51 / 100 : ℝ) ≤ x.re) (hz : (17 / 50 : ℝ) ≤ z.re)
    (hw : -(1 / 100 : ℝ) ≤ w.re) (hxw : 1 + firsteps ≤ x.re + w.re) :
    (∏ P : T, rawErrorSlot η u P.val (hT P.val P.property) x w z) *
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z =
    ∑' e : ErrorPacketIndex S u T, errorPacketCoefficient S hS η u T hT x z e *
      (errorPacketScale S u T e : ℂ)^(-w) := by
  have hC := (continuedCorrection_coefficient_mass firsteps w.re
    (markExclusions S T) (markedSourceExclusions S hS T)
    (marked_firstTail firsteps S hfirst T) η u x z hx hz hw hxw).1
  have hCn : Summable (fun e : CorrectionIndex (markExclusions S T) u =>
    ‖correctionCoefficient (markExclusions S T) (markedSourceExclusions S hS T) η u x z e *
      (correctionScale (markExclusions S T) u e : ℂ)^(-w)‖) := by
    convert hC using 1
    ext e
    have hp : 0 < (correctionScale (markExclusions S T) u e : ℝ) :=
      lt_of_lt_of_le zero_lt_one (by exact_mod_cast correctionScale_one_le (markExclusions S T) u e)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re]
  rw [error_product_expansion η u T hT hη x w z hQ hx hz,
    continuedCorrection_coefficient_expansion firsteps (markExclusions S T)
      (markedSourceExclusions S hS T) (marked_firstTail firsteps S hfirst T)
      η u x w z hx hz hw hxw]
  have hprod := tsum_mul_tsum_of_summable_norm
    (hasSum_fintype (fun j : T → Fin 4 =>
      ‖errorTupleCoefficient η u T hT x z j * (errorTupleScale T j : ℂ)^(-w)‖)).summable hCn
  simp only [tsum_fintype] at hprod
  rw [hprod]
  apply tsum_congr
  intro e
  exact (mellin_product_term _ _ _ _ w e.1 e.2).symm

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorErrorPacket -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPrimeSeparation ; sha256 ebcb47bd9280bf8d33ede9b1efdbcb820ab47e436ce066205dc484948073d00a -/
section


/-! Separate the error-prime labels only after the exact quotient-free expansion. -/
noncomputable section
open scoped Classical BigOperators
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem sum_split_slots {α : Type*} [Fintype α] [DecidableEq α] (β : α→Type*) [∀i,Fintype (β i)]
    (p : α→Prop) [DecidablePred p]
    (F : (∀i:{i//p i},β i.val)→ℂ) (g : ∀i:{i//¬p i},β i.val→ℂ) :
    (∑v:(∀i,β i),F (fun i=> v i.val)*(∏j:{i//¬p i},g j (v j.val)))=
      (∑v:(∀i:{i//p i},β i.val),F v)*(∏j:{i//¬p i},∑v:β j.val,g j v) := by
  calc
    _ = ∑v:((∀i:{i//p i},β i.val)×(∀i:{i//¬p i},β i.val)),F v.1*(∏j,g j (v.2 j)) :=
      Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd p β) _ _ (fun _=> rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [←Finset.mul_sum]
      rw [←Finset.sum_mul,←Fintype.prod_sum]

def partialErrorTuple {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i:I,T i.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  continuedCorrection (markExclusions S (Finset.univ.image (fun i:I=>(P i).val)))
    (markedSourceExclusions S hS _) η u x w z*
    ∏i:I,physicalSlotWeight (P i).val (W i.val) (Y i.val) z*
      rawErrorSlot η u (P i).val
        (outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)) x w z

lemma restricted_tuple_image {K : ℕ} (I : Finset (Fin K)) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    Finset.univ.image (fun i:I=> P i.val)=I.image P := by
  ext Q
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i.val,i.property,hi⟩
  · rintro ⟨i,hi,heq⟩
    exact ⟨⟨i,hi⟩,heq⟩

theorem weightedErrorTuple_restrict {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (P : ∀i,T i) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    weightedErrorTuple S hS η u I (fun i=>(P i).val) (fun i=> hT i _ (P i).property) W Y x w z=
      partialErrorTuple S hS η u I T hT (fun i=> P i.val) W Y x w z := by
  unfold weightedErrorTuple partialErrorTuple
  simp only [restricted_tuple_image I (fun i=>(P i).val)]
  congr 1
  exact (Finset.prod_coe_sort I _).symm

theorem physicalMainTuple_restrict {K : ℕ} (u : FreeRow) (I : Finset (Fin K))
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (z : ℂ) :
    physicalMainTuple u I P W Y z=
      ∏j:{i:Fin K//i∉I},physicalSlotWeight (P j.val) (W j.val) (Y j.val) z*
        (-star (idealRowHom u.val (P j.val).val)) := by
  exact Finset.prod_subtype (Finset.univ\I) (by simp)
    (fun i=> physicalSlotWeight (P i) (W i) (Y i) z*(-star (idealRowHom u.val (P i).val)))

theorem weightedErrorTuple_main_sum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (I : Finset (Fin K))
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∑P:(∀i,T i),weightedErrorTuple S hS η u I (fun i=>(P i).val)
      (fun i=> hT i _ (P i).property) W Y x w z*
      physicalMainTuple u I (fun i=>(P i).val) W Y z)=
      (∑P:(∀i:I,T i.val),partialErrorTuple S hS η u I T hT P W Y x w z)*
      (∏j:{i:Fin K//i∉I},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Y j.val) z*
        (-star (idealRowHom u.val P.val.val))) := by
  simp_rw [weightedErrorTuple_restrict,physicalMainTuple_restrict]
  convert! sum_split_slots (fun i=> T i) (fun i=> i∈I)
    (fun P=> partialErrorTuple S hS η u I T hT P W Y x w z)
    (fun j P=> physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))) using 1
  congr 1
  apply Finset.sum_congr
  · ext P
    simp
  · intro P hP
    rfl

theorem calibrated_prime_error_slots_separate {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (htail : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hw : -(1/100:ℝ)≤ w.re) (hxw : 1+eps≤ x.re+w.re) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=> hT i _ (P i).property) W Y x w z)=
      numeratorFreeRowScalar S hS hmax η u x z*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        (∑I∈Finset.univ.powerset,
          (∑P:(∀i:I,T i.val),partialErrorTuple S hS η u I T hT P W Y x w z)*
          (∏j:{i:Fin K//i∉I},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Y j.val) z*
            (-star (idealRowHom u.val P.val.val)))) := by
  calc
    _ = ∑P:(∀i,T i),numeratorFreeRowScalar S hS hmax η u x z*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        (∑I∈Finset.univ.powerset,weightedErrorTuple S hS η u I (fun i=>(P i).val)
          (fun i=> hT i _ (P i).property) W Y x w z*
          physicalMainTuple u I (fun i=>(P i).val) W Y z) := by
      apply Finset.sum_congr rfl
      intro P hP
      exact calibratedTupleValue_error_subsets eps S hS htail hmax _ (hdis P) _ η u W Y x w z hx hz hw hxw
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro I hI
      exact weightedErrorTuple_main_sum S hS η u I T hT W Y x w z

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorPrimeSeparation -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.PhysicalFront ; sha256 1366fb5221bb47e40d1aeb132fd2f5d75c3e42aca9e94f30e9700e01055c2677 -/
section







/-! Exact front factors of the reconstructed numerator and source-pool geometry.
All prime amplitudes retain their original canonical zero extensions. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace Cycle25.Numerator
open Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbePhysical HeckeFamily
open ProbeRaySlots HeckeInverseAmplification CanonicalRowCompletion
local notation "O" => HeckeFamily.O

theorem physicalMainPool_sum (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (u : FreeRow)
    (W : ℝ→ℂ) (a b Y : ℝ) (ha : 0 < a) (hab : a ≤ b) (hY : 0 < Y)
    (hW : Function.support W⊆Set.Ioo a b) (hS : ∀P∈S,(P.absNorm:ℝ) ≤ a*Y) (z : ℂ) :
    (∑P:pool (RayQuotient.identityClass M H) S a b Y,
      physicalSlotWeight P.val W Y z*(-star (idealRowHom u.val P.val.val)))=
      -(Y:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b Y z := by
  unfold physicalSlotWeight
  rw [Finset.sum_coe_sort (pool (RayQuotient.identityClass M H) S a b Y)
    (fun P=> W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val)))]
  exact central_phase_eq_amplitude M H S u.val W a b Y ha hab hY hW hS z

theorem physicalMainPool_product {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) :
    (∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val)))=
      ∏j:{i:Fin K//i∉J},(-(Y j.val:ℂ)^(z-1/2)*
        HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j.val) b (Y j.val) z) := by
  apply Finset.prod_congr rfl
  intro j _
  exact physicalMainPool_sum M H S u (W j.val) a b (Y j.val) ha hab
    (hY j.val) (hW j.val) (hS j.val) z

theorem physicalMainPool_product_norm {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) :
    ‖∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))‖=
      (∏j:{i:Fin K//i∉J},(Y j.val)^(z.re-1/2))*
        ‖∏j:{i:Fin K//i∉J},HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j.val) b (Y j.val) z‖ := by
  rw [physicalMainPool_product M H S u J W a b Y ha hab hY hW hS z,norm_prod,norm_prod,
    ←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos (hY j.val)]
  norm_num

/-- On a row dyad whose lower edge is U, no fixed constant is lost. -/
theorem frequencyWeight_dyad_bound (u : FreeRow) (z : ℂ) (U r : ℝ)
    (hU : 0 < U) (hr : 0 ≤ r) (hz : z.re=r) (hu : U ≤ rowNorm u) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤ U^(-r) := by
  rw [frequencyWeight_ideal_norm,hz]
  exact Real.rpow_le_rpow_of_nonpos hU hu (neg_nonpos.mpr hr)

/-- The source slots used by the actual full-w cells. -/
def sourcePrimePool {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (j : Fin D.N) :=
  pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Z^(D.ell j))

theorem source_complex_support_open {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    Function.support (F.W:ℝ→ℂ)⊆Set.Ioo 1 2 := by
  intro y hy
  apply F.support
  intro hw
  exact hy (by rw [F.complex_eq,hw];simp)

theorem source_prime_pool_outside {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (j : Fin D.N)
    (P : ProbePhysical.PrimeIdeal) (hP : P∈sourcePrimePool F Z j) : P.val∉F.S :=
  ((mem_pool _ _ _ _ _ P).mp hP).2.2.2

/-- Every restricted tuple and full tuple is injective, every prime is coprime
with the fixed external character, and all prime norms exceed four. -/
theorem source_prime_reconstruction_geometry {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop, 1 ≤ Z ∧
      (∀J : Finset (Fin D.N),∀P:(∀i:J,sourcePrimePool F Z i.val),
        Function.Injective (fun i=>(P i).val)) ∧
      (∀P:(∀i,sourcePrimePool F Z i),Function.Injective (fun i=>(P i).val)) ∧
      (∀j P,P∈sourcePrimePool F Z j→IsCoprime P.val η.modulus) ∧
      (∀j P,P∈sourcePrimePool F Z j→(4:ℝ) ≤ P.val.absNorm) ∧
      (∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j)) := by
  have hlarge : ∀ᶠZ : ℝ in atTop,∀j:Fin D.N,
      4 ≤ Z^(D.ell j) ∧ (η.modulus.absNorm:ℝ) < Z^(D.ell j) ∧
        ∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j) := by
    apply Filter.eventually_all.mpr
    intro j
    have ht := tendsto_rpow_atTop (D.slots_bounds j).1
    filter_upwards [ht.eventually (eventually_ge_atTop (4:ℝ)),
      ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
      ht.eventually (eventually_ge_atTop (∑P∈F.S,(P.absNorm:ℝ)))] with Z h4 hη hS
    refine ⟨h4,hη,?_⟩
    intro P hP
    exact (Finset.single_le_sum (fun Q _=> Nat.cast_nonneg _) hP).trans hS
  filter_upwards [hlarge,eventually_ge_atTop (1:ℝ),
    power_pools_eventually_disjoint (RayQuotient.identityClass F.modulus ⊤) F.S
      (fun _:Fin D.N=>1) (fun _=>2) D.ell (fun _=> by norm_num)
      (fun _=> by norm_num) D.slots_injective] with Z hlarge hZ hdis
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hall : ∀P:(∀i,sourcePrimePool F Z i),Function.Injective (fun i=>(P i).val) := by
    intro P i j he
    dsimp only at he
    by_contra hij
    exact Finset.disjoint_left.mp (hdis i j hij) (P i).property
      (by rw [he];exact (P j).property)
  refine ⟨hZ,?_,hall,?_,?_,fun j=>(hlarge j).2.2⟩
  · intro J P i j he
    dsimp only at he
    apply Subtype.ext
    by_contra hij
    exact Finset.disjoint_left.mp (hdis i.val j.val hij) (P i).property
      (by rw [he];exact (P j).property)
  · intro j P hP
    have hp := pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2)
      (Real.rpow_pos_of_pos hZpos (D.ell j)) P hP
    apply prime_coprime_of_norm_gt η P
    exact (hlarge j).2.1.trans (by simpa only [mul_one] using hp.1)
  · intro j P hP
    have hp := pool_norm_bounds (RayQuotient.identityClass F.modulus ⊤) F.S
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2)
      (Real.rpow_pos_of_pos hZpos (D.ell j)) P hP
    exact (hlarge j).1.trans (by simpa only [mul_one] using hp.1.le)


/-- Exact source normalization, for the complex source profile used in moments. -/
theorem source_main_product {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (hZ : 0 < Z)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (J : Finset (Fin D.N)) (z : ℂ) :
    (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
      physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val)))=
      ∏j:{i:Fin D.N//i∉J},(-((Z^(D.ell j.val):ℝ):ℂ)^(z-1/2)*
        HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z) := by
  exact physicalMainPool_product F.modulus ⊤ F.S u J (fun _=> F.W) 1 2
    (fun j=> Z^(D.ell j)) (by norm_num) (by norm_num)
    (fun j=> Real.rpow_pos_of_pos hZ _) (fun _=> source_complex_support_open F)
    (fun j P hP=> by simpa only [one_mul] using hS j P hP) z

/-- The total physical normalization for all remaining main slots. -/
theorem source_main_product_norm {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z : ℝ) (hZ : 0 < Z)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (J : Finset (Fin D.N)) (z : ℂ) :
    ‖∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
      physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))‖=
      Z^((∑j:{i:Fin D.N//i∉J},D.ell j.val)*(z.re-1/2))*
        ‖∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude
          F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z‖ := by
  unfold sourcePrimePool
  rw [physicalMainPool_product_norm F.modulus ⊤ F.S u J (fun _=> F.W) 1 2
    (fun j=> Z^(D.ell j)) (by norm_num) (by norm_num)
    (fun j=> Real.rpow_pos_of_pos hZ _) (fun _=> source_complex_support_open F)
    (fun j P hP=> by simpa only [one_mul] using hS j P hP) z]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,Finset.sum_mul]

/-- The norm of the frequency and all literal main-prime factors on a dyad. -/
theorem source_frequency_main_bound {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (Z U : ℝ) (hZ : 0 < Z) (hU : 0 < U)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.ell j))
    (u : FreeRow) (hu : U ≤ rowNorm u) (J : Finset (Fin D.N))
    (z : ℂ) (hz : z.re=17/50) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩*
      (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
        physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val)))‖ ≤
      U^(-(17/50:ℝ))*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*
        ‖∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude
          F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z‖ := by
  rw [norm_mul,source_main_product_norm F Z hZ hS u J z]
  have hf := frequencyWeight_dyad_bound u z U (17/50) hU (by norm_num) hz hu
  apply (mul_le_mul_of_nonneg_right hf (by positivity)).trans_eq
  rw [hz]
  have he : (∑j:{i:Fin D.N//i∉J},D.ell j.val)*((17/50:ℝ)-1/2)=
      -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val) := by ring
  rw [he]
  ring

/-- The literal real-profile front factors in FullWCellsAt are the same source
complex profile; this is an identity of functions, with no norm relaxation. -/
theorem source_real_profile_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) :
    (fun (_:Fin D.N) y=>(F.w y:ℂ))=(fun _=>(F.W:ℝ→ℂ)) := by
  funext j y
  exact (F.complex_eq y).symm


/-- Bin upper bounds are applied only to the remaining main slots; their
canonical amplitudes and original zero extensions are unchanged. -/
theorem physicalMainPool_product_bound {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)] (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (u : FreeRow) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (a b : ℝ) (Y : Fin K→ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hY : ∀j,0 < Y j)
    (hW : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hS : ∀j,∀P∈S,(P.absNorm:ℝ) ≤ a*Y j) (z : ℂ) (hz : z.re=17/50)
    (U : ℝ) (hU : 0 < U) (width upper : Fin K→ℝ)
    (hQ : ∀j,j∉J→‖HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z‖ ≤
      U^(width j*upper j)) :
    ‖∏j:{i:Fin K//i∉J},∑P:pool (RayQuotient.identityClass M H) S a b (Y j.val),
      physicalSlotWeight P.val (W j.val) (Y j.val) z*(-star (idealRowHom u.val P.val.val))‖ ≤
      (∏j:{i:Fin K//i∉J},(Y j.val)^(-(4/25:ℝ)))*
        U^(∑j:{i:Fin K//i∉J},width j.val*upper j.val) := by
  rw [physicalMainPool_product_norm M H S u J W a b Y ha hab hY hW hS z,hz]
  norm_num only [show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun j _=> Real.rpow_nonneg (hY j.val).le _))
  rw [norm_prod,Real.rpow_sum_of_pos hU]
  exact Finset.prod_le_prod₀ (fun j _=> norm_nonneg _) (fun j _=> hQ j.val j.property)

/-- Error and main subsets together retain every physical prime normalization. -/
theorem error_main_scale_product {K : ℕ} (J : Finset (Fin K)) (Y : Fin K→ℝ) (r : ℝ) :
    (∏j:J,(Y j.val)^r)*(∏j:{i:Fin K//i∉J},(Y j.val)^r)=∏j,(Y j)^r := by
  convert Fintype.prod_subtype_mul_prod_subtype (fun j=> j∈J) (fun j=>(Y j)^r) using 1
  congr 1
  apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl

theorem error_main_source_scale {K : ℕ} (J : Finset (Fin K))
    (Z : ℝ) (hZ : 0 < Z) (ell : Fin K→ℝ) :
    (∏j:J,(Z^(ell j.val))^(-(4/25:ℝ)))*
      (∏j:{i:Fin K//i∉J},(Z^(ell j.val))^(-(4/25:ℝ)))=
      Z^(-(4/25:ℝ)*(∑j,ell j)) := by
  rw [error_main_scale_product J (fun j=> Z^(ell j)) (-(4/25:ℝ))]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul]
  congr 1
  ring

/-- The enlarged moment conductor includes two detector margins. This precise
identity prevents mistaking it for the actual lower edge of the row dyad. -/
theorem frequencyWeight_source_conductor_bound (u : FreeRow) (z : ℂ)
    (Z margin : ℝ) (k : ℕ) (hZ : 1 < Z) (hz : z.re=17/50)
    (hu : u∈dyadicRows 1 k) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖ ≤
      Z^((17/25:ℝ)*margin)*(Z^(sourceDyadConductor Z margin k))^(-(17/50:ℝ)) := by
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hlo : (2:ℝ)^k ≤ rowNorm u := by simpa only [one_mul] using (mem_dyadicRows.mp hu).2.1
  apply (frequencyWeight_dyad_bound u z ((2:ℝ)^k) (17/50) (by positivity) (by norm_num) hz hlo).trans_eq
  rw [←sourceDyad_scale hZ k]
  rw [←Real.rpow_mul hZpos.le,←Real.rpow_mul hZpos.le,←Real.rpow_add hZpos]
  unfold sourceDyadConductor
  congr 1
  ring

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.PhysicalFront -/

/- BEGIN ORIGINAL MODULE Global.Detector.WeightedSourceCount ; sha256 0a61b905deaa2981e6d5c6cdc654c66e89a6193aee59e1b4421b2d4a881ef088 -/
section






/-! Source specialization of the original certified amplitude-class row count.
This stops before any physical numerator estimate. -/
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.Detector
open OAI OAI.SevenEighths
open Cycle25ProbeFinalAssembly Cycle25ProbeHighRowFamily Cycle25WeightedHighRowFamily
open ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem weighted_source_amplitude_count {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      weighted_SourceMomentBound F D.momentKappa counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
        (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=> D.ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.ell j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*Z^(3*D.t)*
          (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by
  obtain ⟨K,hK,hcount⟩ := Cycle25ProbeFinalAssembly.balanced_source_count_from_raw_moments F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t_pos (Sum Bool (RayQuotient.Characters F.modulus ⊤)) D.N n
    (1/200) (7/8) τ D.t (2*τ) D.t D.t
    (by norm_num) (by norm_num) hτ D.t_pos (by linarith) D.t_pos counts
  refine ⟨K+1,by linarith,?_⟩
  intro η
  have hbatches := Cycle25WeightedHighRowFamily.actual_source_amplitude_batches F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.κ D.cost D.t D.t D.t D.momentKappa n
    (by norm_num) (by norm_num) D.momentKappa_lo D.momentKappa_hi hτ hτzero hτheight
    D.epsilon_pos D.e_pos D.e_small D.kappa_pos D.kappa_small D.cost_pos.le
    D.t_pos D.t_pos.le D.t_pos (by nlinarith only [D.detector_budget])
  filter_upwards [hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hc hb hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  let Q := physical F.modulus ⊤ (fun u : FreeRow=> u.val) (fun _ y=>(F.w y:ℂ))
    (fun _=>2) (fun j=> D.ell j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
    (fun j=> D.ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=> D.ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (Z^(d-D.t)+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hrows u hu).2.2.2]⟩
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hb d hd hd' (Z^(d-D.t)+1) rows (hne.mono hsub) hband
      (fun u hu=>(hrows u hu).2.2.1) (fun u hu=>(hrows u hu).2.2.2)
      a i hi ha (by linarith) hnext hcurrent D.N D.ell (fun j=>(D.slots_bounds j).1)
      (fun j=>(D.slots_bounds j).2.2) (by rw [D.slots_sum]; linarith [Submission20261012.Global.ell_interval.1]) (fun _ y=>(F.w y:ℂ))
      (fun _=>2) (fun _=> z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=
      sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := (hmom rows d a hd hd' ha (by linarith) hrows i z hz hzim)
    q B hBsub hBd hRev hSlots hWidths hW hUpper hExternal hMesh hBin hBfam
  have hcard := hc d hd hd' a D.ε D.momentKappa D.t C0 q i hi ha (by linarith) (by linarith)
    D.epsilon_pos.le D.epsilon_small D.momentKappa_lo D.momentKappa_hi D.t_pos (by linarith)
    B (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun j=> D.ell j/d) Q bin (by linarith)
    (fun j _=>(div_pos (D.slots_bounds j).1 hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum]; exact div_pos Submission20261012.Global.ell_pos hdpos) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have he : Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+159*D.ε+D.t+D.t+7*D.t=Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t) := by ring
  rw [he] at hcard
  apply hcard.trans
  have hC0pos : 0 ≤ C0 := by linarith
  have hcp : 0 ≤ (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) D.momentKappa+(159*D.ε+9*D.t)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hcp
  apply mul_le_mul
  · nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · positivity
  · positivity

end Submission20261012.Global.Detector
end

#print axioms Submission20261012.Global.Detector.weighted_source_amplitude_count
end
/- END ORIGINAL MODULE Global.Detector.WeightedSourceCount -/
