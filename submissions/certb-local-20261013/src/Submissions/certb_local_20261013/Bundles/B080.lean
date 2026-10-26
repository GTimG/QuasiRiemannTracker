/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.certb_local_20261013.Bundles.B042
import Submissions.certb_local_20261013.Bundles.B052
import Submissions.certb_local_20261013.Bundles.B064
import Submissions.certb_local_20261013.Bundles.B067
import Submissions.certb_local_20261013.Bundles.B078
import Submissions.certb_local_20261013.Bundles.B079
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedColumn
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstHighExceptionalPowers
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstLiveAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowCompletedFiber

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowCompletedFiber ; sha256 6594899d1ed0ac39d98f0c1e39b1518193651a9db8fe715d9de1c8f7b225aafc -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowCompletedFiber.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_completed_fiber_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0< Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J : Ideal Eis) (_hJ : J≠0)
      (Z d ell0 shift : ℝ), Z₀≤ Z → 0≤ d → d≤ Submission20261012.Global.ell → 0≤ ell0 → ell0≤ Submission20261012.Global.ell-d+η → |shift|≤η →
      (Ideal.absNorm J:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P) →
      (∀ i,1≤ H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤ H i) → (∏ i,H i)≤ Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈representativeRowFiber parents J (Ideal.span {m}*F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  have hsubmissionEll := Submission20261012.Global.ell_interval
  let Q₀ := Q*Ideal.span {(72:Eis)}
  let c : Eis := (9:Eis)*(ConcretePrimeRowBridge.idealGenerator Q)*(72:Eis)
  have hc : c≠0 := mul_ne_zero (mul_ne_zero (by norm_num)
    (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ)) (by norm_num)
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀ := by
    dsimp only [c,Q₀]
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      ConcretePrimeRowBridge.span_idealGenerator]
    ring
  let : Finite (Eis⧸Ideal.span {c}) := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : mask≠0 := mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := low_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
    (fun h => (E h).shape) hEc hEN (fun h => (E h).primary) (fun h => (E h).coprime)
    mask hmask0 Ck η hCk hη hη1 rmax
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J hJ Z d ell0 shift hZ hd hd1 hell hellcap hshift hJn
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod Ψ hΨnorm hΨperiod u θ w hw
  let rows := originalResidualRows parents J mask
  have hparents0 : ∀ I∈parents,I≠0 := fun I hI => (hparents I hI).1
  let hrows : ∀ K∈rows,Admissible K := originalResidualAdmissible parents J F m hbad
  have hcop : ∀ K∈rows,IsCoprime Q₀ K := by
    intro K hK
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    exact rowResidualPart_coprime_period I F Q₀ m hperiod
  have hGN : ∀ f,IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q₀).ideal f) :=
    (poolPrimeFamily J mask Q₀).level_coprime Q₀ c hcQ (poolPrimeFamily_period J mask Q₀)
  have hrowcop : ∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J mask Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine ⟨?_,residual_level_coprime K Q₀ (hrows K hK) c hcQ (hcop K hK)⟩
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
    obtain ⟨hIp,hpow,hmask'⟩ := Finset.mem_filter.mp hI
    exact poolPrimeFamily_fiber_row_coprime J I mask Q₀ hJ (hparents0 I hIp) hmask0 hpow.symm hmask'.symm
  have hLN : ∀ i,∀ P∈lists i,IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP => maximal_prime_level_coprime P (hmax i P hP) (hgood i P hP) Q₀ c hcQ (hLP i P hP)
  have hz : 1< Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0< Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hO : 0≤ O := normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):ℝ) := by
    have := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  obtain ⟨D,hD⟩ := he (σ:=σ) J F Q₀ hJ hF.ne_zero Z d ell0 shift O
    hZ hd hd1 hell hellcap hshift rfl hJn parents rows hparents (Finset.Subset.refl _) hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q₀)
    hrowcop hLN hodd
  let scalar := fun h (K : rows) => fixedThetaRowCoeff c hc
    ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Ψ Q) h
  have hscalar : ∀ h K,‖scalar h K‖≤1 := fun h K =>
    (residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm Ψ Q hΨnorm c hc h
  have henergy := hD θ w scalar hw hscalar
  have hTw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) :=
    CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW θ
  have hTs := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W θ) :=
    HasCompactSupport.intro isCompact_Icc (fun x hx => by
      by_contra hn
      exact hx (hTs hn))
  have hid (K : rows) := original_completed_residual_source parents J F hJ hF m hm hparents0 u hbad
    Q hQ c hc hcQ E hcop lists hmax hgood hdis hodd hLP D Ψ hΨnorm hΨperiod hmLam hm2
    (CompletedHeight.normTwistedSource W θ) hTc lo hi hlo hTs hTw (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w K
  have hre := original_fiber_energy_reindex parents J (mask) hparents0
    (fun I => ∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator I))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))
  rw [hre]
  have heq : (∑ K : rows,‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)=
      ∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ h,scalar h K*
        ∑ A : Finset (FreeReflection.pool J mask Q₀),frozenInactiveWeight J F mask Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical ((poolPrimeFamily J mask Q₀).restrict A)
            (poolPrimeFamily J mask Q₀).ideal rows hrows lists hmax hgood T (D h A T) (E h).shape (E h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift)) w K‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hid K)
  have hbound := heq.trans_le henergy
  have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):ℝ) := Real.rpow_logb hzp (ne_of_gt hz) hPowPos
  have hR : C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+506*η-O/2)=
      C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+506*η)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
    rw [show ((1-Submission20261012.Global.ell)-d)+506*η-O/2=(((1-Submission20261012.Global.ell)-d)+506*η)+O*(-(1/2:ℝ)) by ring,
      Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
    ring
  have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis =>
    ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
      (CompletedHeight.normTwistedSource W θ) (Z^(1+ell0+shift))
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)
  exact hs.symm.trans_le (hbound.trans_eq hR)
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowCompletedFiber -/

/- BEGIN ORIGINAL MODULE Global.Numerator.ActualSourceHelpers ; sha256 b719183277617e8a400e23fa00473a24dbe55b0c3773048a30c5ae659cb3651a -/
section




/-! Actual source amplitude estimates on the retained external rectangle. -/
noncomputable section
open scoped Classical BigOperators
open Filter
namespace Submission20261012.Global.Numerator
open Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25.Weighted ProbeAssembly HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

theorem actual_source_prime_upper {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (τ:ℝ) (n:ℕ)
    (hτ:0 < τ) (hheight:4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ:ℝ in atTop,∀(rows:Finset FreeRow) (d a:ℝ) (i:ℕ),
      1/2≤ d → d≤ h+rowExtension → 51/100≤ a → a≤7/8 → i≤ n →
      ∀η:Character,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-D.t)) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      ∀p∈FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),∀u∈rows,∀j:Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j))
        ((17/50:ℂ)+p.2*Complex.I)
      ‖Q‖≤(Z^(D.ell j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.ell j)) ((2*a-1)/2) D.t Q+D.t) := by
  filter_upwards [weighted_source_prime_bins D F τ n hτ hheight] with Z hbins
  intro rows d a i hd hdmax ha hatop hi η hrows hnext p hp u hu j
  have hd' : d≤7/8 := by norm_num [rowExtension,Endpoint.zeta] at hdmax;linarith [Submission20261012.Global.h_interval.2]
  have hb := hbins d (by linarith) hd' η u (hrows u hu).1 (hrows u hu).2.1
    (hrows u hu).2.2 a i hi ha (by linarith) (hnext u hu) ((17/50:ℂ)+p.2*Complex.I)
    (by norm_num) (by simpa using hp.2) j
  have he : a-1/2=(2*a-1)/2 := by ring
  simpa only [he] using hb.2.2.2.1

end Submission20261012.Global.Numerator
end
end
/- END ORIGINAL MODULE Global.Numerator.ActualSourceHelpers -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedErrorCaps ; sha256 9343a4c9d621f1bf4c91bbb9a7ca189a14246375648cba2e80fa00119875d4cc -/
section



/-! Actual extracted error estimates with Ready discharged by source caps.
Dead extracted sources vanish exactly. Every live extracted source receives
its Ready packet from the pinned source theorem before the genuine analytic
estimate is used. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance actualExtractedErrorCapsDecEq {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance actualExtractedErrorCapsFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstLiveAdmission

theorem actual_firstExtractedErrors_power_from_caps
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost)
    (Avol Dscale Pmask qmoving εgeo : ℝ) (hεgeo : 0 < εgeo)
    (hbudget : CenteredMomentFirstSecondInputGates.exponent Avol Dscale Pmask qmoving εgeo ξ ≤ Bcap):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀ prime : O, Prime (Ideal.span {prime}) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀ family : Fin 3 → RayCharacter → Character,
    (∀ i χ, (family i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ i χ, ((family i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun i : Fin 3 => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    src.W₁ 0=0 → src.W₂ 0=0 → volume src≤ Z^Avol →
    (R0.absNorm : ℝ)≤ Z^Pmask → R0≠0 →
    (∀ i, (radius i)⁻¹≤ Z^Dscale) →
    (∀ i χ, ((family i χ).modulus.absNorm : ℝ)≤ Z^qmoving) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r : Fin 3 → RayCharacter → ℝ,
    (∀ (i : Fin 3) (χ : RayCharacter)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools
        ((Ideal.span {prime})^(errorIndex i+1))),
      let input := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
      Z^(r i χ) ≤ input.X₁ ∧ Z^(r i χ) ≤ input.X₂ ∧ Z^(r i χ) ≤ input.Y₁ ∧ Z^(r i χ) ≤ input.Y₂) →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime family ≤
      mass (child src C R0 B τ t)^2*
        ∑i : Fin 3, 16*(errorIndex i+2:ℝ)^2*localErrorCost prime (errorIndex i)*
          ∑χ : RayCharacter, ∑j : Fin 4,
            ((Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/
                (seed.absNorm:ℝ))*
              CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (errorIndex i+1)
                (τ.modulus.absNorm:ℝ) Z (radius i)
                (refinedErrorDeficit prime Z (errorIndex i+1) sigma
                  (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving (r i χ) j)*
              (volume (child src C R0 B τ t)/(normValue prime)^(errorIndex i+1))^(powers εsrc j) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_original_subsets_error_power (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ,
    eventually_active_error_ready N upper (max 1 b) (max 1 b) εgeo
      hupper (le_max_left _ _) (le_max_left _ _) hεgeo] with Z hZ hreadyZ
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime hprimeScale hslot family hrad hfamily
  dsimp only
  intro hzero1 hzero2 hvolumeCap hmaskCap hR0 hradInv hconductorCap seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip
    hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower r hr
  have hzpos : 0 < Z := zero_lt_one.trans hZ.1
  have hp0 : prime ≠ 0 := fun h => hprime.ne_zero (by simp [h])
  apply firstExtractedErrors_power_budget (child src C R0 B τ t) (R0*C) seed Z
    (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime hprime hslot family
  · intro i χ j
    apply mul_nonneg
    · positivity
    · fin_cases j <;>
        simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
        (try unfold errorCommonRadius) <;> positivity
  · intro i χ Bp
    let d := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
    let Re := (R0*C)*(Ideal.span {prime})^(errorIndex i+1)
    let Ke := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve prime (errorIndex i+1)
    by_cases hdead : ∀ I : Ideal O, (original d Re seed).beta I = 0
    · have he := CenteredMomentFirstSecondInputGates.normalized_zero d Re seed hdead ballProfile Ke
      change normalizedGaussSource d Re seed ballProfile Ke ≤ _
      rw [he]
      apply mul_nonneg _ (sq_nonneg _)
      apply Finset.sum_nonneg
      intro j hj
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · fin_cases j <;>
            simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
            (try unfold errorCommonRadius) <;> positivity
      · exact Real.rpow_nonneg (volume_pos _).le _
    have hlive : ∃ I : Ideal O, (original d Re seed).beta I ≠ 0 := by
      simpa only [not_forall] using hdead
    have he : Endpoints upper (max 1 b) (max 1 b) src :=
      ⟨hupperSrc, (fun i => by rw [hhiSrc i]; exact hhighs i.val), hb1, hb1max, hb2, hb2max⟩
    have hKe : 0 < Ke := Real.rpow_pos_of_pos hzpos _
    have hR := hreadyZ.2 src hcard he C R0 seed B τ t hR0 hB
      (Ideal.span {prime}) (Ideal.span_singleton_eq_bot.not.mpr hp0) (errorIndex i+1)
      hslot Bp (family i χ) t Ke Avol Dscale Pmask qmoving ξ hKe hξ.le hzero1 hzero2
      hvolumeCap (hradInv i) hmaskCap (hconductorCap i χ) hlive
    have hready : Ready d Re Ke Z ξ Bcap := ready_mono d Re Ke Z ξ _ Bcap hZ.1.le hbudget hR
    have hk : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
      fin_cases i <;> norm_num [errorIndex]
    exact hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      prime hp0 (errorIndex i) hk hprimeScale hslot Bp (family i χ) χ t (hrad i χ) (hfamily i χ)
      (errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t) rfl
      hready seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (r i χ) (hr i χ Bp).1 (hr i χ Bp).2.1 (hr i χ Bp).2.2.1 (hr i χ Bp).2.2.2

#print axioms actual_firstExtractedErrors_power_from_caps
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedErrorCaps -/

/- BEGIN ORIGINAL MODULE Analytic.ActualExtractedErrors ; sha256 e9c45c97fe96b87079c5e8a0aaa0a946e93485960e5bb6e0fa07c69e96a84c69 -/
section


/-! Literal extracted errors from the actual first common child. All
analytic estimates, restored source matching and refined affine admission
are supplied internally before the actual extraction allocations are summed. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization
open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization
open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates


open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice

theorem actual_firstExtractedErrors_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap εremove lo hi εchild:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(haUpper:a≤1/4)(hbPlain:1≤ b)
    (L:ℝ)(hL:0≤ L)
    (ha:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)(hMcap:0< Mcap)
    (hεchild:0<εchild)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hbetaTop:HeckeZeroSupremum.beta≤7/8)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0< lower)(hupper:1≤ upper)
    (ha0:0< a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤ highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤ Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0< sigma)(hξsmall:ξ≤ sigma/4)(hcost:1≤ cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0< Cbound ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤(Cycle25.Energy.commonMesh Mcap 0 L εchild)) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤ N → lower≤ src.lower → src.upper≤ upper →
    0≤ src.b₁ → 0≤ src.b₂ → src.b₁≤ max 1 b → src.b₂≤ max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0< K → 0< asource →
    0≤ delta → 0≤ reserve → a0≤ asource →
    ∀ prime : O, Prime (Ideal.span {prime}) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀ family : Fin 3 → RayCharacter → Character,
    (∀ i χ, (family i χ).modulus.absNorm≤ CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i))) →
    (∀ i χ, ((family i χ).modulus.absNorm:ℝ)≤
      cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (errorIndex i+1))) →
    let radius := fun i : Fin 3 => errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (errorIndex i+1)
    (∀ (i : Fin 3) (χ : RayCharacter)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools
        ((Ideal.span {prime})^(errorIndex i+1))),
      Ready (errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t)
        ((R0*C)*(Ideal.span {prime})^(errorIndex i+1)) (radius i) Z ξ Bcap) →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤ Z^Bseed →
    ∀profile:Profiles a b,profile.profile 0=src.W₁ → profile.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*(3/4)*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mwidth →
    Mwidth-sigma/2≤ Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤ CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r : Fin 3 → RayCharacter → ℝ,
    (∀ (i : Fin 3) (χ : RayCharacter)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools
        ((Ideal.span {prime})^(errorIndex i+1))),
      let input := errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t
      Z^(r i χ) ≤ input.X₁ ∧ Z^(r i χ) ≤ input.X₂ ∧ Z^(r i χ) ≤ input.Y₁ ∧ Z^(r i χ) ≤ input.Y₂) →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+(3/4)*mesh
    firstExtractedErrors (child src C R0 B τ t) (R0*C) seed Z
      (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime family ≤
      mass (child src C R0 B τ t)^2*
        ∑i : Fin 3, 16*(errorIndex i+2:ℝ)^2*localErrorCost prime (errorIndex i)*
          ∑χ : RayCharacter, ∑j : Fin 4,
            ((Cbound*(profile.control Uprofile)^2*(1+|t|+height)^Jheight*
              Z^(CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/
                (seed.absNorm:ℝ))*
              CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (errorIndex i+1)
                (τ.modulus.absNorm:ℝ) Z (radius i)
                (refinedErrorDeficit prime Z (errorIndex i+1) sigma
                  (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))) paid saving (r i χ) j)*
              (volume (child src C R0 B τ t)/(normValue prime)^(errorIndex i+1))^(powers εsrc j) := by
  obtain ⟨Uprofile,Jheight,hactual⟩ := actual_original_subsets_error_power (α := α) M H hH
    Wslot aslot bslot Mcap εremove lo hi εchild a b Mslot εmask hMslot hεmask haPlain haUpper hbPlain
    L hL ha hWs hW hbslot hMcap hεchild hε hbeta hbetaTop N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hactualZ⟩ := hactual η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cbound,hCbound,?_⟩
  filter_upwards [hactualZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
    C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime hprimeScale hslot family hrad hfamily
  dsimp only
  intro hready seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip
    hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower r hr
  have hzpos : 0 < Z := zero_lt_one.trans hZ.1
  have hp0 : prime ≠ 0 := fun h => hprime.ne_zero (by simp [h])
  apply firstExtractedErrors_power_budget (child src C R0 B τ t) (R0*C) seed Z
    (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime hprime hslot family
  · intro i χ j
    apply mul_nonneg
    · positivity
    · fin_cases j <;>
        simp only [CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
        (try unfold errorCommonRadius) <;> positivity
  · intro i χ Bp
    have hk : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
      fin_cases i <;> norm_num [errorIndex]
    exact hZ.2 Aorig θ w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max
      C D R0 hC hD hCD E B τ t hB hmod K delta reserve asource hK hasource hdelta hreserve haSource
      prime hp0 (errorIndex i) hk hprimeScale hslot Bp (family i χ) χ t (hrad i χ) (hfamily i χ)
      (errorInput src C R0 B τ t (Ideal.span {prime}) (errorIndex i+1) Bp (family i χ) t) rfl
      (hready i χ Bp) seed hseed hseed0 hseedcap profile hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (r i χ) (hr i χ Bp).1 (hr i χ Bp).2.1 (hr i χ Bp).2.2.1 (hr i χ Bp).2.2.2

#print axioms actual_firstExtractedErrors_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.ActualExtractedErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorAssembly ; sha256 fb73dab838fa7460245dbdd7155552bbce573d9b5ba8eef10301f2b26f29f215 -/
section




/-! Four actual error powers at the common reference. The removal entry
keeps its strict local reserve, and the three other entries retain the
source volume and width instead of replacing them by a declared cap. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentFirstMixedAllowance CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentFirstMixedExceptionalLow CenteredMomentFirstMixedDiagonal
open CenteredMomentEnergyFirstHighExceptionalPowers CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyCanonicalAmplifiedColumn RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The exceptional cutoff is `5*M0/6` for the low source, or `M0`
when the actual minimum scale supplies the high-source factor. -/
def refinedErrorExponents (A M0 exceptionalCut paid eps saving delta reserve : ℝ) : Fin 4 → ℝ :=
  ![paid-157/200000,
    A-exceptionalCut+27/1000+5*(delta+reserve)/6,
    A-M0+9/500+delta+reserve+eps*A,
    A-M0+9/500+delta+reserve-saving]

/-- Both source exceptional gates give the same four-entry interface.
Every premise is source geometry; no error or target moment estimate is assumed. -/
theorem actual_refined_error_cores
    (η τ : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (E : Finset (CommonIndex C D))
    (K V Z delta reserve paid eps saving r Mdecl Mwidth exceptionalCut : ℝ)
    (hK : 0 < K) (hV : 0 < V) (hZ : 1 < Z) (heps : 0 ≤ eps)
    (hdef : Mdecl-(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)) ≤ 429/100000)
    (hgate : exceptionalCut=5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ))/6 ∨
      (exceptionalCut=Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ) ∧
       Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ) ≤ Mwidth))
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*activeConductor C D})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (p : O) (hp : p ∈ elementPool (primePool M H Sbad (1/2) 1 (Z^((9/500 : ℝ)/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hlog : 9/2000 ≤ Real.logb Z (normValue p))
    (hr : exceptionalCut=Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ) →
      r=Mwidth/4-Real.logb Z (C.absNorm : ℝ)-errorRemoval p Z k) :
    let M0 := Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)
    let Kerror := errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) K V Z)
      (Real.logb Z (C.absNorm : ℝ)) (9/500) delta reserve p k
    ∀ j : Fin 4,
      errorCores p k (τ.modulus.absNorm : ℝ) V (C.absNorm : ℝ) Z
        (allowance C D Z) Kerror (refinedErrorDeficit p Z k (9/500) (Mdecl-M0))
        paid eps saving r j ≤
      Z^(refinedErrorExponents (Real.logb Z V) M0 exceptionalCut paid eps saving delta reserve j) := by
  dsimp only
  have hpdata := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad _ _ _ Q hQ).2) p hp
  have hp0 := hpdata.1.ne_zero
  have hz : 0 < Z := zero_lt_one.trans hZ
  intro j
  fin_cases j
  · exact refined_error_main_core p hp0 k hk _ V _ Z _ _ _ paid eps saving r
      (norm_pos τ.modulus τ.modulus_ne_bot) hV (norm_pos C hC.1) hZ
      (allowance_nonneg _ _ _) hdef hlog
  · rcases hgate with hcut | ⟨hcut,hwidth⟩
    · have hh := actual_error_exceptional_reference η τ C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) hC hD hCD E rfl
        K V Z 0 (9/500) delta reserve r hZ hmod M H Sbad hbad p hp k hk hK hV
      rw [hcut]
      convert hh using 1 <;> dsimp [errorCores,reference,refinedErrorExponents] <;> ring
    · have hh := actual_error_exceptional_uniform_cap η τ C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E}) hC hD hCD E rfl
        K V Z 0 (9/500) delta reserve Mwidth hZ hmod M H Sbad hbad p hp k hk hK hV hwidth
      rw [hr hcut,hcut]
      convert hh using 1 <;> dsimp [errorCores,reference,refinedErrorExponents] <;> ring
  · exact actual_error_diagonal η τ C D hC hD hCD E K V Z (9/500) delta reserve eps
      hK hV hZ heps hmod p hp0 k hk
  · have hh := actual_error_diagonal η τ C D hC hD hCD E K V Z (9/500) delta reserve 0
      hK hV hZ (by norm_num) hmod p hp0 k hk
    simp only [Real.rpow_zero,mul_one,zero_mul,add_zero] at hh
    have ht := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hz.le (-saving))
    rw [← Real.rpow_add hz] at ht
    convert ht using 1 <;> dsimp [errorCores,reference,refinedErrorExponents] <;> ring

/-- A source-level four-power estimate is summed over the literal extraction
allocations. This is the coefficient shape returned by ActualErrorPower. -/
theorem firstExtractedErrors_refined_power_budget {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (Z d K₀ c delta reserve : ℝ)
    (p : O) (hp : Prime (Ideal.span {p}))
    (hslot : ∀ j, ∀ I ∈ (activeInput s).slots j, IsCoprime (Ideal.span {p}) I)
    (family : Fin 3 → RayCharacter → Character)
    (q deficit paid eps saving : ℝ) (r : Fin 3 → RayCharacter → ℝ)
    (Hcoef : Fin 3 → RayCharacter → Fin 4 → ℝ)
    (hZ : 0 < Z) (hq : 0 ≤ q) (hH : ∀ i χ j, 0 ≤ Hcoef i χ j)
    (hbound : ∀ i χ,
      ∀ B : actualAllocations (activeInput s).pools ((Ideal.span {p})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p})^(errorIndex i+1))
          R seed B (family i χ) s.t ballProfile
          (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1)) ≤
        (∑ j, Hcoef i χ j*errorPowers p (errorIndex i+1) q Z
          (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
          (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid saving (r i χ) j*
          (volume (child (activeInput s) ((Ideal.span {p})^(errorIndex i+1)) R B (family i χ) s.t))^(powers eps j))*
          mass (child (activeInput s) ((Ideal.span {p})^(errorIndex i+1)) R B (family i χ) s.t)^2) :
    firstExtractedErrors s R seed Z d K₀ c (9/500) delta reserve p family ≤
      mass s^2*∑ i : Fin 3, 16*(errorIndex i+2 : ℝ)^2*localErrorCost p (errorIndex i)*
        ∑ χ : RayCharacter, ∑ j : Fin 4,
          Hcoef i χ j*errorPowers p (errorIndex i+1) q Z
            (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
            (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid saving (r i χ) j*
            (volume s/(normValue p)^(errorIndex i+1))^(powers eps j) := by
  apply firstExtractedErrors_power_budget s R seed Z d K₀ c (9/500) delta reserve p hp hslot family
    (fun i χ j => Hcoef i χ j*errorPowers p (errorIndex i+1) q Z
      (errorCommonRadius Z d K₀ c (9/500) delta reserve p (errorIndex i+1))
      (refinedErrorDeficit p Z (errorIndex i+1) (9/500) deficit) paid saving (r i χ) j)
    (powers eps) _ hbound
  intro i χ j
  apply mul_nonneg (hH i χ j)
  exact error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq hZ.le
    (Real.rpow_nonneg hZ.le _) j

#print axioms actual_refined_error_cores
#print axioms firstExtractedErrors_refined_power_budget
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorAssembly -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceMatches ; sha256 8d6c10d4d5631003bf9aa1e771ed581eb956945f4987173249a1d08956e3dfa9 -/
section





/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

section FixedData
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (η : Character) (η₀ : Slot → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (hQM : Q ≤ M)
  (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
  (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH hQM hQη₀ S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

theorem actual_joint_high_source_matches_contribution
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (ηcommon : Character) (hanchor : ∀ j, η₀ j = ηcommon)
    (Wslot : ℝ → ℂ) (hVslot : ∀ j, V j = Wslot)
    (bslot : ℝ) (hBslot : ∀ j, Bprofile j = bslot)
    (Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 < ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hproductLoss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ productLoss)
    (hpopulationLoss : 0 < populationLoss) (hB : 0 ≤ B)
    (hloss : populationLoss+dmax*productLoss ≤ loss)
    (τdetector dmin heightLoss : ℝ) (I : ℕ)
    (hτdetector : 0 < τdetector) (hdmin : 0 < dmin) (hheightLoss : 0 < heightLoss)
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂plain : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂plain) (hW₂ : ContDiff ℝ ∞ W₂)
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧ primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (s : JointReconstructionLabel → CommonSecondKernelLabel Slot)
        (Ds : JointReconstructionLabel → Finset (Ideal O))
        (z : JointReconstructionLabel → O) (t₁ t₂ H₁ H₂ : JointReconstructionLabel → ℝ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < H₁ v ∧ 0 < H₂ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ H₁ v ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ H₂ v) →
      ∀ (parentL parentR : JointReconstructionLabel → JointParentLabel η)
        (NL : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentL v).val (w v).val)
        (NR : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentR v).val (w v).val)
        (punctureL punctureR : JointReconstructionLabel → Ideal O),
      (∀ v, punctureL v ≠ 0) → (∀ v, punctureR v ≠ 0) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent (s v).leftRay)
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.1)))
        (s v).toKernelLabel.frequency (z v) (t₁ v) J =
        CenteredMomentHeckeExpansion.rowWeight (parentL v).val
          (fixedBadMask*idealGenerator (punctureL v)) 1 (w v).val (t₁ v) J) →
      (∀ v ∈ S, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent ((s v).rightRay⁻¹))
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.2)))
        (s v).toKernelLabel.frequency (-(z v)) (t₂ v) J =
        CenteredMomentHeckeExpansion.rowWeight (parentR v).val
          (fixedBadMask*idealGenerator (punctureR v)) 1 (w v).val (t₂ v) J) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NL v).character (punctureL v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NR v).character (punctureR v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, |t₁ v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ ∧ |t₂ v|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux → (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |t₁ v+freq v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ ∧
        |t₂ v+freq v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      (∀ v ∈ S, ∀ q ∈ (s v).activeFullRetainedFiber (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v),
        (s v).fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-c₂+lengthLoss ∧
        (s v).fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-d₂+lengthLoss) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss)*
        (∑ v ∈ S, ∑ D ∈ Ds v, ‖(UniqueFactorizationMonoid.moebius D : ℂ)‖ *
          ((s v).withProjector D).retainedPair (t₁ v) (t₂ v) (z v) (H₁ v) (H₂ v)) ≤
        C*retainedProfileEnvelope S s aSource*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,hdata⟩ := actual_retained_buffered_short_gates
    W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨Cs,hCs,hremove⟩ := survivingBufferedData_remove_short M H V Aprofile Bprofile
    σmin σmax hA hVs (fun j => (hV j).continuous)
  have hCspos : 0 < Cs := zero_lt_one.trans_le hCs
  obtain ⟨τ,ν,orders,N,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_retained_dominated_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV Rwidth dmax ε e κ ηaux σmin σmax
      productLoss populationLoss loss B hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget
      hproductLoss hpopulationLoss hB hloss τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      profileBound (fun k => (hprofile k).le) lo hi fiberLoss hfiberLoss
  refine ⟨profileBound,hprofile,τ,ν,orders,N,C*Cs^2,hν,hντ,hτdet,hheight,horders,
    mul_pos hC (sq_pos_of_pos hCspos),?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ σ freq θ slotWidth aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical parentL parentR NL NR punctureL punctureR
    hpunctureL hpunctureR hplain hmatch hrowL hrowR hscale hprimeScale
    hcondL hcondR hfreq hfour htwo hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ hlength
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  have hslots (v) (hv : v ∈ S) (j) : (s v).input.slots j =
      CenteredMomentPrimeSlot.primePool M H (Bprofile j) ((s v).input.P j) := by
    rw [hBslot]
    exact (matches_high_slot_gates M H hH (s v).input ηcommon (θ v) (slotWidth v)
      (σ v) (freq v) Wslot bslot Z (hmatch v hv)).1 j
  have hνsource (v) (hv : v ∈ S) (j) (J) (hJ : J ∈ (s v).input.slots j) :
      (s v).input.ν j J = idealCoeff (η₀ j).inverse J := by
    rw [hanchor]
    exact (matches_high_slot_gates M H hH (s v).input ηcommon (θ v) (slotWidth v)
      (σ v) (freq v) Wslot bslot Z (hmatch v hv)).2.1 j J hJ
  have hWsource (v) (hv : v ∈ S) (j) :
      (s v).input.W j = shiftedPrimeProfiles V (σ v) (freq v) j := by
    have hVeq : V = fun _ : Slot => Wslot := funext hVslot
    rw [hVeq]
    exact (matches_high_slot_gates M H hH (s v).input ηcommon (θ v) (slotWidth v)
      (σ v) (freq v) Wslot bslot Z (hmatch v hv)).2.2 j
  have hdne : d ≠ 0 := by
    intro hh
    rw [hh,Real.rpow_zero] at hbase
    norm_num at hbase
  apply hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t₁ t₂ H₁ H₂ aSource haSource
    hsourceIntervals hsourceNorm hprojectorNorm hphysical
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ (Cs^2) (sq_nonneg Cs) ?_
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  intro v hv q hq
  have hqLive := (s v).activeFullRetainedFiber_live (Ds v) (t₁ v) (t₂ v) (H₁ v) (H₂ v) (z v) hq
  obtain ⟨DL,DR,hnorm,hlenL,hlenR,hadL,hadR,hscaleL,hscaleR,hzeroL,htL,hbiL,hzeroR,htR,hbiR⟩ := hdata
    (fun J => orders (J ∩ largePrimeSlots Aprofile Bprofile (s v).input.P)) p.lower e
    (by linarith [p.upper_bound]) he'.le M H hH η (w v) (parentL v) (parentR v) (NL v) (NR v)
    (punctureL v) (punctureR v) (hpunctureL v) (hpunctureR v)
    (s v) (Ds v) (z v) (t₁ v) (t₂ v) Z d η₀
    (shiftedPrimeProfiles V (σ v) (freq v)) Aprofile Bprofile i
    Rwidth τ ηaux 0 0 p.height (hplain v hv).1 (hplain v hv).2
    (hslots v hv) (hνsource v hv) (hWsource v hv) (hrowL v hv) (hrowR v hv)
    hZ.1 hdne (lt_of_lt_of_le (by norm_num) hbase) hRw
    (hscale v hv).1 (hscale v hv).2.1 (hscale v hv).2.2.1 (hscale v hv).2.2.2
    (hprimeScale v hv) le_rfl le_rfl (hcondL v hv) (hcondR v hv)
    (hfreq v hv).1 (hfreq v hv).2 hfour htwo
    (by rw [hheightBin]) q hqLive
  let shiftedL := DL.withSlotShifts (σ v) (freq v)
  let shiftedR := DR.withSlotShifts (σ v) (freq v)
  have hvalueL := DL.withSlotShifts_value (fun j => (hzeroL j).1) (fun j => (hzeroL j).2)
    M H η₀ V Bprofile (σ v) (freq v) Z d
  have hvalueR := DR.withSlotShifts_value (fun j => (hzeroR j).1) (fun j => (hzeroR j).2)
    M H η₀ V Bprofile (σ v) (freq v) Z d
  have hadShiftL := DL.withSlotShifts_short_gates M H hH η₀ Rwidth τ ηaux 0 0
    σmin σmax Z d p.height (σ v) (freq v) hadL
    (fun j => hσrange v hv j.val) (fun j => by
      rw [htL,hbiL]
      exact (hslotfreq v hv j.val).1)
  have hadShiftR := DR.withSlotShifts_short_gates M H hH η₀ Rwidth τ ηaux 0 0
    σmin σmax Z d p.height (σ v) (freq v) hadR
    (fun j => hσrange v hv j.val) (fun j => by
      rw [htR,hbiR]
      exact (hslotfreq v hv j.val).2)
  let Tslots := largePrimeSlots Aprofile Bprofile (s v).input.P
  let DL' := shiftedL.restrictSlots Tslots
  let DR' := shiftedR.restrictSlots Tslots
  have hleft := hremove η (w v) orders profileBound p.lower e η₀ (s v).input.P Z d shiftedL
    hscaleL (fun j _ => (hprimeScale v hv j).1)
    (fun j => ⟨(hadShiftL.slots j).2.2.1,(hadShiftL.slots j).2.2.2⟩)
  have hright := hremove η (w v) orders profileBound p.lower e η₀ (s v).input.P Z d shiftedR
    hscaleR (fun j _ => (hprimeScale v hv j).1)
    (fun j => ⟨(hadShiftR.slots j).2.2.1,(hadShiftR.slots j).2.2.2⟩)
  refine ⟨DL',DR',?_,?_,?_,?_,?_⟩
  · rw [hnorm,← hvalueL,← hvalueR]
    exact (mul_le_mul hleft hright (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left
      (shiftedL.restrictSlots_length_le Tslots (fun j => (hadShiftL.slots j).1)) hd).trans
        (hlenL.trans (hlength v hv q hq).1)
  · exact (mul_le_mul_of_nonneg_left
      (shiftedR.restrictSlots_length_le Tslots (fun j => (hadShiftR.slots j).1)) hd).trans
        (hlenR.trans (hlength v hv q hq).2)
  · exact shiftedL.restrict_large_admissible M H hH η₀ Aprofile Bprofile (s v).input.P
      Rwidth τ ηaux σmin σmax Z d p.height hscaleL hadShiftL
  · exact shiftedR.restrict_large_admissible M H hH η₀ Aprofile Bprofile (s v).input.P
      Rwidth τ ηaux σmin σmax Z d p.height hscaleR hadShiftR

end FixedData
#print axioms actual_joint_high_source_matches_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceMatches -/
