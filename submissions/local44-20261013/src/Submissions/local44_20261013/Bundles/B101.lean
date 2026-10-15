/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B034
import Submissions.local44_20261013.Bundles.B084
import Submissions.local44_20261013.Bundles.B085
import Submissions.local44_20261013.Bundles.B091
import Submissions.local44_20261013.Bundles.B096
import Submissions.local44_20261013.Bundles.B099
import Submissions.local44_20261013.Bundles.B100
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowWindowBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceSupport

/- BEGIN ORIGINAL MODULE Global.Low.Detector.LowWindowBound ; sha256 c0dfeedd93b446daf209d6c8d836d57a2e0a202acba2ce2f840323ea2ff1c8a5 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Detector.LowWindowBound.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

noncomputable section
open scoped Classical ContDiff
namespace LowProbe
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma compensatedPhysicalProbe_window_scale {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) (c : ℂ) :
    compensatedPhysicalProbe η C W0 W1 slots (fun i x=> c*W i x) Yp X Y Z=
      c^K*compensatedPhysicalProbe η C W0 W1 slots W Yp X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc]
  exact (Finset.mul_sum ..).symm

theorem original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤ Submission20261012.Global.ell) (R : Set Id)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤ B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤ C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss) := by
  let D := max 1 B
  have hD : 0< D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=> W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have heloss : 256*ε≤ loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];linarith
  intro η
  obtain ⟨C,hC,hbound⟩ := original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=> Z^(ell i))
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤ D^K*(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤ D^K*(C*Z^((Submission20261012.Global.signal Submission20261012.Global.theta)+loss)) := by gcongr
    _=_ := by ring

end LowProbe
end

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Detector.LowWindowBound -/

/- BEGIN ORIGINAL MODULE Analytic.JointActualErrorAdmission ; sha256 02c9e331da23e49c613e8163f5dda3711158a1b8a47ce60424abea53b9305bcc -/
section




/-! Source admission for the exact error family selected by coherent
amplification. All remaining gates are source support or scalar geometry. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstAnnularInput CenteredMomentFirstScale CenteredMomentFirstPhysicalSource
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows RayFourExpansion
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CompletedGauss
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstMixedAllowance CenteredMomentRankinRadical CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance actualErrorAdmissionDecidableSum : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def actualAmplifierErrorRun (s : Input ι) (C : Ideal O) (P : Finset (Ideal O))
    (τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character)
    (parent : Character) (t : ℝ) : ExtractedErrorRun s C P where
  height := t
  family := fun B => τ (liveIndices B.val) parent

theorem actual_nominal_log_lower
    (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (hE : E ≠ 0)
    (K V Z BC BD BK : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 1 ≤ V)
    (hCcap : (C.absNorm : ℝ) ≤ Z^BC) (hDcap : (D.absNorm : ℝ) ≤ Z^BD) (hKcap : K ≤ Z^BK) :
    -(BC+BD+BK) ≤ nominalLog C D E K V Z := by
  have hz := zero_lt_one.trans hZ
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  have hv := zero_lt_one.trans_le hV
  have hcl := Real.logb_le_logb_of_le hZ hc hCcap
  have hdl := Real.logb_le_logb_of_le hZ hd hDcap
  have hkl := Real.logb_le_logb_of_le hZ hK hKcap
  rw [Real.logb_rpow hz hZ.ne'] at hcl hdl hkl
  have hvl := Real.logb_nonneg hZ hV
  have hel : 0 ≤ Real.logb Z (E.absNorm : ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hrl : 0 ≤ Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hr)
  rw [nominalLog,firstNominalScale,commonPart_of_equal_support C D hC.1 hCD,
    commonPart_of_equal_support D C hD.1 hCD.symm]
  simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow]
  norm_num only
  linarith

theorem actual_error_radius_inverse
    (C D E : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (hE : E ≠ 0)
    (K V Z BC BD BK sigma delta reserve Dscale : ℝ) (hZ : 1 < Z) (hK : 0 < K) (hV : 1 ≤ V)
    (hCcap : (C.absNorm : ℝ) ≤ Z^BC) (hDcap : (D.absNorm : ℝ) ≤ Z^BD) (hKcap : K ≤ Z^BK)
    (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta) (hreserve : 0 ≤ reserve)
    (hbudget : BC+BD+BK ≤ Dscale) (p : O) (k : ℕ) :
    (errorCommonRadius Z (Real.logb Z (D.absNorm : ℝ)) (nominalLog C D E K V Z)
      (Real.logb Z (C.absNorm : ℝ)) sigma delta reserve p k)⁻¹ ≤ Z^Dscale := by
  have hn := actual_nominal_log_lower C D E hC hD hCD hE K V Z BC BD BK hZ hK hV hCcap hDcap hKcap
  unfold errorCommonRadius
  rw [←Real.rpow_neg (zero_lt_one.trans hZ).le]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hm := le_max_right (Real.logb Z (D.absNorm : ℝ)-Real.logb Z (C.absNorm : ℝ)-
    2*errorRemoval p Z k+errorMoving p Z k) (0 : ℝ)
  linarith

theorem actual_allocated_slot_coprime
    (P : Finset (Ideal O)) (hP : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (s : Input ι) (C R : Ideal O) (parent : Character) (t Z sigma b eta : ℝ)
    (hZ : 1 < Z) (hb : 0 ≤ b) (hsep : b*Z^eta < Z^(sigma/6))
    (hpl : ∀ Q ∈ P, Z^(sigma/6) ≤ (Q.absNorm : ℝ)) (hupper : s.upper ≤ b)
    (z : ι → ℝ) (hz : ∀ i,z i ≤ eta) (hlen : ∀ i,s.P i = Z^(z i))
    (B : actualAllocations s.pools C) (p : elementPool P) :
    ∀ i, ∀ I ∈ (activeInput (child s C R B parent t)).slots i,
      IsCoprime (Ideal.span {p.val}) I := by
  let c := child s C R B parent t
  have hd := elementPool_data P hP hbad p.val p.property
  exact original_slot_coprime (original c (R*C) 1).active Z sigma b eta hZ.le hb hsep
    (fun i => z i.val) (fun i => hz i.val) (fun i => hlen i.val)
    (fun i y hy => (s.slot_support i.val hy).2.trans hupper)
    (original c (R*C) 1).active_slot
    (fun i I hI => c.prime i I ((original c (R*C) 1).active_subset _ hI))
    (Ideal.span {p.val}) (hP _ hd.2.1) (hpl _ hd.2.1)

theorem actual_amplifier_error_source_admissible
    (P : Finset (Ideal O)) (hP : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P, Q ∉ fixedBadPrimes)
    (τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character)
    (hτ : ∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
      radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i)))
    (s : Input ι) (C D R : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (E : Finset (CommonIndex C D))
    (parent : Character) (t Z K sigma delta reserve Dscale heightCap b eta BC BD BK : ℝ)
    (hZ : 1 < Z) (hK : 0 < K) (hvolume : 1 ≤ volume s) (ht : |t| ≤ heightCap)
    (hb : 0 ≤ b) (hupper : s.upper ≤ b) (hsep : b*Z^eta < Z^(sigma/6))
    (hpl : ∀ Q ∈ P, Z^(sigma/6) ≤ (Q.absNorm : ℝ))
    (z : ι → ℝ) (hz : ∀ i,z i ≤ eta) (hlen : ∀ i,s.P i = Z^(z i))
    (hCcap : (C.absNorm : ℝ) ≤ Z^BC) (hDcap : (D.absNorm : ℝ) ≤ Z^BD) (hKcap : K ≤ Z^BK)
    (hsigma : 0 ≤ sigma) (hdelta : 0 ≤ delta) (hreserve : 0 ≤ reserve)
    (hbudget : BC+BD+BK ≤ Dscale) :
    (actualAmplifierErrorRun s C P τ parent t).SourceAdmissible D R E parent
      Z K sigma delta reserve Dscale heightCap := by
  refine ⟨ht,?_,?_,?_⟩
  · intro B hB p
    exact actual_allocated_slot_coprime P hP hbad s C R parent t Z sigma b eta hZ hb hsep hpl hupper z hz hlen B p
  · intro B hB p i χ
    exact_mod_cast hτ (liveIndices B.val) parent p i χ
  · intro p i
    exact actual_error_radius_inverse C D _ hC hD hCD
      (Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _))
      K (volume s) Z BC BD BK sigma delta reserve Dscale hZ hK hvolume hCcap hDcap hKcap
      hsigma hdelta hreserve hbudget p.val (errorIndex i+1)

/-- The same annular prime pool used by the coherent amplifier supplies
all admission gates uniformly before the source and its allocations. -/
theorem eventually_actual_amplifier_error_source_admissible
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ Sbad)
    (sigma b eta : ℝ) (hsigma : 0 < sigma) (hb : 0 ≤ b) (hgap : eta < sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
    ∀ (τ : (J : Finset ι) → Character → elementPool P → Fin 3 → RayCharacter → Character),
    (∀ J η (p : elementPool P) i χ, ((τ J η p i χ).modulus.absNorm : ℝ) ≤
      radicalBound (childCharacter η χ) fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
    ∀ (s : Input ι) (C D R : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C = primeSupport D → ∀ E : Finset (CommonIndex C D),
    ∀ (parent : Character) (t K delta reserve Dscale heightCap BC BD BK : ℝ),
    0 < K → 1 ≤ volume s → |t| ≤ heightCap → s.upper ≤ b →
    ∀ (z : ι → ℝ), (∀ i,z i ≤ eta) → (∀ i,s.P i = Z^(z i)) →
    (C.absNorm : ℝ) ≤ Z^BC → (D.absNorm : ℝ) ≤ Z^BD → K ≤ Z^BK →
    0 ≤ delta → 0 ≤ reserve → BC+BD+BK ≤ Dscale →
    (actualAmplifierErrorRun s C P τ parent t).SourceAdmissible D R E parent
      Z K sigma delta reserve Dscale heightCap := by
  have hgap' : eta < (sigma/3)/2 := by linarith
  filter_upwards [eventually_actual_pool M H hH Sbad hbad (sigma/3) 1 0 b eta
    (by positivity) (by norm_num) hgap'] with Z hZ
  obtain ⟨hZ,hP,hcard,hlarge,hsep,hdata⟩ := hZ
  refine ⟨hZ,?_⟩
  dsimp only
  intro τ hτ s C D R hC hD hCD E parent t K delta reserve Dscale heightCap BC BD BK
    hK hvolume ht hupper z hz hlen hCcap hDcap hKcap hdelta hreserve hbudget
  have he : (sigma/3)/2 = sigma/6 := by ring
  rw [he] at hsep
  exact actual_amplifier_error_source_admissible _ (fun Q hQ => (hdata Q hQ).1)
    (fun Q hQ => (hdata Q hQ).2.1) τ hτ s C D R hC hD hCD E parent t Z K sigma delta reserve
    Dscale heightCap b eta BC BD BK hZ hK hvolume ht hb hupper hsep
    (fun Q hQ => by simpa only [he] using (hdata Q hQ).2.2.1)
    z hz hlen hCcap hDcap hKcap hsigma.le hdelta hreserve hbudget


#print axioms actual_amplifier_error_source_admissible
#print axioms eventually_actual_amplifier_error_source_admissible
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointActualErrorAdmission -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentExceptionalPhysical ; sha256 47de6b4b0adcd6c49421e6c4b5823a21a50093671d66d11bfe17e3edf8039963 -/
section


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource CenteredMomentCommonSectorColumn
open CenteredMomentCommonLinearSource CenteredMomentCommonHeightEnvelope CenteredMomentReflectedSource
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentActiveSource CenteredMomentSecondRetainedAggregate CenteredMomentSourceRow
open CenteredMomentSecondBlockAggregate CenteredMomentSecondSectorColumns
open CenteredMomentRowNorm CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentSecondScaled CenteredMomentSecondHeightFamily CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFiniteProfileExceptionalCommon CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonExceptionalCost CenteredMomentExceptionalAmplitudePair
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSectorLocalization
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentChildRows CenteredMomentForcing
open CenteredMomentFirstSectors
open CenteredMomentSecondPhysicalLedger CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondExceptionalKernel CenteredMomentMobiusRegroup CenteredMomentFixedRay
open RayFourExpansion UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O
local instance coherentExceptionalPhysicalDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_coherent_exceptional_physical_scalar
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi) (lo hi : ι → ℝ)
    (ε δ θ B Lbound : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hθ : 0 < θ)
    (hB : 0 ≤ B) (hL : 0 ≤ Lbound) (W : 𝓢(ℝ,ℂ)) :
    ∃ J : ℕ, ∃ Sprofile : Finset (ℕ×ℕ), (0,0) ∈ Sprofile ∧
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} → ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (profile : Profiles wlo whi),
    (∀ i, src.lo i = lo i) → (∀ i, src.hi i = hi i) → (∀ i, 1 ≤ src.P i) →
    src.W₁ = profile.profile 0 → src.W₂ = profile.profile 1 →
    ∀ (R seed C₁ L₁ : Ideal O) (hC₁ : Supported C₁), R ≠ 0 → ∀ hseed : seed ∣ C₁,
    ∀ p : ActiveLabel (commonSecondColumns (original src R seed) C₁ hC₁)
      (commonSecondBeta (original src R seed) C₁ L₁),
    ∀ (η : Character) (U : Finset (CommonIndex p.val.1 p.val.2))
      (family : RayCharacter → Character),
    Family η p.val.1 p.val.2 (lowActiveLeftSupported p) (lowActiveRightSupported p) U family →
    ∀ (χ₀ : RayCharacter) (t Kphys Radius r P : ℝ) (n : Fin 4 → ℤ), 0 < Kphys → 0 < P →
    Z^r ≤ src.X₁ → Z^r ≤ src.X₂ → Z^r ≤ src.Y₁ → Z^r ≤ src.Y₂ →
    idealCoeff η p.val.1 ≠ 0 →
    ∀ m : O, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ₀) Q m
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U) z) →
    (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ dyadicScale (n 1)) →
    (∀ χ : RayCharacter, ∀ z ∈ rows, ((family χ).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.1).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ χ : RayCharacter, ∀ z ∈ rows, ((reflected (family χ)).modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*(C₁*p.val.2).absNorm)*(Ideal.span {z}).absNorm : ℝ) ≤ Z^B) →
    (∀ L ∈ divisorPool Finset.univ (fun I : sectorPool p.val.2 (lowActiveRightSupported p).1
        (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
          (commonSecondBeta (original src R seed) C₁ L₁)) => (I : Ideal O)),
      (moebius L : ℂ) ≠ 0 → (L.absNorm : ℝ) ≤ Z^Lbound) →
    ‖physicalBlock η t
      (activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
        (commonSecondBeta (original src R seed) C₁ L₁))
      (commonSecondBeta (original src R seed) C₁ L₁) p.val.1 p.val.2
      (lowActiveLeftSupported p) (lowActiveRightSupported p) U Radius rows W Kphys n‖/
      (volume src.toData*P) ≤
    (256*Ckernel)*coherentExceptionalProfile Sprofile src profile J Q K t*
      Z^(2*ε+δ-max (max (r-Real.logb Z ((C₁*p.val.1).absNorm : ℝ)) 0)
        (max (r-Real.logb Z ((C₁*p.val.2).absNorm : ℝ)) 0))*
      (((C₁*p.val.1).absNorm : ℝ)*(C₁*p.val.2).absNorm)^θ*
      coherentExceptionalScalar (volume src.toData) P (C₁.absNorm : ℝ) p.val.1 p.val.2 U Kphys n := by
  obtain ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,hbound⟩ := actual_coherent_exceptional_kernel
    wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL W 1
  refine ⟨J,Sprofile,hSprofile,Ckernel,hCkernel,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
    p η U family hfamily χ₀ t Kphys Radius r P n hKphys hPcount hX₁ hX₂ hY₁ hY₂ hη m hm hml hm2
    rows hn hex hN hcondL hcondR hDs
  let S := activeSource (commonSecondColumns (original src R seed) C₁ hC₁)
    (commonSecondBeta (original src R seed) C₁ L₁)
  let β := commonSecondBeta (original src R seed) C₁ L₁
  let Ds := divisorPool Finset.univ (fun I : sectorPool p.val.2 (lowActiveRightSupported p).1 S => (I : Ideal O))
  have hCD := (commonLabels_data _ _ _ _ p.property).2.2
  let E := coherentExceptionalKernelBudget Sprofile src profile J Q C₁ p.val.1 p.val.2 U K Z ε δ θ r t n
  have hE : 0 ≤ E := coherentExceptionalKernelBudget_nonneg Sprofile src profile J Q C₁
    p.val.1 p.val.2 U K Z ε δ θ r t n hK.le (zero_lt_one.trans hZ.1)
  have hk (χ ξ : RayCharacter) :
      (∑ L ∈ Ds, ∑ z ∈ rows, ‖((1+SecondKernelLabel.kernelScale n : ℝ) : ℂ)*(moebius L : ℂ)*
        (projectedSecondKernelLabel η S β p.val.1 p.val.2 (lowActiveLeftSupported p)
          (lowActiveRightSupported p) hCD U L χ ξ).kernelRow t z W Kphys Radius n‖) ≤ Ckernel*E := by
    have hexχ := (exceptional_rows_pair η χ₀ χ ξ Q hQ72 m
      (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U)
      hml hm2 rows hex).1
    have hN' (z : O) (hz : z ∈ rows) :
        ((Ideal.span {z}).absNorm : ℝ) ≤ 1*Z^(Real.logb Z (dyadicScale (n 1))) := by
      rw [one_mul,Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' (dyadicScale_pos _)]
      exact hN z hz
    have hh := hZ.2 src profile hlo hhi hP hW₁ hW₂ R seed C₁ L₁ hC₁ hR hseed
      p η U family hfamily χ (ξ⁻¹) t Kphys Radius r n hX₁ hX₂ hY₁ hY₂
      hη m hm hml hm2 rows hn hexχ 1 (Real.logb Z (dyadicScale (n 1)))
      (by norm_num) hN' (hcondL χ) (hcondR (ξ⁻¹)) Ds hDs
    simpa only [E,coherentExceptionalKernelBudget,forcingNorm,pow_one,Real.one_rpow,mul_one,
      coherentProjectorKernel,CommonSecondKernelLabel.toKernelLabel,projectedSecondKernelLabel,
      S,β,inv_inv,profileMass,withHeight,slotControl,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hb := projectedSecondKernelSum_weighted_norm_le η t S β p.val.1 p.val.2
    (lowActiveLeftSupported p) (lowActiveRightSupported p) hCD U Radius rows W Kphys n
    (Ckernel*E) (mul_nonneg hCkernel hE) hk
  have hv := CenteredMomentExceptionalAmplitudePair.volume_pos src.toData
  have hp := secondPrecountFactor_pos (volume src.toData) P hv hPcount p.val.1 p.val.2
    (lowActiveLeftSupported p) (lowActiveRightSupported p) U Kphys hKphys n
  have hscale : 0 < 1+SecondKernelLabel.kernelScale n := by
    exact add_pos zero_lt_one (div_pos
      (mul_pos (dyadicScale_pos _) (dyadicScale_pos _))
      (mul_pos (dyadicScale_pos _) (dyadicScale_pos _)))
  have hb' := (le_div_iff₀ hscale).mpr (by simpa only [mul_comm] using hb)
  rw [actual_physicalBlock_kernel_precount η t S β p.val.1 p.val.2
    (lowActiveLeftSupported p) (lowActiveRightSupported p) hCD U Radius rows hn W Kphys hKphys n]
  apply (mul_le_mul_of_nonneg_left hb' hp.le).trans_eq
  calc
    _ = (256*Ckernel)*(secondPrecountFactor (volume src.toData) P p.val.1 p.val.2 U Kphys n*E/
        (1+SecondKernelLabel.kernelScale n)) := by ring
    _ = _ := by
      rw [coherent_exceptional_kernel_scalar Sprofile src profile J Q C₁ p.val.1 p.val.2
        (lowActiveLeftSupported p) U K Z ε δ θ r t P Kphys n hZ.1]
      ring

#print axioms actual_coherent_exceptional_physical_scalar
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentExceptionalPhysical -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstLiveSource ; sha256 668ea6db463c6ac93dca35aabb3acbf6ce148af36b7fa1ed6b9b27e75da2cf30 -/
section




/-! Removing zero first physical blocks is exact. Every remaining
block supplies the two lower column scales required by the first kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData ConcreteTraceCRT
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildInput
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentCanonicalFirst
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentSecondRetainedRows
open CenteredMomentSectorLocalization CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstScale CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def firstPhysicalValue (src : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (t : FirstSourceOuterIndex src R seed K radius → ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (i : FirstSourceOuterIndex src R seed K radius) : ℂ :=
  (firstSourceOuterLabel src R seed K radius i).sourceBlock (t i)
    (retainedRows (radius i.1 i.2.1.val) 1) W V K
    (dyadicScale (i.2.2 0)) (dyadicScale (i.2.2 1))
    (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))

def firstLiveSourceLabels (src : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed K radius))
    (t : FirstSourceOuterIndex src R seed K radius → ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) :=
  labels.filter (fun i => firstPhysicalValue src R seed K radius t W V i ≠ 0)

theorem first_physical_sum_live (src : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed K radius))
    (t : FirstSourceOuterIndex src R seed K radius → ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (weight : FirstSourceOuterIndex src R seed K radius → ℂ) :
    (∑ i ∈ labels,weight i*firstPhysicalValue src R seed K radius t W V i) =
    ∑ i ∈ firstLiveSourceLabels src R seed K radius labels t W V,
      weight i*firstPhysicalValue src R seed K radius t W V i := by
  rw [firstLiveSourceLabels,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with h
  · rfl
  · simp only [not_not] at h
    simp only [h,mul_zero]

theorem first_live_source_lower_dyads (src : Input ι) (R seed : Ideal O) (K : ℝ)
    (radius : (p : Labels src R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ)
    (labels : Finset (FirstSourceOuterIndex src R seed K radius))
    (t : FirstSourceOuterIndex src R seed K radius → ℝ)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (a₁ a₂ window : ℝ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hs₁ : ∀ x,src.W₁ x ≠ 0 → a₁ ≤ x) (hs₂ : ∀ x,src.W₂ x ≠ 0 → a₂ ≤ x)
    (hwin : ∀ j y,V j y ≠ 0 → |y| ≤ window)
    (i : FirstSourceOuterIndex src R seed K radius)
    (hi : i ∈ firstLiveSourceLabels src R seed K radius labels t W V) :
    let q := firstSourceOuterLabel src R seed K radius i
    originalLowerProfile src a₁ a₂*volume src.toData ≤
      (q.C.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 2) ∧
    originalLowerProfile src a₁ a₂*volume src.toData ≤
      (q.D.absNorm : ℝ)*Real.exp window*dyadicScale (i.2.2 3) := by
  intro q
  have hn := (Finset.mem_filter.mp hi).2
  have hsource (I) (hI : q.data.beta I ≠ 0) :
      originalLowerProfile src a₁ a₂*volume src.toData ≤ (I.absNorm : ℝ) :=
    original_column_lower src R seed I a₁ a₂ ha₁ ha₂ hs₁ hs₂ hI
  exact CenteredMomentFirstPhysicalSourceSupport.block_reference_lower
    q.parent (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator q.data.R) 1 (t i)
    q.data.columns q.data.beta q.C q.D q.hC q.hD q.E
    (retainedRows (radius i.1 i.2.1.val) 1) W V K
    (dyadicScale (i.2.2 0)) (dyadicScale (i.2.2 1))
    (dyadicScale (i.2.2 2)) (dyadicScale (i.2.2 3))
    (originalLowerProfile src a₁ a₂) (volume src.toData) window
    (dyadicScale_pos _) (dyadicScale_pos _) hsource hwin hn

#print axioms first_physical_sum_live
#print axioms first_live_source_lower_dyads
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstLiveSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOuterMass ; sha256 da00b6f7d6e536ad8ae32c4fe8b882f46e7963e3ebc34c6c997bb70fbba98dd8 -/
section


/-! The sharp first outer count comes from the actual common radical
mass, including all inactive subsets and literal dyadic blocks. This
is the count paired with the independent extracted-error reference. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCanonicalFirst
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstPhysicalDyadicCount CenteredMomentFirstDiscardedEnergy
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentSecondRetainedAggregate CenteredMomentRankinRadical
open CenteredMomentSecondBlockRadicalHarmonicMass
local notation "O" => HeckeFamily.O
local instance firstOuterMassDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_first_outer_radical_mass (B L Cr ε : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
    Squarefree seed → seed ≠ 0 → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (K : ℝ), 0 < K →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    (∑ i : FirstSourceOuterIndex s R seed K radius,
      1/((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ)) ≤ C*Z^ε/(seed.absNorm : ℝ) := by
  obtain ⟨Cm,hCm,hm⟩ := actual_active_radical_mass B (ε/2) hB (by positivity)
  obtain ⟨Cd,hCd,hd⟩ := original_blocks_subpower B L Cr (ε/2) hB hL hCr (by positivity)
  refine ⟨Cd*Cm,mul_pos hCd hCm,?_⟩
  filter_upwards [hd,eventually_ge_atTop (2:ℝ)] with Z hd hZ
  refine ⟨lt_of_lt_of_le (by norm_num) hZ,?_⟩
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hsource K hK radius hr
  have hz : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hmass := hm Z hZ seed hs hs0 (finiteColumns (Fintype.piFinset s.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
    (fun I _ hI => original_column_mask s R seed I hI)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2.trans hsource)
  have hp (p : Labels s R seed) := commonLabels_supported
    (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
  change (∑ i : FirstSourceOuterIndex s R seed K radius,
    radicalWeight i.1.val.1 i.1.val.2) ≤ _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_sigma,Nat.cast_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ p : Labels s R seed, ∑ _E : ↥(inactiveSubsets p.val.1 p.val.2),
        (Cd*Z^(ε/2))*radicalWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp'
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right
        (hd p.val.1 p.val.2 (hp p).1.1 (hp p).2.1 E.val K (radius p E.val)
          (sourceRadius s) hK hH (hr p E.val) hsource) (radicalWeight_nonneg _ _)
    _ ≤ ∑ p : Labels s R seed, ∑ _E : Finset (CommonIndex p.val.1 p.val.2),
        (Cd*Z^(ε/2))*radicalWeight p.val.1 p.val.2 := by
      apply Finset.sum_le_sum
      intro p hp'
      rw [Finset.sum_coe_sort (inactiveSubsets p.val.1 p.val.2)
        (fun _ => (Cd*Z^(ε/2))*radicalWeight p.val.1 p.val.2)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => mul_nonneg (by positivity) (radicalWeight_nonneg _ _))
    _ = (Cd*Z^(ε/2))*(∑ p : Labels s R seed, ∑ _E : Finset (CommonIndex p.val.1 p.val.2),
        radicalWeight p.val.1 p.val.2) := by simp only [Finset.mul_sum]
    _ ≤ (Cd*Z^(ε/2))*(Cm*Z^(ε/2)/(seed.absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cd*Cm)*(Z^(ε/2)*Z^(ε/2))/(seed.absNorm : ℝ) := by ring
    _ = _ := by rw [←Real.rpow_add hz,add_halves]

theorem actual_first_outer_sector_count (B L Cr ε : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
    Squarefree seed → seed ≠ 0 → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (K : ℝ), 0 < K →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    ∀ (labels : Finset (FirstSourceOuterIndex s R seed K radius)) (p : ℝ),
    (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    (labels.card : ℝ) ≤ C*Z^(p+ε)/(seed.absNorm : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := actual_first_outer_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hsource K hK radius hr labels p hp
  have hh := hZ.2 ι s R seed hs hs0 hz₁ hz₂ hH hsource K hK radius hr
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  calc
    _ = ∑ _i ∈ labels, (1:ℝ) := by simp
    _ ≤ ∑ i ∈ labels, Z^p*(1/((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hn := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero i.1.val.1 i.1.val.2)
      simpa only [mul_one_div] using (one_le_div hn).mpr (hp i hi)
    _ = Z^p*(∑ i ∈ labels, 1/((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ Z^p*(∑ i : FirstSourceOuterIndex s R seed K radius,
        1/((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by positivity)) (by positivity)
    _ ≤ Z^p*(C*Z^ε/(seed.absNorm : ℝ)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [Real.rpow_add hz]; ring

/-- The actual first source measure: sharp common-sector count and harmonic
projectors. Both ray labels are included in the fixed constant. -/
theorem actual_first_source_sector_harmonic_mass (B L Cr ε : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hCr : 0 < Cr) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (s : Input ι) (R seed : Ideal O),
    Squarefree seed → seed ≠ 0 → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
    0 < sourceRadius s → sourceRadius s ≤ Z^B →
    ∀ (K : ℝ), 0 < K →
    ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
    (∀ p E, radius p E ≤ Cr*Z^L) →
    ∀ (labels : Finset (FirstSourceOuterIndex s R seed K radius)) (p : ℝ),
    (∀ i ∈ labels, ((commonRadical i.1.val.1 i.1.val.2).absNorm : ℝ) ≤ Z^p) →
    (∑ k ∈ firstLeftSourceLabels labels (firstSourceOuterLabel s R seed K radius)
      (fun _ => sourceRadius s), 1/((k.2.1.val).absNorm : ℝ)) ≤
        C*Z^(p+ε)/(seed.absNorm : ℝ) ∧
    (∑ k ∈ firstRightSourceLabels labels (firstSourceOuterLabel s R seed K radius)
      (fun _ => sourceRadius s), 1/((k.2.1.val).absNorm : ℝ)) ≤
        C*Z^(p+ε)/(seed.absNorm : ℝ) := by
  obtain ⟨Co,hCo,ho⟩ := actual_first_outer_sector_count B L Cr (ε/2) hB hL hCr (by positivity)
  obtain ⟨Cp,hCp,hp⟩ := actual_first_supported_label_harmonic_mass B (ε/2) hB (by positivity)
  refine ⟨Cp*Co,mul_pos hCp hCo,?_⟩
  filter_upwards [ho,hp] with Z hZo hZp
  refine ⟨hZo.1,?_⟩
  intro ι _ _ s R seed hs hs0 hz₁ hz₂ hH hsource K hK radius hr labels p hrad
  have hc := hZo.2 ι s R seed hs hs0 hz₁ hz₂ hH hsource K hK radius hr labels p hrad
  have hh := hZp.2 labels (firstSourceOuterLabel s R seed K radius)
    (fun _ => sourceRadius s) (fun _ _ => hsource)
  have he : Cp*Z^(ε/2)*(Co*Z^(p+ε/2)/(seed.absNorm : ℝ)) =
      (Cp*Co)*Z^(p+ε)/(seed.absNorm : ℝ) := by
    calc
      _ = (Cp*Co)*(Z^(ε/2)*Z^(p+ε/2))/(seed.absNorm : ℝ) := by ring
      _ = _ := by rw [←Real.rpow_add (zero_lt_one.trans hZo.1)]; congr 3 <;> ring
  have hz : 0 < Z := zero_lt_one.trans hZo.1
  have hcap := (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ Cp*Z^(ε/2))).trans_eq he
  exact ⟨hh.1.trans hcap,hh.2.trans hcap⟩

#print axioms actual_first_outer_radical_mass
#print axioms actual_first_outer_sector_count
#print axioms actual_first_source_sector_harmonic_mass
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOuterMass -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighSourceOriginal ; sha256 220bb4b34fa970334e733677256996f5c38943241f2297c6b8ea3a23b943f09f -/
section





/-! The actual high physical estimate on the literal nested source indices.
Canonical rows, units and source transports are constructed by the embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization HeckeDetectorDyadicGeometry
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput RayFourExpansion
open NonzeroJointSourceRow
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

theorem actual_joint_high_source_original_volume
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
    (lo hi : Slot → ℝ) (fiberLoss : ℝ) (hfiberLoss : 0 < fiberLoss)
    (aSource Mslot upper : ℝ) (haSource : 0 < aSource) (hMslot : 0 ≤ Mslot)
    (conductorReserve : ℝ) (hconductorReserve : 0 < conductorReserve)
    (Sbad : Finset (Ideal O)) (primeLoss : ℝ) (hprimeLoss : 0 < primeLoss)
    (hprimeReserve : primeLoss ≤ 144011/219600000)
    (Wkernel : 𝓢(ℝ,ℂ))
    (tailA targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (d P W : ℝ), dmin ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ → P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (input : Input Slot) (puncture seed : Ideal O)
        (hpuncture : puncture ≠ 0) (hseed : Squarefree seed)
        (hz₁ : input.W₁ 0 = 0) (hz₂ : input.W₂ 0 = 0)
        (side : Bool) (ξ₁ ξ₂ : RayCharacter)
        (fallback : NonzeroJointSourceRow (original input puncture seed) side)
        (qs : Finset (NonzeroJointSourceRow (original input puncture seed) side)),
      let S := qs.image NonzeroJointSourceRow.label
      let unit := sourceUnit fallback η ξ₁ ξ₂
      let w := sourceRow fallback η ξ₁ ξ₂
      let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
      let first := sourceFirst fallback η ξ₁ ξ₂
      let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
      let Ds := fun v => (s v).physicalProjectors
      let rayWeight := fun v => (s v).physicalRayWeight
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ q ∈ qs, Squarefree q.val.L) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (t K Radius tbase firstU firstTheta : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ),
      (∀ v ∈ S, (∀ j, (s v).input.M j ≤ Mslot) ∧ (s v).input.upper ≤ upper ∧
        (s v).input.b₁ ≤ b₁ ∧ (s v).input.b₂ ≤ b₂plain) →
      (∀ v ∈ S, (∀ j, (s v).input.lo j = lo j) ∧ (∀ j, (s v).input.hi j = hi j)) →
      (∀ v ∈ S, (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ Z^(2*B) ∧
        (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, ∀ L ∈ Ds v, (UniqueFactorizationMonoid.moebius L : ℂ) ≠ 0 →
        (L.absNorm : ℝ) ≤ Z^(2*B)) →
      (∀ v ∈ S, 0 < dyadicScale (n v 2) ∧ 0 < dyadicScale (n v 3) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ≤ dyadicScale (n v 2) ∧
        aSource*CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData/
          (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ) ≤ dyadicScale (n v 3)) →
      ∀ Bmask : ℝ, W+Bmask+conductorReserve ≤ d →
      (∀ v ∈ S, (((first v).leftPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask ∧
        (((first v).rightPuncture (s v)).radical.absNorm : ℝ) ≤ Z^Bmask) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, t v = tbase v+2*Real.pi*(firstU v-firstTheta v)) →
      (∀ v ∈ S, |tbase v| ≤ Z^ν ∧ |firstU v| ≤ Z^ν ∧ |firstTheta v| ≤ Z^ν) →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ v ∈ S, ∀ j, |freq v j| ≤ Z^ν) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      ∀ supportLoss clipLoss commonLoss : ℝ, supportLoss+clipLoss+commonLoss ≤ lengthLoss →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^A) →
      (∀ v ∈ S, Z^(c+c₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.1).absNorm : ℝ) ∧
        Z^(c+d₂-commonLoss) ≤ (((s v).firstCommon*(s v).second.val.2).absNorm : ℝ)) →
      (∀ v ∈ S, (max 1 (s v).input.upper)^Fintype.card Slot ≤ Z^supportLoss) →
      Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ clipLoss →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →

      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      ∀ scalarLoss : ℝ,
      (∀ v ∈ S, 0 < K v ∧
        K v ≤ Z^(2*A-c-d₁+R₁+E-1+max (d₁-c) 0+6*(3/500)+(omegaLoss-scalarLoss))) →
      (∀ v ∈ S, (s v).secondLogCost Z ≤ g₂-t₂cost-b₂+scalarLoss) →
      ∀ volumeLoss : ℝ,
      Z^(A-volumeLoss) ≤ CenteredMomentExceptionalAmplitudePair.volume input.toData →
      (∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        ∑ q ∈ qs, let v := q.label; ∑ D ∈ Ds v,
          ‖((s v).withRays χ ξ).physicalRowTerm (CenteredMomentExceptionalAmplitudePair.volume input.toData)
            (actualHighPrimeCount M H Sbad Z)
            (t v) (z v) Wkernel (K v) (Radius v) (n v) D‖) ≤
        C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,hhigh⟩ :=
    actual_joint_high_source_rays η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
      aSource Mslot upper haSource hMslot conductorReserve hconductorReserve
      Sbad primeLoss hprimeLoss hprimeReserve Wkernel tailA targetLower plainBound₁ plainBound₂
      hplainBound₁ hplainBound₂ hplainNorm₁ hplainNorm₂
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,C,hν,hντ,hτdet,hheight,horders,hC,?_⟩
  filter_upwards [hhigh] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
  dsimp only
  let S := qs.image NonzeroJointSourceRow.label
  let unit := sourceUnit fallback η ξ₁ ξ₂
  let w := sourceRow fallback η ξ₁ ξ₂
  let s := sourceKernel input puncture seed side hseed hz₁ hz₂ fallback η ξ₁ ξ₂ 1 1
  let first := sourceFirst fallback η ξ₁ ξ₂
  let z := sourceFrequency fallback
  let Ds := fun v => (s v).physicalProjectors
  let rayWeight := fun v => (s v).physicalRayWeight
  intro R hR hprojSource hbin hnorm hNw hNr t K Radius tbase firstU firstTheta n
    σ freq θ slotWidth hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost volumeLoss hVolumeLower
  have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin
    input puncture seed hpuncture hseed hz₁ hz₂ side ξ₁ ξ₂ fallback qs
    R hR hprojSource hbin hnorm hNw hNr t K Radius tbase firstU firstTheta n
    σ freq θ slotWidth hprofileCaps hsourceIntervals hsourceNorm hprojectorNorm hphysical
    Bmask hconductorBalance hmaskNorm hplain hmatch
    hscale hprimeScale hteq hinputfreq hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
    supportLoss clipLoss commonLoss hlengthLossSplit hvolume hcommonDyads hsupport hclip
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htarget scalarLoss hKactual hcost
  have hz : 0 < Z := zero_lt_one.trans hZ.1
  have hV := CenteredMomentExceptionalAmplitudePair.volume_pos input.toData
  have hratio := sector_original_volume_ratio Z A c volumeLoss
    (CenteredMomentExceptionalAmplitudePair.volume input.toData) hZ.1 hVolumeLower
  have he := physical_source_sum_change_volume qs (fun q => s q.label)
    (fun q => t q.label) (fun q => K q.label) (fun q => Radius q.label)
    (fun q => z q.label) (fun q => n q.label) Wkernel
    (CenteredMomentExceptionalAmplitudePair.volume input.toData) (Z^(A-c))
    (actualHighPrimeCount M H Sbad Z) hV (Real.rpow_pos_of_pos hz _)
  change _ ≤ C*Z^(π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000)
  rw [he]
  calc
    _ ≤ (Z^(A-c)/CenteredMomentExceptionalAmplitudePair.volume input.toData)*
        (C*Z^(π+A-c+R₁+E+Bc-144011/219600000)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ Z^(-c+volumeLoss)*(C*Z^(π+A-c+R₁+E+Bc-144011/219600000)) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by
      rw [show π+A-2*c+R₁+E+Bc+volumeLoss-144011/219600000 =
        (-c+volumeLoss)+(π+A-c+R₁+E+Bc-144011/219600000) by ring,Real.rpow_add hz (-c+volumeLoss) (π+A-c+R₁+E+Bc-144011/219600000)]
      ring

end FixedData
#print axioms actual_joint_high_source_original_volume
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighSourceOriginal -/
