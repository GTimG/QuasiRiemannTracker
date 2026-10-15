/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Submissions.affine_local_20261013.Bundles.B011
import Submissions.affine_local_20261013.Bundles.B040
import Submissions.affine_local_20261013.Bundles.B044
import Submissions.affine_local_20261013.Bundles.B059
import Submissions.affine_local_20261013.Bundles.B062
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadialPointwise
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstDivisorCommonBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedRightTransport

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalFirstContribution ; sha256 c932330b7ce4e33fc2f46b47fe5024f181d3898e61db5802705f8b423a324d3e -/
section




/-! Actual exceptional first children, with source-derived normalization,
profile control and the local negative exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstMixedAllowance CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstChildProfileControl CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondExceptionalUniformSource CenteredMomentFiniteProfileExceptional
open CenteredMomentFiniteProfileExceptionalPhysical CenteredMomentSecondEnergySplit
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open ConcretePrimeRowBridge RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointExceptionalFirstDecEq1 {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance jointExceptionalFirstDecEq2 {κ : Type*} : DecidableEq (κ ⊕ Fin 2) := Classical.decEq _

open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalFixedWeightSum
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstSectors
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentFirstMixedRightTransport
open CenteredMomentSupportedCorrelation CenteredMomentSecondRetainedAggregate

structure MainExceptionalRun where
  mask : Ideal O
  seed : Ideal O
  height : ℝ
  omega : ℝ
  Tsec : ℝ
  ξ : ℝ
  ray : RayCharacter
  rowModulus : O

namespace MainExceptionalRun
variable {Slot : Type*} [Fintype Slot]

def normalizedValue (x : MainExceptionalRun) (s : Input Slot) (C D : Ideal O)
    (U : Finset (CommonIndex C D)) (τ : Character) (K b Z : ℝ) (Q : Ideal O) : ℝ :=
  allocatedMainExceptionalEnergy s (commonPart C D) x.mask x.seed τ x.height b Z Q x.ray x.rowModulus
    (mainCommonRadius Z (Real.logb Z (D.absNorm : ℝ))
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
        K (CenteredMomentAmplificationChildInput.volume s) Z)
      (Real.logb Z (C.absNorm : ℝ)) (9/500) x.omega 0) x.Tsec x.ξ /
    ((τ.modulus.absNorm : ℝ)*(CenteredMomentAmplificationChildInput.volume s/(C.absNorm : ℝ)^2)*
      Z^(allowance C D Z))

/-- These are literal support, conductor, scale and frequency gates for
one actual run. No energy estimate or normalization envelope is assumed. -/
structure Admissible (x : MainExceptionalRun) (s : Input Slot) (C D : Ideal O)
    (τ : Character) (Z Bcap Bfirst heightCap seedFloor : ℝ) : Prop where
  mask_ne : x.mask ≠ 0
  seed_squarefree : Squarefree x.seed
  seed_ne : x.seed ≠ 0
  omega_le : x.omega ≤ 1/100
  common_cap : (C.absNorm : ℝ) ≤ Z^Bfirst
  child_caps : ∀ B : actualAllocations s.pools (commonPart C D),
    frozenCoefficient B.val (commonPart C D) x.mask s.ν s.W s.P ≠ 0 →
    let d := child s (commonPart C D) x.mask B τ x.height
    (∀ i, 1 ≤ d.P i) ∧ 0 ≤ sourceRadius d ∧ sourceRadius d ≤ Z^Bcap
  conductor_cap : (τ.modulus.absNorm : ℝ) ≤ Z^Bcap
  mask_cap : ((x.mask*commonPart C D).absNorm : ℝ) ≤ Z^Bcap
  row_ne : x.rowModulus ≠ 0
  row_lambda : goodLambda ∣ x.rowModulus
  row_two : (2 : O) ∣ x.rowModulus
  frequency_pos : 0 < frequencyRadius x.Tsec Z x.ξ
  frequency_cap : frequencyRadius x.Tsec Z x.ξ ≤ Z^Bcap
  height_le : ‖x.height‖ ≤ heightCap
  seed_lower : seedFloor ≤ (x.seed.absNorm : ℝ)
end MainExceptionalRun

/-- The actual allocated source estimate is uniform in all finite first
labels and Fourier heights bounded by the displayed height cap. -/
theorem actual_local_main_exceptional_runs
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (b : ℝ) (hb : 1 ≤ b) (Bcap Bfirst : ℝ)
    (hBcap : 0 ≤ Bcap) (hBfirst : 0 ≤ Bfirst) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Cfixed : ℝ, 0 < Cfixed ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p.profile 0 → s.W₂ = p.profile 1 → s.upper ≤ b →
      ∀ (η τ : Character) (C D : Ideal O) (hC : Supported C) (hD : Supported D),
      primeSupport C = primeSupport D → ∀ U : Finset (CommonIndex C D),
      ∀ (K M heightCap seedFloor : ℝ), 0 < K → 0 ≤ heightCap → 0 < seedFloor →
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72 : O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U*activeConductor C D} →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      ∀ x : MainExceptionalRun, x.Admissible s C D τ Z Bcap Bfirst heightCap seedFloor →
      x.normalizedValue s C D U τ K b Z Q ≤
        Cfixed*p.control S^2*(1+heightCap)^(2*J)*mass s^6*Z^(-2/25 : ℝ)/seedFloor := by
  obtain ⟨J,S,hS,hsource⟩ := actual_local_main_exceptional_contribution
    wlo whi hwlo hwhi lo hi b hb Bcap Bfirst hBcap hBfirst
  refine ⟨J,S,hS,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Cfixed,hCfixed,hsource⟩ := hsource Q hQ hQt hQ72
  refine ⟨Cfixed,hCfixed,?_⟩
  filter_upwards [hsource] with Z hsource
  refine ⟨hsource.1,?_⟩
  intro s p hlo hhi hW₁ hW₂ hupper η τ C D hC hD hCD U K M heightCap seedFloor
    hK hheight hfloor hmod hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ x hx
  have hh := hsource.2 s p hlo hhi hW₁ hW₂ η τ C D
    (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) U})
    hC hD hCD U rfl K x.omega M hK hmod x.mask x.seed x.height hupper
    hM hwidth hvolume hx.common_cap hx.omega_le hX₁ hX₂ hY₁ hY₂
    hx.mask_ne hx.seed_squarefree hx.seed_ne hx.child_caps hx.conductor_cap hx.mask_cap
    x.ray x.rowModulus hx.row_ne hx.row_lambda hx.row_two x.Tsec x.ξ hx.frequency_pos hx.frequency_cap
  apply hh.trans
  have hZ := (zero_lt_one.trans hsource.1).le
  have ht : (1+‖x.height‖)^(2*J) ≤ (1+heightCap)^(2*J) := by
    gcongr
    exact hx.height_le
  apply (div_le_div_of_nonneg_left (by positivity) hfloor hx.seed_lower).trans
  exact div_le_div_of_nonneg_right (by gcongr) hfloor.le

/-- The actual paired exceptional allocation sums, with the canonical
first scalar and every original first label, have a fixed negative reserve.
The only hypotheses on the second source runs are the displayed source
and geometric gates; there is no exceptional envelope premise. -/
theorem actual_first_allocated_exceptional_sum
    {Slot : Type*} [Fintype Slot]
    (wlo whi : ℝ) (hwlo : 0 < wlo) (hwhi : 0 ≤ whi)
    (lo hi : Slot → ℝ) (b : ℝ) (hb : 1 ≤ b) (Bcap Bfirst Lfirst Crfirst : ℝ)
    (hBcap : 0 ≤ Bcap) (hBfirst : 0 ≤ Bfirst) (hLfirst : 0 ≤ Lfirst) (hCrfirst : 0 < Crfirst) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), (0,0) ∈ S ∧
      ∀ Q : Ideal O, Q ≠ 0 → Q ≠ ⊤ → Q ≤ Ideal.span {(72 : O)} →
      ∃ Cfixed : ℝ, 0 < Cfixed ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (s : Input Slot) (p₀ : Profiles wlo whi),
      (∀ i, s.lo i = lo i) → (∀ i, s.hi i = hi i) →
      s.W₁ = p₀.profile 0 → s.W₂ = p₀.profile 1 → s.upper ≤ b →
      ∀ R seed : Ideal O, Squarefree seed → seed ≠ 0 → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      0 < sourceRadius s → sourceRadius s ≤ Z^Bfirst →
      ∀ (m A : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
        (K a₁ a₂ win M heightCap seedFloor : ℝ),
      0 < K → 0 < a₁ → 0 < a₂ → 0 ≤ heightCap → 0 < seedFloor →
      (∀ y, s.W₁ y ≠ 0 → a₁ ≤ y) → (∀ y, s.W₂ y ≠ 0 → a₂ ≤ y) →
      (∀ i y, V i y ≠ 0 → |y| ≤ win) →
      1 ≤ M → M ≤ Real.logb Z K+Real.logb Z (s.η.modulus.absNorm : ℝ)+Real.logb Z fixedPresentationCost →
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s) ≤ (883/1000)*M →
      Z^(M/4) ≤ s.X₁ → Z^(M/4) ≤ s.X₂ → Z^(M/4) ≤ s.Y₁ → Z^(M/4) ≤ s.Y₂ →
      ∀ radius : (p : Labels s R seed) → Finset (CommonIndex p.val.1 p.val.2) → ℝ,
      (∀ p E, radius p E ≤ Crfirst*Z^Lfirst) →
      ∀ (ξ₁ ξ₂ : RayCharacter) (F : Families s R seed ξ₁ ξ₂),
      ∀ runs : (p : Labels s R seed) → (E : Finset (CommonIndex p.val.1 p.val.2)) →
        Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm) → Fin 2 → MainExceptionalRun,
      (∀ (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2)),
        E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2 → ∀ n,
        (runs p E n 0).mask = R ∧ (runs p E n 1).mask = R ∧
        (runs p E n 0).Admissible s p.val.1 p.val.2 (F p E).left Z Bcap Bfirst heightCap seedFloor ∧
        (runs p E n 1).Admissible s p.val.2 p.val.1 (F p E).right Z Bcap Bfirst heightCap seedFloor) →
      (∑ p : Labels s R seed,
        ∑ E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2,
        ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
          (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm),
          allowanceWeight s R seed m A t W V K (radius p E) Z p E (F p E).left (F p E).right n *
            (Real.sqrt ((runs p E n 0).normalizedValue s p.val.1 p.val.2 E (F p E).left K b Z Q)*
             Real.sqrt ((runs p E n 1).normalizedValue s p.val.2 p.val.1
               (swapSubset p.val.1 p.val.2 E) (F p E).right K b Z Q))) ≤
      Cfixed*p₀.control S^2*(1+heightCap)^(2*J)*mass s^6*
        ((Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ))*
          Z^(-7/100 : ℝ)/((seed.absNorm : ℝ)*seedFloor) := by
  obtain ⟨J,S,hS,hsource⟩ := actual_local_main_exceptional_runs
    wlo whi hwlo hwhi lo hi b hb Bcap Bfirst hBcap hBfirst
  obtain ⟨Cweight,hCweight,hweight⟩ := original_fixed_allowance_weight_sum
    Bfirst Lfirst Crfirst (1/100) hBfirst hLfirst hCrfirst (by norm_num)
  refine ⟨J,S,hS,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨Csource,hCsource,hsource⟩ := hsource Q hQ hQt hQ72
  refine ⟨Csource*Cweight,mul_pos hCsource hCweight,?_⟩
  filter_upwards [hsource,hweight] with Z hsource hweight
  refine ⟨hsource.1,?_⟩
  intro s p₀ hlo hhi hW₁ hW₂ hupper R seed hseed hseed0 hzero₁ hzero₂ hH hHcap
    m A t W V K a₁ a₂ win M heightCap seedFloor hK ha₁ ha₂ hheight hfloor hs₁ hs₂ hwin
    hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ radius hr ξ₁ ξ₂ F runs hruns
  have hZ : 0 < Z := zero_lt_one.trans hsource.1
  let bound := Csource*p₀.control S^2*(1+heightCap)^(2*J)*mass s^6*Z^(-2/25 : ℝ)/seedFloor
  have hbound : 0 ≤ bound := by dsimp [bound]; positivity
  have hpair (p : Labels s R seed) (E : Finset (CommonIndex p.val.1 p.val.2))
      (hE : E ∈ CenteredMomentFirstDiscardedEnergy.inactiveSubsets p.val.1 p.val.2)
      (n : Blocks (effectiveScale p.val.1 p.val.2 E K) (radius p E)
        (sourceRadius s/p.val.1.absNorm) (sourceRadius s/p.val.2.absNorm)) :
      Real.sqrt ((runs p E n 0).normalizedValue s p.val.1 p.val.2 E (F p E).left K b Z Q)*
        Real.sqrt ((runs p E n 1).normalizedValue s p.val.2 p.val.1
          (swapSubset p.val.1 p.val.2 E) (F p E).right K b Z Q) ≤ bound := by
    have hp := commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ p.property
    have hCD := first_label_equal_support s R seed p
    obtain ⟨_,_,hleft,hright⟩ := hruns p E hE n
    have hleft := hsource.2 s p₀ hlo hhi hW₁ hW₂ hupper s.η (F p E).left p.val.1 p.val.2
      hp.1 hp.2 hCD E K M heightCap seedFloor hK hheight hfloor (F p E).left_modulus
      hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ (runs p E n 0) hleft
    have hright := hsource.2 s p₀ hlo hhi hW₁ hW₂ hupper s.η (F p E).right p.val.2 p.val.1
      hp.2 hp.1 hCD.symm (swapSubset p.val.1 p.val.2 E) K M heightCap seedFloor hK hheight hfloor
      (right_modulus s.η p.val.1 p.val.2 hp.1 E ξ₁ ξ₂ (F p E))
      hM hwidth hvolume hX₁ hX₂ hY₁ hY₂ (runs p E n 1) hright
    exact (mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt hbound)
  have hw := hweight Slot s R seed hseed hseed0 hzero₁ hzero₂ hH hHcap m A t W V
    K a₁ a₂ win hK ha₁ ha₂ hs₁ hs₂ hwin radius hr ξ₁ ξ₂ F
  calc
    _ ≤ bound*sumAllowanceWeight s R seed m A t W V K Z radius
        (fun p E => (F p E).left) (fun p E => (F p E).right) := by
      unfold sumAllowanceWeight
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro E hE
      apply Finset.sum_le_sum
      intro n _
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hpair p E hE n)
        (allowanceWeight_nonneg s R seed m A t W V K (radius p E) Z hZ.le
          p E (F p E).left (F p E).right n)
    _ ≤ bound*
        (((Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ))*
          (Cweight*Z^(1/100 : ℝ)/(seed.absNorm : ℝ))) :=
      mul_le_mul_of_nonneg_left hw hbound
    _ = _ := by
      have hpow : Z^(-2/25 : ℝ)*Z^(1/100 : ℝ) = Z^(-7/100 : ℝ) := by
        rw [←Real.rpow_add hZ]
        norm_num
      dsimp only [bound]
      calc
        _ = (Csource*Cweight)*p₀.control S^2*(1+heightCap)^(2*J)*mass s^6*
          ((Real.exp win/((∏ i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*(s.η.modulus.absNorm : ℝ))*
          (Z^(-2/25 : ℝ)*Z^(1/100 : ℝ))/((seed.absNorm : ℝ)*seedFloor) := by ring
        _ = _ := by rw [hpow]

#print axioms actual_local_main_exceptional_runs
#print axioms actual_first_allocated_exceptional_sum
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalFirstContribution -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstKernelCutoff ; sha256 57f1b696c2d3070a8c2f826b01d74ff0287664a81d8db04b6a9ce4c2ec8f4770 -/
section




/-! The first Fourier windows need the improved joint energy only in a
bounded region. Their tails use the literal height-independent source
majorant; the polynomial degree is chosen before the live geometry. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstDivisorCommonBound
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem two_variable_polynomial_extension_even (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∀ target : ℝ, lower ≤ target → ∀ (Z Ch Ct : ℝ),
      1 ≤ Z → 0 ≤ Ch → 0 ≤ Ct → ∀ F : ℝ → ℝ → ℝ,
      (∀ θ u, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → F θ u ≤ Ch*Z^target) →
      (∀ θ u, F θ u ≤ Ct*Z^B) →
      ∀ θ u, F θ u ≤ ((Ch+Ct)*Z^target*((1+‖θ‖)^N)^2)*(1+‖u‖)^(2*N) := by
  obtain ⟨N,hN⟩ := three_variable_polynomial_extension_lower ν B lower hν
  refine ⟨N,?_⟩
  intro target htarget Z Ch Ct hZ hCh hCt F hlocal hcoarse θ u
  have hh := hN target htarget Z Ch Ct hZ hCh hCt (fun θ u _ => F θ u)
    (fun θ u _ hθ hu _ => hlocal θ u hθ hu) (fun θ u _ => hcoarse θ u) θ u 0
  simp only [norm_zero,add_zero,one_pow,mul_one] at hh
  apply hh.trans
  have hθ : (1+‖θ‖)^N ≤ ((1+‖θ‖)^N)^2 := by
    have hp := one_le_pow₀ (show 1 ≤ 1+‖θ‖ by linarith [norm_nonneg θ]) (n := N)
    nlinarith
  have hu : (1+‖u‖)^N ≤ (1+‖u‖)^(2*N) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg u]) (by omega)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hθ (by positivity)) hu (by positivity) (by positivity)

namespace FirstJointLabel

def leftCoarse (s : FirstJointLabel ι) (U : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  coarse s.data s.C s.hC s.projector U K

def rightCoarse (s : FirstJointLabel ι) (U : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  coarse s.data s.D s.hD s.projector U K

theorem leftEnergy_le_coarse (s : FirstJointLabel ι) (t : ℝ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) : s.leftEnergy t U K ≤ s.leftCoarse U K :=
  commonEnergy_coarse s.data s.C s.hC s.projector U K hK s.pair.left t

theorem rightEnergy_le_coarse (s : FirstJointLabel ι) (t : ℝ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) : s.rightEnergy t U K ≤ s.rightCoarse U K :=
  commonEnergy_coarse s.data s.D s.hD s.projector U K hK s.pair.right t

end FirstJointLabel

theorem joint_first_blocks_from_local_common_energy
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay : ℕ) (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (target₁ target₂ Z Ch₁ Ch₂ Ct₁ Ct₂ : ℝ),
      lower ≤ target₁ → lower ≤ target₂ → 1 ≤ Z →
      0 ≤ Ch₁ → 0 ≤ Ch₂ → 0 ≤ Ct₁ → 0 ≤ Ct₂ →
      ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).leftEnergy
            (t k.1+2*Real.pi*(w-θ)) (U k) (H k)) ≤ Ch₁*Z^target₁) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).rightEnergy
            (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k)) ≤ Ch₂*Z^target₂) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftCoarse (U k) (H k)) ≤ Ct₁*Z^B →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightCoarse (U k) (H k)) ≤ Ct₂*Z^B →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ ≤
          C * (Real.sqrt ((Ch₁+Ct₁)*Z^target₁) * Real.sqrt ((Ch₂+Ct₂)*Z^target₂)) := by
  obtain ⟨N,hpoly⟩ := two_variable_polynomial_extension_even ν B lower hν
  obtain ⟨C,hC,hkernel⟩ := joint_first_blocks_from_common_energy (ι := ι)
    W V M hM hV hV₂c hV₂s hV₃c hV₃s decay N N N N
  refine ⟨N,C,hC,?_⟩
  intro target₁ target₂ Z Ch₁ Ch₂ Ct₁ Ct₂ ht₁ ht₂ hZ hCh₁ hCh₂ hCt₁ hCt₂
    Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁
    U H hH hU hmajor hleft hright hcoarseL hcoarseR
  apply hkernel labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀
    hη hV₀ hV₁ U H hH hU hmajor ((Ch₁+Ct₁)*Z^target₁) ((Ch₂+Ct₂)*Z^target₂)
      (by positivity) (by positivity)
  · apply hpoly target₁ ht₁ Z Ch₁ Ct₁ hZ hCh₁ hCt₁ _ hleft
    intro θ w
    apply le_trans (Finset.sum_le_sum (fun k hk =>
      ((s k.1).sourceChild k.2).leftEnergy_le_coarse _ (U k) (H k) (hH k hk)))
    exact hcoarseL
  · apply hpoly target₂ ht₂ Z Ch₂ Ct₂ hZ hCh₂ hCt₂ _ hright
    intro θ w
    apply le_trans (Finset.sum_le_sum (fun k hk =>
      ((s k.1).sourceChild k.2).rightEnergy_le_coarse _ (U k) (H k) (hH k hk)))
    exact hcoarseR

theorem joint_first_blocks_from_local_normalized_common_energy
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (hV₂c : HasCompactSupport (V 2)) (hV₂s : ContDiff ℝ ∞ (V 2))
    (hV₃c : HasCompactSupport (V 3)) (hV₃s : ContDiff ℝ ∞ (V 3))
    (decay : ℕ) (ν B lower : ℝ) (hν : 0 < ν) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T target₁ target₂ Z Ch₁ Ch₂ Ct₁ Ct₂ : ℝ), 0 < T →
      lower ≤ target₁ → lower ≤ target₂ → 1 ≤ Z →
      0 ≤ Ch₁ → 0 ≤ Ch₂ → 0 ≤ Ct₁ → 0 ≤ Ct₂ →
      ∀ {Λ : Type*} [DecidableEq Λ]
      (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
      (t K K₀ H₀ A₀ B₀ : Λ → ℝ) (η : Λ → ℂ),
      (∀ z ∈ rows, z ≠ 0) →
      (∀ l, 0 < K l) → (∀ l, 0 < K₀ l) → (∀ l, 0 < H₀ l) →
      (∀ l, 0 < A₀ l) → (∀ l, 0 < B₀ l) →
      (∀ l ∈ labels, ∀ i : (s l).SourceIndex,
        ‖η l * (s l).sourceWeight (K l) (A₀ l) (B₀ l) i‖ ≤ 1) →
      (∀ l ∈ labels, ‖V 0 ((s l).sourceRowLog (K l) (K₀ l))‖ ≤ 1) →
      (∀ l ∈ labels, ∀ z ∈ rows, ‖V 1 (Real.log (‖eisEmbedding z‖ ^ 2 / H₀ l))‖ ≤ 1) →
      ∀ (U : ((l : Λ) × (s l).SourceIndex) → 𝓢(ℝ, ℂ))
        (H : ((l : Λ) × (s l).SourceIndex) → ℝ),
      (∀ k ∈ firstSourceLabels labels s, 0 < H k) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z : O,
        0 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ k ∈ firstSourceLabels labels s, ∀ z ∈ rows,
        1 ≤ (U k (‖eisEmbedding z‖ ^ 2 / H k)).re) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).leftEnergy
            (t k.1+2*Real.pi*(w-θ)) (U k) (H k)) ≤ T*(Ch₁*Z^target₁)) →
      (∀ θ w : ℝ, ‖θ‖ ≤ Z^ν → ‖w‖ ≤ Z^ν →
        (∑ k ∈ firstSourceLabels labels s,
          ((s k.1).sourceChild k.2).rightEnergy
            (t k.1+2*Real.pi*(w-(-θ))) (U k) (H k)) ≤ T*(Ch₂*Z^target₂)) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).leftCoarse (U k) (H k)) ≤ T*(Ct₁*Z^B) →
      (∑ k ∈ firstSourceLabels labels s,
        ((s k.1).sourceChild k.2).rightCoarse (U k) (H k)) ≤ T*(Ct₂*Z^B) →
      ‖∑ l ∈ labels, (((1 + K₀ l * H₀ l / (A₀ l * B₀ l)) ^ decay : ℝ) : ℂ) * η l *
        (s l).sourceBlock (t l) rows W V (K l) (K₀ l) (H₀ l) (A₀ l) (B₀ l)‖ / T ≤
          C * (Real.sqrt ((Ch₁+Ct₁)*Z^target₁) * Real.sqrt ((Ch₂+Ct₂)*Z^target₂)) := by
  obtain ⟨N,C,hC,hkernel⟩ := joint_first_blocks_from_local_common_energy (ι := ι)
    W V M hM hV hV₂c hV₂s hV₃c hV₃s decay ν B lower hν
  refine ⟨N,C,hC,?_⟩
  intro T target₁ target₂ Z Ch₁ Ch₂ Ct₁ Ct₂ hT ht₁ ht₂ hZ hCh₁ hCh₂ hCt₁ hCt₂
    Λ inst labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁
    U H hH hU hmajor hleft hright hcoarseL hcoarseR
  have hh := hkernel target₁ target₂ Z (T*Ch₁) (T*Ch₂) (T*Ct₁) (T*Ct₂)
    ht₁ ht₂ hZ (by positivity) (by positivity) (by positivity) (by positivity)
    labels rows s t K K₀ H₀ A₀ B₀ η hrows hK hK₀ hH₀ hA₀ hB₀ hη hV₀ hV₁
    U H hH hU hmajor
    (by simpa only [mul_assoc] using hleft) (by simpa only [mul_assoc] using hright)
    (by simpa only [mul_assoc] using hcoarseL) (by simpa only [mul_assoc] using hcoarseR)
  rw [←mul_add,←mul_add,mul_assoc,mul_assoc,Real.sqrt_mul hT.le,Real.sqrt_mul hT.le] at hh
  apply (div_le_iff₀ hT).mpr
  apply hh.trans_eq
  calc
    _ = C*(Real.sqrt T)^2*
        (Real.sqrt ((Ch₁+Ct₁)*Z^target₁)*Real.sqrt ((Ch₂+Ct₂)*Z^target₂)) := by ring
    _ = _ := by rw [Real.sq_sqrt hT.le]; ring

#print axioms joint_first_blocks_from_local_normalized_common_energy

#print axioms joint_first_blocks_from_local_common_energy

#print axioms two_variable_polynomial_extension_even
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstKernelCutoff -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighComplete ; sha256 cce25cae8139734278d154e642212c27d5d61830500f41091058c1a8d5490252 -/
section



/-! The actual joint high-bin contribution after paying the polynomial
height factor. Density chooses its degree before the external Fourier
cutoff; all row and profile data remain live after this choice. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDetectorZeros CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily ConcretePrimeRowBridge
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

theorem actual_joint_high_contribution
    (V : Slot → ℝ → ℂ) (Aprofile Bprofile : Slot → ℝ) (hA : ∀ j, 0 < Aprofile j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (Aprofile j) (Bprofile j))
    (hV : ∀ j, ContDiff ℝ ∞ (V j))
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
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ),
      0 < ν ∧ ν < τ ∧ τ < τdetector ∧ 4*τ < dmin*ηaux ∧
      (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ (Z d P W : ℝ), 1 < Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      P ≤ B → W ≤ B →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ i : ℕ, i ≤ I → p.height = (3*(i+1 : ℕ))*Z^τ →
      ∀ (unit : JointReconstructionLabel → Oˣ) (S : Finset JointReconstructionLabel)
        (w : JointReconstructionLabel → NonzeroElement),
      (∀ v ∈ S, (w v).val = v.row (unit v)) →
      ∀ (R : JointReconstructionLabel →
        JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ v label, R v label ≠ 0),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) (R v) (hR v)
        p.lower p.upper p.height (w v)) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {(w v).val}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (w v).val) : ℝ) ≤ Z^P) →
      ∀ (DL DR : ∀ v, SurvivingBufferedData η (w v) Slot orders profileBound p.lower e),
      (∀ v ∈ S, (DL v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      (∀ v ∈ S, (DR v).Admissible M H hH η₀ Aprofile Bprofile
        Rwidth τ ηaux σmin σmax Z d p.height) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂ omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      (∀ v ∈ S, d*(DL v).length ≤ A-c-c₂+lengthLoss) →
      (∀ v ∈ S, d*(DR v).length ≤ A-c-d₂+lengthLoss) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂ →
      0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss →
      P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂-b₂+omegaLoss)*
        (∑ v ∈ S, ‖(DL v).value M H η₀ V Bprofile Z d‖ *
          ‖(DR v).value M H η₀ V Bprofile Z d‖) ≤
        C*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨J,hmain⟩ := actual_joint_surviving_high_product η η₀ Q hQtop hQ72 hQη hβ
    M H hH hQM hQη₀ S₀ φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
    V Aprofile Bprofile hA hVs hV Rwidth dmax ε e κ ηaux σmin σmax
    productLoss populationLoss loss B hRw hdmax hε he he' hκ hκone hη.le
    hbudget hprimebudget hproductLoss hpopulationLoss hB hloss profileBound hprofile
  obtain ⟨τ,ν,hν,hντ,hτdet,hheight,hτJ⟩ := exists_external_height_exponents
    τdetector dmin ηaux heightLoss J hτdetector hdmin hη hheightLoss
  have hτ : 0 < τ := hν.trans hντ
  obtain ⟨orders,N,C,horders,hC,hmain⟩ := hmain τ hτ
  let CH : ℝ := (1+3*(I+1 : ℕ))^J
  have hCH : 0 < CH := by dsimp [CH]; positivity
  refine ⟨τ,ν,orders,N,C*CH,hν,hντ,hτdet,hheight,horders,mul_pos hC hCH,?_⟩
  intro Z d P W hZ hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr DL DR hDL hDR
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂ omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂
    hb₂ hlenL hlenR hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal
  have hpair := hmain Z d P W hZ hd hdmax' hbase hT hPB hWB p hp unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr DL DR hDL hDR (A+lengthLoss) c c₂ d₂ b₂ hb₂
    (fun v hv => by linarith [hlenL v hv]) (fun v hv => by linarith [hlenR v hv])
  have hheightBound : (1+|p.height|)^J ≤ CH*Z^heightLoss := by
    rw [hheightBin]
    exact buffered_density_height_bound Z τ heightLoss J I i hZ.le hτ.le hi hτJ.le
  have hρ := local_density_bounds (2*p.lower-1) hδ hδtop
  have hρ₀ : 0 ≤ unmarkedDensity (2*p.lower-1) := by linarith [hρ.1]
  have hρ₁ : unmarkedDensity (2*p.lower-1) ≤ 1 := by linarith [hρ.2.1]
  have hWmul := mul_le_mul_of_nonneg_left hW hρ₀
  have hgeom := mul_le_mul_of_nonneg_right hρ₁ hgeometryLoss
  have hlen := mul_le_mul_of_nonneg_right (show 2*p.lower-1 ≤ 1 by linarith) hlengthLoss
  apply joint_high_rpow_bound Z (C*CH) _ (2*p.lower-1) A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂ omegaLoss
    (loss+heightLoss+geometryLoss+lengthLoss+missingLoss) hZ.le (mul_pos hC hCH).le
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂ (by linarith)
  apply hpair.trans
  calc
    _ ≤ C*(CH*Z^heightLoss)*
        Z^(unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A+lengthLoss-c-b₂)+loss) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheightBound hC.le) (by positivity)
    _ = (C*CH)*Z^(unmarkedDensity (2*p.lower-1)*W+P+
        (2*p.lower-1)*(A+lengthLoss-c-b₂)+loss+heightLoss) := by
      rw [Real.rpow_add (zero_lt_one.trans hZ)
        (unmarkedDensity (2*p.lower-1)*W+P+(2*p.lower-1)*(A+lengthLoss-c-b₂)+loss) heightLoss]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)) (mul_pos hC hCH).le

end FixedData
#print axioms actual_joint_high_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighComplete -/

/- BEGIN ORIGINAL MODULE Analytic.JointLiveCommonSource ; sha256 ca200ddffc1ed15653bf888cd47a069d12ed090e4c51086213b7551f31ceeaa5 -/
section



/-! The source Cauchy bound keeps exact frozen coefficients until their
zero branches are discarded. Only live common allocations require a
child estimate; all source, divisor and normalization factors are kept. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonRadialSource
open CenteredMomentCommonRadialPointwise CenteredMomentCommonRadialCost
open CenteredMomentCommonLinearNormalization CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentRestrictedSourceNormalization CenteredMomentRestrictedSource
open CenteredMomentSecondLiveEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentAmplificationLiveMask CenteredMomentCommonProfile
open CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem original_source_weighted_common_bound
    (s : Input ι) (r : Radial) (C : Ideal O) (hC : Supported C)
    (R seed L : Ideal O) (hseed : seed ∣ C) :
    sourceEnergy s r C hC R seed L ≤
      ((actualAllocations s.pools C).card : ℝ)*
        ∑ B : actualAllocations s.pools C,
          ‖commonScalar s C R B‖^2*energy (commonData s C R B) r L := by
  have he := normalized_restricted_child_energy s.pools s.pools_ne
    (fun i I hI => s.prime i I hI) C R seed hC hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
    (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos) s.P_pos
    (fun I => (if L ∣ I then 1 else 0)*heightCoeff s.η s.t I)
    r.keep r.profile r.scale r.scale_pos r.nonneg
  simp_rw [live_divisor_energy] at he
  simp_rw [live_source_eq] at he
  simp_rw [←commonScalar_sq] at he
  convert he using 1
  unfold sourceEnergy
  dsimp only
  congr 1
  unfold sourceRestrictedEnergy
  congr 1
  funext I
  dsimp only
  split_ifs <;> simp_all

theorem actual_live_common_source_pointwise (lo hi : ι → ℝ) (Bcap δ : ℝ)
    (hBcap : 0 ≤ Bcap) (hδ : 0 < δ) :
    ∃ C0 : ℝ,0 < C0 ∧ ∀ (s : Input ι),
      (∀ i,s.lo i = lo i) → (∀ i,s.hi i = hi i) →
      ∀ (r : Radial) (C : Ideal O) (hC : Supported C) (R seed L : Ideal O),
      seed ∣ C → Squarefree L → ∀ (E Z : ℝ),0 ≤ E → 1 < Z →
      (C.absNorm : ℝ) ≤ Z^Bcap → (L.absNorm : ℝ) ≤ Z^Bcap →
      (∀ B : actualAllocations s.pools C,
        frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
        ∀ a ∈ (commonData s C R B).toSource.active L,
          childEnergy (commonData s C R B) r L a ≤ E) →
      sourceEnergy s r C hC R seed L ≤
        C0*Z^δ*(profileCost s*E)/((C.absNorm : ℝ)*L.absNorm) := by
  obtain ⟨C₁,hC₁,hchild⟩ := CenteredMomentRadialPointwiseUniform.actual_uniform_divisor
    lo hi Bcap (δ/2) hBcap (by linarith)
  obtain ⟨C₂,hC₂,hcount⟩ := card_squared_subpower (ι := ι) Bcap (δ/2) hBcap (by linarith)
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s hlo hhi r C hC R seed L hseed hL E Z hE hZ hNC hNL hc
  have hnC := CenteredMomentFirstScale.norm_pos C hC.1
  have hnL := CenteredMomentFirstScale.norm_pos L hL.ne_zero
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hprofile := s.toData.profile_nonneg
  have hbound0 : 0 ≤ C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm : ℝ) := by positivity
  have heach (B : actualAllocations s.pools C) :
      ‖commonScalar s C R B‖^2*energy (commonData s C R B) r L ≤
        (commonSourceProfile s/(C.absNorm : ℝ))*
          (C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm : ℝ)) := by
    by_cases hB : frozenCoefficient B.val C R s.ν s.W s.P = 0
    · rw [commonScalar_sq,hB,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul]
      exact mul_nonneg (div_nonneg (commonSourceProfile_nonneg s) hnC.le) hbound0
    · have hh := hchild (liveIndices B.val) (commonData s C R B)
        (fun i => hlo i.val) (fun i => hhi i.val) r L hL E Z hE hZ hNL (hc B hB)
      have hh' : energy (commonData s C R B) r L ≤
          C₁*Z^(δ/2)*(s.toData.profileFactor*E)/(L.absNorm : ℝ) := by
        apply hh.trans
        apply div_le_div_of_nonneg_right _ hnL.le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (common_profile_le s C R B) hE
      exact mul_le_mul (commonScalar_sq_bound s C R hC.1 B) hh'
        (energy_nonneg _ _ _) (div_nonneg (commonSourceProfile_nonneg s) hnC.le)
  have hh := (original_source_weighted_common_bound s r C hC R seed L hseed).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _ => heach B)) (Nat.cast_nonneg _))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at hh
  apply hh.trans
  have hcount' := hcount s C hC.1 Z hZ hNC
  calc
    _ = ((actualAllocations s.pools C).card : ℝ)^2*
        (C₁*Z^(δ/2)*(profileCost s*E)/((C.absNorm : ℝ)*L.absNorm)) := by
      unfold commonSourceProfile profileCost
      ring
    _ ≤ (C₂*Z^(δ/2))*(C₁*Z^(δ/2)*(profileCost s*E)/((C.absNorm : ℝ)*L.absNorm)) :=
      mul_le_mul_of_nonneg_right hcount'
        (div_nonneg (mul_nonneg (by positivity) (mul_nonneg (profileCost_nonneg s) hE))
          (mul_nonneg hnC.le hnL.le))
    _ = _ := by
      have hp : Z^(δ/2)*Z^(δ/2) = Z^δ := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      calc
        _ = (C₁*C₂)*(Z^(δ/2)*Z^(δ/2))*(profileCost s*E)/((C.absNorm : ℝ)*L.absNorm) := by ring
        _ = _ := by rw [hp]

#print axioms original_source_weighted_common_bound
#print axioms actual_live_common_source_pointwise
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLiveCommonSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowSourceGeometry ; sha256 1f15c20942815b1ba65ae2c71ec0f7cb330082e22f00515ec209c1dc367c38fb -/
section




/-! Nominal low-bin width from the actual second physical block. This
keeps the enlarged first radius and the literal common-frequency norms. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge CenteredMomentSecondPhysicalLedger
open CenteredMomentSourceRow
open RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentSecondChildRadialWidth
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

def jointLowNominal (M c d a omegaLoss g₂ t₂ : ℝ) : ℝ :=
  M-max (c-d) 0-6*a-omegaLoss-g₂+t₂

lemma jointSecondFrequency_log (C : Ideal O) (hC : C ≠ 0)
    (H Z A c d R e M a omegaLoss ξ : ℝ) (hH : 0 < H) (hZ : 1 < Z)
    (hCnorm : Real.logb Z (C.absNorm : ℝ) = c) :
    Real.logb Z (frequencyRadius (jointSecondNominal C H Z A c d R e M a omegaLoss) Z ξ) =
      2*Real.logb Z H-2*c-(2*A-c-d+R+e-M+max (d-c) 0+6*a+omegaLoss)+ξ/2 := by
  have hz := zero_lt_one.trans hZ
  have hc : (0 : ℝ) < C.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  unfold frequencyRadius jointSecondNominal jointSecondBall
  rw [Real.logb_mul (div_pos (pow_pos (div_pos hH hc) _) (Real.rpow_pos_of_pos hz _)).ne'
    (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_div (pow_pos (div_pos hH hc) _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_pow,Real.logb_div hH.ne' hc.ne']
  simp only [hCnorm,Real.logb_rpow hz hZ.ne']
  ring

theorem actual_joint_low_width
    (C₁ C₂ D₂ : Ideal O) (hC₁ : C₁ ≠ 0)
    (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character)
    (hfamily : Family η C₂ D₂ hC₂ hD₂ U family)
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (n : Fin 4 → ℤ)
    (H Z A c d R e M a omegaLoss ξ sourceLoss parentLoss : ℝ)
    (hH : 0 < H) (hZ : 1 < Z)
    (hCnorm : Real.logb Z (C₁.absNorm : ℝ) = c)
    (hsource : Real.logb Z H ≤ A+sourceLoss)
    (hparent : Real.logb Z (η.modulus.absNorm : ℝ) ≤ R+e+parentLoss)
    (hne : physicalBlock η t S β C₂ D₂ hC₂ hD₂ U
      (frequencyRadius (jointSecondNominal C₁ H Z A c d R e M a omegaLoss) Z ξ)
      rows W K n ≠ 0) :
    ∀ χ : RayCharacter,
      Real.logb Z (dyadicScale (n 1))+Real.logb Z ((family χ).modulus.absNorm : ℝ) ≤
        jointLowNominal M c d a omegaLoss
          (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
          (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) +
        (2*sourceLoss+parentLoss+ξ/2+
          Real.logb Z (16*(CenteredMomentSecondRadicalBudget.fixedFactor : ℝ))) := by
  intro χ
  have hh := dyadic_log_budget hfamily t S β
    (frequencyRadius (jointSecondNominal C₁ H Z A c d R e M a omegaLoss) Z ξ)
    rows W K hK n hne Z hZ χ
  rw [jointSecondFrequency_log C₁ hC₁ H Z A c d R e M a omegaLoss ξ hH hZ hCnorm] at hh
  have hmax : max (c-d) 0-max (d-c) 0 = c-d := by
    rcases le_total c d with hcd | hdc
    · rw [max_eq_right (sub_nonpos.mpr hcd),max_eq_left (sub_nonneg.mpr hcd)]
      ring
    · rw [max_eq_left (sub_nonneg.mpr hdc),max_eq_right (sub_nonpos.mpr hdc)]
      ring
  dsimp only [jointLowNominal]
  linarith

/-- The source volume drop is the norm of the complete cumulative common
ideal. Its comparison with the nominal width uses the actual frequency
generator divisibility, so canceled slots need no separate lower length. -/
theorem actual_joint_low_volume_shift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C₁ D₁ C₂ D₂ Rmask : Ideal O)
    (hC₁ : C₁ ≠ 0) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (B : actualAllocations s.pools (C₁*C₂))
    (hne : frozenCoefficient B.val (C₁*C₂) Rmask s.ν s.W s.P ≠ 0)
    (Z A M a omegaLoss loss : ℝ) (hZ : 1 < Z)
    (hvolume : Real.logb Z (volume s.toData) ≤ A)
    (hprofile : (Fintype.card ι : ℝ)*Real.logb Z (max 1 s.upper) ≤ loss) :
    Real.logb Z (secondCommonVolume s (C₁*C₂) B)-
      jointLowNominal M (Real.logb Z (C₁.absNorm : ℝ)) (Real.logb Z (D₁.absNorm : ℝ))
        a omegaLoss (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) ≤
      A-M+6*a+omegaLoss+loss := by
  have hc₁ := CenteredMomentFirstScale.norm_pos C₁ hC₁
  have hc₂ := CenteredMomentFirstScale.norm_pos C₂ hC₂.1
  have hcommon := actual_second_common_volume_log s (C₁*C₂) Rmask B hne Z hZ
  rw [map_mul,Nat.cast_mul,Real.logb_mul hc₁.ne' hc₂.ne'] at hcommon
  have hg0 := commonFrequencyGenerator_ne_zero C₂ D₂ hC₂
  have hdiv : Ideal.span {commonFrequencyGenerator C₂ D₂} ∣ C₂ := by
    have hh := Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
      (commonFrequencyGenerator_dvd C₂ D₂ hC₂ hD₂ hCD₂).1
    simpa only [primary_span_supported C₂ hC₂] using hh
  have hg : normValue (commonFrequencyGenerator C₂ D₂) ≤ (C₂.absNorm : ℝ) :=
    CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ C₂ hC₂.1 hdiv
  have hglog := Real.logb_le_logb_of_le hZ (normValue_pos _ hg0) hg
  have hc0 : 0 ≤ Real.logb Z (C₁.absNorm : ℝ) :=
    Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one C₁ hC₁)
  have hd0 : 0 ≤ Real.logb Z (D₁.absNorm : ℝ) :=
    Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one D₁ hD₁)
  have htpos := common_product_pos C₂ D₂ hC₂ U
  have ht1 : (1 : ℝ) ≤ (∏ P ∈ U,P.val).absNorm := by
    exact_mod_cast (show 1 ≤ (∏ P ∈ U,P.val).absNorm by exact_mod_cast htpos)
  have ht := Real.logb_nonneg hZ ht1
  have hm : max (Real.logb Z (C₁.absNorm : ℝ)-Real.logb Z (D₁.absNorm : ℝ)) 0 ≤
      Real.logb Z (C₁.absNorm : ℝ) := max_le (by linarith) hc0
  dsimp only [jointLowNominal]
  linarith

/-- Both sides use the same second common family and nominal width. -/
theorem actual_joint_low_volume_shift_selected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (C₁ D₁ C₂ D₂ Rmask : Ideal O)
    (hC₁ : C₁ ≠ 0) (hD₁ : D₁ ≠ 0) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : primeSupport C₂ = primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂))
    (T : Ideal O) (hT : T = C₂ ∨ T = D₂)
    (B : actualAllocations s.pools (C₁*T))
    (hne : frozenCoefficient B.val (C₁*T) Rmask s.ν s.W s.P ≠ 0)
    (Z A M a omegaLoss loss : ℝ) (hZ : 1 < Z)
    (hvolume : Real.logb Z (volume s.toData) ≤ A)
    (hprofile : (Fintype.card ι : ℝ)*Real.logb Z (max 1 s.upper) ≤ loss) :
    Real.logb Z (secondCommonVolume s (C₁*T) B)-
      jointLowNominal M (Real.logb Z (C₁.absNorm : ℝ)) (Real.logb Z (D₁.absNorm : ℝ))
        a omegaLoss (Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂)))
        (Real.logb Z ((∏ P ∈ U,P.val).absNorm : ℝ)) ≤
      A-M+6*a+omegaLoss+loss := by
  have hc₁ := CenteredMomentFirstScale.norm_pos C₁ hC₁
  have hTs : Supported T := by
    rcases hT with rfl | rfl
    · exact hC₂
    · exact hD₂
  have hc₂ := CenteredMomentFirstScale.norm_pos T hTs.1
  have hcommon := actual_second_common_volume_log s (C₁*T) Rmask B hne Z hZ
  rw [map_mul,Nat.cast_mul,Real.logb_mul hc₁.ne' hc₂.ne'] at hcommon
  have hg0 := commonFrequencyGenerator_ne_zero C₂ D₂ hC₂
  have hdiv : Ideal.span {commonFrequencyGenerator C₂ D₂} ∣ T := by
    rcases hT with hT | hT
    · rw [hT]
      have hh := Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
        (commonFrequencyGenerator_dvd C₂ D₂ hC₂ hD₂ hCD₂).1
      simpa only [primary_span_supported C₂ hC₂] using hh
    · rw [hT]
      have hh := Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
        (commonFrequencyGenerator_dvd C₂ D₂ hC₂ hD₂ hCD₂).2
      simpa only [primary_span_supported D₂ hD₂] using hh
  have hg : normValue (commonFrequencyGenerator C₂ D₂) ≤ (T.absNorm : ℝ) :=
    CenteredMomentFirstSourceConductorCaps.divisor_norm_le _ T hTs.1 hdiv
  have hglog := Real.logb_le_logb_of_le hZ (normValue_pos _ hg0) hg
  have hc0 : 0 ≤ Real.logb Z (C₁.absNorm : ℝ) :=
    Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one C₁ hC₁)
  have hd0 : 0 ≤ Real.logb Z (D₁.absNorm : ℝ) :=
    Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one D₁ hD₁)
  have htpos := common_product_pos C₂ D₂ hC₂ U
  have ht1 : (1 : ℝ) ≤ (∏ P ∈ U,P.val).absNorm := by
    exact_mod_cast (show 1 ≤ (∏ P ∈ U,P.val).absNorm by exact_mod_cast htpos)
  have ht := Real.logb_nonneg hZ ht1
  have hm : max (Real.logb Z (C₁.absNorm : ℝ)-Real.logb Z (D₁.absNorm : ℝ)) 0 ≤
      Real.logb Z (C₁.absNorm : ℝ) := max_le (by linarith) hc0
  dsimp only [jointLowNominal]
  linarith

#print axioms actual_joint_low_volume_shift_selected

#print axioms actual_joint_low_width
#print axioms actual_joint_low_volume_shift
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowSourceGeometry -/

/- BEGIN ORIGINAL MODULE Analytic.JointRetainedTransport ; sha256 386e94381a68b88598c9e287039e3ec339e418533dbf089c11e71e2c2e06458b -/
section



/-! Exact transport of allocated positive source rows, including their
complete common-ideal punctures. No analytic bound is an input. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentSecondHeightFamily CenteredMomentSourceRectangleMask
open CenteredMomentNaturalRowSource CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_transport (η τ : Character) (m A z n B w : O) (t : ℝ)
    (he : ∀ I : Ideal O, rowWeight η m A z t I = rowWeight τ n B w t I)
    (W : ℝ → ℂ) (X : ℝ) :
    rowTwistedSum η m A z W t X = rowTwistedSum τ n B w W t X := by
  simp only [rowTwistedSum_eq_weight]
  exact tsum_congr (fun I => by rw [he I])

theorem rowSlot_transport (η τ : Character) (m A z n B w : O) (t : ℝ)
    (he : ∀ I : Ideal O, rowWeight η m A z t I = rowWeight τ n B w t I)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) :
    rowSlot η m A z S β t = rowSlot τ n B w S β t := by
  simp only [rowSlot_eq_weight]
  exact Finset.sum_congr rfl (fun I _ => by rw [he I])

theorem allocatedPositiveRow_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η τ : Character) (m A z n B w : O) (t : ℝ)
    (he : ∀ I : Ideal O, rowWeight η m A z t I = rowWeight τ n B w t I)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    allocatedPositiveRow η m A z t pool β P D a W₁ W₂ X₁ X₂ =
      allocatedPositiveRow τ n B w t pool β P D a W₁ W₂ X₁ X₂ := by
  unfold allocatedPositiveRow retainedPositiveRow positiveSlotRow
  rw [rowTwistedSum_transport η τ m A z n B w t he,
    rowTwistedSum_transport η τ m A z n B w t he]
  congr 2
  exact Finset.prod_congr rfl (fun i _ => rowSlot_transport η τ m A z n B w t he _ _)

/-- Two ideal punctures combine multiplicatively, including at unsupported
ideals where the actual fixed mask makes both coefficients zero. -/
theorem rowWeight_join_puncture (η τ : Character) (j w : O) (t : ℝ)
    (T R : Ideal O)
    (he : ∀ I : Ideal O, rowWeight η fixedBadMask 1 j t I =
      rowWeight τ (fixedBadMask*idealGenerator T) 1 w t I) (I : Ideal O) :
    rowWeight η (fixedBadMask*idealGenerator R) 1 j t I =
      rowWeight τ (fixedBadMask*idealGenerator (R*T)) 1 w t I := by
  have hLam : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have h₂ : (2 : O) ∣ fixedBadMask := dvd_mul_left _ _
  rw [← rowWeight_ideal_mask η fixedBadMask 1 j t hLam h₂ R I, he I,
    ← rowWeight_ideal_mask τ fixedBadMask 1 w t hLam h₂ T I,
    ← rowWeight_ideal_mask τ fixedBadMask 1 w t hLam h₂ (R*T) I,
    IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

/-- The literal extra source mask is combined with the canceled-prime
mask of a natural row, before constructing any buffered data. -/
theorem allocatedPositiveRow_natural_transport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η τ : Character) (A z w : O) (t : ℝ)
    (N : NaturalRow τ w) (T R : Ideal O) (hT : T ≠ 0)
    (he : ∀ I : Ideal O, rowWeight η fixedBadMask 1 (A*z) t I =
      CenteredMomentHeckeColumnWindow.heightCoeff (excluded N.character T) t I)
    (pool : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    allocatedPositiveRow η (fixedBadMask*idealGenerator R) A z t pool β P D a W₁ W₂ X₁ X₂ =
      allocatedPositiveRow τ (fixedBadMask*idealGenerator (R*T)) 1 w t
        pool β P D a W₁ W₂ X₁ X₂ := by
  apply allocatedPositiveRow_transport
  intro I
  have hbase (J : Ideal O) := (he J).trans (naturalRow_masked_height N T hT t J)
  simpa only [rowWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, one_mul] using
    rowWeight_join_puncture η τ (A*z) w t T R hbase I

#print axioms allocatedPositiveRow_transport
#print axioms allocatedPositiveRow_natural_transport
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointRetainedTransport -/
