/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Submissions.affine_local_20261013.Bundles.B053
import Submissions.affine_local_20261013.Bundles.B064
import Submissions.affine_local_20261013.Bundles.B067
import Submissions.affine_local_20261013.Bundles.B078
import Submissions.affine_local_20261013.Bundles.B080
import Submissions.affine_local_20261013.Bundles.B084
import Submissions.affine_local_20261013.Bundles.B086
import Submissions.affine_local_20261013.Bundles.B087
import Submissions.affine_local_20261013.Bundles.B088
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceSecondZeroEnergy

/- BEGIN ORIGINAL MODULE Analytic.JointAllocatedErrors ; sha256 cc748c537617c33c0a9519627337904ad5cdf49c2b79f54f04b23f5be38d504d -/
section




/-! Actual first-allocation mass for the normalized prime average of the
literal extracted errors. The canonical common reference is retained for
the subsequent paired first-label allowance sum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstMixedNormalization
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentPrimeElements
open CenteredMomentFirstAnnularInput CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstChildProfileControl CenteredMomentFirstPhysicalSource
open CenteredMomentFirstScale CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentSourceLiveColumn
open RayFourExpansion
local notation "O" => HeckeFamily.O
local instance jointAllocatedErrorsDecEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def allocatedExtractedErrors {ι : Type*} [Fintype ι]
    (N : ℕ) (s : Input ι) (C R seed : Ideal O) (τ : Character)
    (t b Z d K₀ c sigma delta reserve : ℝ) (P : Finset (Ideal O))
    (family : actualAllocations s.pools C → elementPool P → Fin 3 → RayCharacter → Character) : ℝ :=
  ((max 1 b)^N*((actualAllocations s.pools C).card : ℝ)/(C.absNorm : ℝ))*
    ∑ B : actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
        (frozenControl B.val s.M)^2*((56/(P.card : ℝ))*∑ p : elementPool P,
          firstExtractedErrors (child s C R B τ t) (R*C) seed Z d K₀ c sigma delta reserve p (family B p))
      else 0

theorem allocated_error_reference_bound (N : ℕ) (b ε : ℝ) (hb : 1 ≤ b) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ {ι : Type*} [Fintype ι],
    ∀ (s : Input ι), Fintype.card ι ≤ N → ∀ (C R seed : Ideal O), C ≠ 0 →
    ∀ (τ : Character) (t Z d K₀ c sigma delta reserve allowance E : ℝ), 0 < Z → 0 ≤ E →
    ∀ (P : Finset (Ideal O))
      (family : actualAllocations s.pools C → elementPool P → Fin 3 → RayCharacter → Character),
    (∀ B, frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 →
      (56/(P.card : ℝ))*(∑ p : elementPool P,
        firstExtractedErrors (child s C R B τ t) (R*C) seed Z d K₀ c sigma delta reserve p (family B p)) ≤
        mass (child s C R B τ t)^2*
          (reference (τ.modulus.absNorm : ℝ) (volume s) (C.absNorm : ℝ) Z allowance/
            (volume s/(C.absNorm : ℝ)))*E) →
    allocatedExtractedErrors N s C R seed τ t b Z d K₀ c sigma delta reserve P family/
      ((τ.modulus.absNorm : ℝ)*(volume s/(C.absNorm : ℝ)^2)*Z^allowance) ≤
        D*(C.absNorm : ℝ)^ε*mass s^2*E := by
  obtain ⟨D,hD,halloc⟩ := allocated_exceptional_control N b ε hb hε
  refine ⟨D,hD,?_⟩
  intro ι _ s hn C R seed hC τ t Z d K₀ c sigma delta reserve allowance E hZ hE P family hbound
  have hv := volume_pos s
  have hc := norm_pos C hC
  have hq := norm_pos τ.modulus τ.modulus_ne_bot
  have hfactor : 0 ≤ reference (τ.modulus.absNorm : ℝ) (volume s) (C.absNorm : ℝ) Z allowance/
      (volume s/(C.absNorm : ℝ))*E := by unfold reference; positivity
  have hh := halloc hn s C R hC τ t _ hfactor
    (fun B => (56/(P.card : ℝ))*∑ p : elementPool P,
      firstExtractedErrors (child s C R B τ t) (R*C) seed Z d K₀ c sigma delta reserve p (family B p))
    (fun B hB => by convert hbound B hB using 1 <;> ring)
  have hden : 0 < (τ.modulus.absNorm : ℝ)*(volume s/(C.absNorm : ℝ)^2)*Z^allowance := by positivity
  have hh' := div_le_div_of_nonneg_right hh hden.le
  apply hh'.trans_eq
  rw [Real.rpow_sub hc,Real.rpow_one]
  unfold reference
  field_simp
  <;> ring

#print axioms allocated_error_reference_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointAllocatedErrors -/

/- BEGIN ORIGINAL MODULE Analytic.JointCoherentZero ; sha256 3ed66da1323b8eab570a96000c3f99f3411178e342c39dc21dec1ddb642a279b -/
section




/-! The coherent common-source zero frequency keeps its first-projector
denominator. A divisor estimate on the original coefficients replaces
any allocation of the common main polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceZeroEnergy
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceSecondZeroEnergy
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance coherentZeroDecidableSum : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_coefficient_small_power (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (s : Input ι) (R seed : Ideal O) (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ →
      s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) → sourceRadius s ≤ Z^B →
      ∀ I : Ideal O, (original s R seed).beta I ≠ 0 →
        ‖(original s R seed).beta I‖ ≤ C*(2*B₁*B₂*∏ j,s.M j)*Z^ε := by
  let n := Fintype.card ι+2
  let δ := ε/((B+1)*(n : ℝ))
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^n,by positivity,?_⟩
  intro Z hZ s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource I hI
  have hM : 0 ≤ ∏ j,s.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.M_ge_one j))
  obtain ⟨hI₀,hIN⟩ := original_column_norm s R seed I hz₁ hz₂ hI
  have hcoef := finiteColumnCoefficient_norm_le (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (2*B₁*B₂*∏ j,s.M j) (by positivity) (fun v _ _ =>
      profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M s.W₁ s.W₂ B₁ B₂
        (fun j => zero_le_one.trans (s.M_ge_one j)) hB₁ hB₂ s.W_bound hb₁ hb₂
        s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v) I hI₀
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hdiv : ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) ≤ (1+D)*Z^(B*δ) := by
    calc
      _ ≤ D*(I.absNorm : ℝ)^δ := hd I hI₀
      _ ≤ (1+D)*(Z^B)^δ := mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hIN.trans hsource) hδ.le)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
      _ = _ := by rw [←Real.rpow_mul hz.le]
  have hpower : B*δ*(n : ℝ) ≤ ε := by
    have heq : B*δ*(n : ℝ) = B*ε/(B+1) := by dsimp [δ]; field_simp <;> ring
    rw [heq]
    apply (div_le_iff₀ (show 0 < B+1 by positivity)).mpr
    nlinarith
  change ‖(original s R seed).beta I‖ ≤ (2*B₁*B₂*∏ j,s.M j)*
    ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ)^n at hcoef
  calc
    _ ≤ (2*B₁*B₂*∏ j,s.M j)*((1+D)*Z^(B*δ))^n :=
      hcoef.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv n) (by positivity))
    _ = (1+D)^n*(2*B₁*B₂*∏ j,s.M j)*Z^(B*δ*(n : ℝ)) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

theorem actual_common_second_zero (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cbound : ℝ, 0 < Cbound ∧ ∀ (Z : ℝ), 1 ≤ Z →
      ∀ (s : Input ι) (R seed C L : Ideal O) (hC : Supported C) (hL : L ≠ 0)
        (B₁ B₂ : ℝ), 0 ≤ B₁ → 0 ≤ B₂ → s.W₁ 0 = 0 → s.W₂ 0 = 0 →
      (∀ x, ‖s.W₁ x‖ ≤ B₁) → (∀ x, ‖s.W₂ x‖ ≤ B₂) →
      0 ≤ sourceRadius s → sourceRadius s ≤ Z^B →
      ∀ (η : Character) (t : ℝ),
      ‖sourceSecondZero (commonSecondColumns (original s R seed) C hC)
        (commonSecondBeta (original s R seed) C L) η t‖ ≤
      Cbound*(2*B₁*B₂*∏ j,s.M j)^2*Z^ε*sourceRadius s/
        ((C.absNorm : ℝ)*(L.absNorm : ℝ)) := by
  obtain ⟨D,hD,hd⟩ := original_coefficient_small_power (ι := ι) B (ε/2) hB (by positivity)
  refine ⟨128*D^2,by positivity,?_⟩
  intro Z hZ s R seed C L hC hL B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource₀ hsource η t
  have hM : 0 ≤ ∏ j,s.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.M_ge_one j))
  let F := 2*B₁*B₂*∏ j,s.M j
  have hf : 0 ≤ F := by dsimp [F]; positivity
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hc : 0 < (C.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hcap := commonSecond_source_norm_cap (original s R seed) C L hC (sourceRadius s)
    (fun I _ hI => (original_column_norm s R seed I hz₁ hz₂ hI).2)
  have hh := sourceSecondZero_divisor_bound (commonSecondColumns (original s R seed) C hC)
    (commonSecondBeta (original s R seed) C L) η t (D*F*Z^(ε/2))
    (sourceRadius s/(C.absNorm : ℝ)) (by positivity) (div_nonneg hsource₀ hc.le) L hL
    (by
      intro I hI hβ
      unfold commonSecondBeta at hβ ⊢
      split_ifs at hβ ⊢ with h
      · exact hd Z hZ s R seed B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂ hsource (C*I) hβ
      · exact False.elim (hβ rfl))
    (by
      intro I hI hβ
      by_contra hn
      simp only [commonSecondBeta,hn,and_false,ite_false,ne_eq,not_true_eq_false] at hβ)
    (fun I hI hβ => hcap I (Finset.mem_filter.mp hI).1 hβ)
  apply hh.trans_eq
  have hp : (Z^(ε/2))^2 = Z^ε := by
    rw [←Real.rpow_mul_natCast hz.le]
    norm_num
  dsimp only [F]
  rw [mul_pow,mul_pow,hp]
  ring

#print axioms original_coefficient_small_power
#print axioms actual_common_second_zero
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCoherentZero -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstCoarsePower ; sha256 f432b96704e10e69eea0229d19a54c54022bd14ae4603546c01c2b1b8df22d37 -/
section


/-! Polynomial first Fourier-tail caps, with the profile constant fixed
before the original input and its label geometry. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstDivisorCommonBound CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local instance firstCoarsePowerDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def firstAbsoluteProfileConstant (N : ℕ) (F U b₁ b₂ B₁ B₂ : ℝ) : ℝ :=
  2*128^(N+2)*(max 1 F)^N*B₁*B₂*(max 1 U)^N*max 1 b₁*max 1 b₂

lemma originalAbsoluteProfile_uniform {ι : Type*} [Fintype ι]
    (s : Input ι) (N : ℕ) (F U b₁ b₂ B₁ B₂ : ℝ)
    (hN : Fintype.card ι ≤ N) (hF : ∀ i, s.M i ≤ F)
    (hU : s.upper ≤ U) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    originalAbsoluteProfile s B₁ B₂ ≤ firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂ := by
  have hp : (∏ i, s.M i) ≤ (max 1 F)^N := by
    calc
      _ ≤ ∏ _i : ι, max 1 F := Finset.prod_le_prod₀
        (fun i _ => zero_le_one.trans (s.M_ge_one i))
        (fun i _ => (hF i).trans (le_max_right _ _))
      _ = (max 1 F)^Fintype.card ι := by simp
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) hN
  have h128 : (128:ℝ)^(Fintype.card ι+2) ≤ 128^(N+2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hu : (max 1 s.upper)^Fintype.card ι ≤ (max 1 U)^N :=
    (pow_le_pow_left₀ (by positivity) (max_le_max le_rfl hU) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hN)
  have hm : 0 ≤ ∏ i, s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
  unfold originalAbsoluteProfile firstAbsoluteProfileConstant
  gcongr

lemma firstAbsoluteProfileConstant_nonneg (N : ℕ) (F U b₁ b₂ B₁ B₂ : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    0 ≤ firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂ := by
  unfold firstAbsoluteProfileConstant
  positivity

theorem original_common_coarse_projector_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (F U b₁ b₂ B₁ B₂ D : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hD : 0 ≤ D)
    (s : Input ι) (R seed C : Ideal O) (hC : Supported C) (Ds : Finset (Ideal O))
    (W : Ideal O → 𝓢(ℝ,ℂ)) (K : Ideal O → ℝ) (Z A B J : ℝ)
    (hZ : 1 ≤ Z) (hJ : 0 ≤ J)
    (hN : Fintype.card ι ≤ N) (hF : ∀ i, s.M i ≤ F)
    (hU : s.upper ≤ U) (hb₁ : s.b₁ ≤ b₁) (hb₂ : s.b₂ ≤ b₂)
    (hz₁ : s.W₁ 0 = 0) (hz₂ : s.W₂ 0 = 0)
    (hbound₁ : ∀ x, ‖s.W₁ x‖ ≤ B₁) (hbound₂ : ∀ x, ‖s.W₂ x‖ ≤ B₂)
    (hK : ∀ L ∈ Ds, 0 < K L) (hKcap : ∀ L ∈ Ds, K L ≤ Z^J)
    (hW : ∀ L ∈ Ds, diagonalControl (W L) ≤ D)
    (hsource : sourceRadius s ≤ Z^B) (hvolume : volume s.toData ≤ Z^A) :
    (∑ L ∈ Ds, coarse (original s R seed) C hC L (W L) (K L)) ≤
      (volume s.toData/(C.absNorm : ℝ))*
        ((128*D*(firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2)*Z^(J+2*B+A)) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hc : (1:ℝ) ≤ C.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hp := originalAbsoluteProfile_uniform s N F U b₁ b₂ B₁ B₂ hN hF hU hb₁ hb₂ hB₁ hB₂
  have hp0 : 0 ≤ originalAbsoluteProfile s B₁ B₂ := by
    unfold originalAbsoluteProfile
    have hm : 0 ≤ ∏ i, s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
    positivity
  have hv := CenteredMomentSourceInputTailUniform.volume_pos s
  have hh := original_common_coarse_projector_sum s R seed C hC Ds W K (Z^B) (D*Z^J) B₁ B₂
    (by positivity) (by positivity) hK
    (fun L hL => mul_le_mul (hW L hL)
      (max_le (Real.one_le_rpow hZ hJ) (hKcap L hL)) (by positivity) hD)
    hB₁ hB₂ hz₁ hz₂ hbound₁ hbound₂ hsource
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hv.le (zero_le_one.trans hc))
  calc
    _ ≤ 128*(D*Z^J)*(firstAbsoluteProfileConstant N F U b₁ b₂ B₁ B₂)^2*(Z^B)^2*Z^A := by
      apply (div_le_self (by positivity) hc).trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0 hp 2) (by positivity)) (sq_nonneg _))
        hvolume hv.le (by positivity)
    _ = _ := by
      rw [←Real.rpow_two (Z^B),←Real.rpow_mul hz.le]
      simp only [Real.rpow_add hz]
      rw [show B*2 = 2*B by ring]
      ring

#print axioms original_common_coarse_projector_power
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstCoarsePower -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighKernel ; sha256 f7347186477984fece148f59a8187cf971fefc9ca52e9b6e2bbbd9f2fe8dc02f -/
section







/-! The high retained source estimate with every buffered product
constructed internally from its literal source coefficient identities. -/
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
open CenteredMomentSectorLocalization
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

theorem actual_joint_high_kernel_contribution
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
    (Wkernel : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (tailA tailV targetLower plainBound₁ plainBound₂ : ℝ)
    (hplainBound₁ : 0 ≤ plainBound₁) (hplainBound₂ : 0 ≤ plainBound₂)
    (hplainNorm₁ : ∀ x, ‖W₁ x‖ ≤ plainBound₁) (hplainNorm₂ : ∀ x, ‖W₂ x‖ ≤ plainBound₂) :
    ∃ profileBound : ℕ → ℝ, (∀ k, 0 < profileBound k) ∧
    ∃ (τ ν : ℝ) (orders : Finset Slot → ℕ) (N Nkernel : ℕ) (C : ℝ),
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
        (z : JointReconstructionLabel → O) (t K Radius : JointReconstructionLabel → ℝ)
        (n : JointReconstructionLabel → Fin 4 → ℤ) (rayWeight : JointReconstructionLabel → ℂ)
        (σ freq : JointReconstructionLabel → Slot → ℝ)
        (θ : JointReconstructionLabel → Slot → RayQuotient.Characters M H)
        (slotWidth : JointReconstructionLabel → Slot → ℝ)
        (aSource : ℝ), 0 < aSource →
      (∀ v ∈ S, ‖rayWeight v‖ ≤ 1) →
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
      ∀ (parentL parentR : JointReconstructionLabel → JointParentLabel η)
        (NL : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentL v).val (w v).val)
        (NR : ∀ v, CenteredMomentNaturalRowSource.NaturalRow (parentR v).val (w v).val)
        (punctureL punctureR : JointReconstructionLabel → Ideal O),
      (∀ v, punctureL v ≠ 0) → (∀ v, punctureR v ≠ 0) →
      (∀ v ∈ S, (s v).input.W₁ = W₁ ∧ (s v).input.W₂ = W₂) →
      (∀ v ∈ S, CenteredMomentAllocatedRayDictionary.Matches M H hH (s v).input
        ηcommon (θ v) (slotWidth v) (σ v) (freq v) Wslot bslot Z) →
      (∀ v ∈ S, ∀ height : ℝ, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent (s v).leftRay)
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.1)))
        (s v).toKernelLabel.frequency (z v) height J =
        CenteredMomentHeckeExpansion.rowWeight (parentL v).val
          (fixedBadMask*idealGenerator (punctureL v)) 1 (w v).val height J) →
      (∀ v ∈ S, ∀ height : ℝ, ∀ J : Ideal O, CenteredMomentHeckeExpansion.rowWeight
        (CenteredMomentChildRows.childCharacter (s v).parent ((s v).rightRay⁻¹))
        (fixedBadMask*idealGenerator ((s v).puncture*((s v).firstCommon*(s v).second.val.2)))
        (s v).toKernelLabel.frequency (-(z v)) height J =
        CenteredMomentHeckeExpansion.rowWeight (parentR v).val
          (fixedBadMask*idealGenerator (punctureR v)) 1 (w v).val height J) →
      (∀ v ∈ S, (s v).input.X₁ ≤ (Z^d)^Rwidth ∧ (s v).input.X₂ ≤ (Z^d)^Rwidth ∧
        (s v).input.Y₁ ≤ (Z^d)^Rwidth ∧ (s v).input.Y₂ ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ j, 1 ≤ (s v).input.P j ∧ (s v).input.P j ≤ (Z^d)^Rwidth) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NL v).character (punctureL v)) label).modulus.absNorm ≤ Z^d) →
      (∀ v ∈ S, ∀ label, (bufferedProductFamily M H hH η₀
        (CenteredMomentNaturalRowSource.excluded (NR v).character (punctureR v)) label).modulus.absNorm ≤ Z^d) →
      (∀ ξ u₁ u₂ : ℝ, ‖ξ‖ ≤ Z^ν → ‖u₁‖ ≤ Z^ν → ‖u₂‖ ≤ Z^ν → ∀ v ∈ S, |(t v+2*Real.pi*(u₁-ξ))|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ ∧ |(t v+2*Real.pi*(u₂-(-ξ)))|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux → (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ v ∈ S, ∀ j, σmin ≤ σ v j ∧ σ v j ≤ σmax) →
      (∀ ξ u₁ u₂ : ℝ, ‖ξ‖ ≤ Z^ν → ‖u₁‖ ≤ Z^ν → ‖u₂‖ ≤ Z^ν → ∀ v ∈ S, ∀ j, |(t v+2*Real.pi*(u₁-ξ))+freq v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ ∧
        |(t v+2*Real.pi*(u₂-(-ξ)))+freq v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      ∀ (A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ : ℝ),
      2*b₂ = c₂+d₂ →
      (∀ ξ u₁ u₂ : ℝ, ‖ξ‖ ≤ Z^ν → ‖u₁‖ ≤ Z^ν → ‖u₂‖ ≤ Z^ν → ∀ v ∈ S, ∀ q ∈ (s v).activeFullRetainedFiber (Ds v) ((t v+2*Real.pi*(u₁-ξ))) ((t v+2*Real.pi*(u₂-(-ξ)))) (dyadicScale (n v 2)) (dyadicScale (n v 3)) (z v),
        (s v).fullLeftLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-c₂+lengthLoss ∧
        (s v).fullRightLength Z q+Real.logb Z (max 1 b₁*max 1 b₂plain) ≤ A-c-d₂+lengthLoss) →
      67/100 ≤ 2*p.lower-1 → 2*p.lower-1 ≤ 3/4 → A ≤ 883/1000 →
      0 ≤ π → π ≤ c → π ≤ d₁ → R₁ ≤ π →
      0 ≤ R₀ → 0 ≤ E → 0 ≤ Bc → L ≤ 5*(R₁-R₀) →
      0 ≤ b₂ → g₂ ≤ b₂ → 0 ≤ t₂cost → 0 ≤ geometryLoss → 0 ≤ lengthLoss →
      W ≤ 1-R₁-max (c-d₁) 0+L-6*(3/500)+geometryLoss → P ≤ π-R₁-E+R₀+missingLoss →
      omegaLoss+fiberLoss+loss+heightLoss+geometryLoss+lengthLoss+missingLoss ≤ 144011/109800000 →
      A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss ≤ tailA →
      (∀ v ∈ S, CenteredMomentExceptionalAmplitudePair.volume (s v).input.toData ≤ Z^tailV) →
      targetLower ≤ π+A-c+R₁+E+Bc-144011/109800000 →
      (∑ v ∈ S, ∑ D ∈ Ds v,
        ‖(((1+SecondKernelLabel.kernelScale (n v))^decay : ℝ) : ℂ) *
          ((UniqueFactorizationMonoid.moebius D : ℂ)*
            ((Z^(A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss) : ℝ) : ℂ)*rayWeight v) *
          ((s v).withProjector D).toKernelLabel.kernelRow (t v) (z v) Wkernel (K v) (Radius v) (n v)‖) ≤
        C*(retainedProfileEnvelope S s aSource+128/aSource*(originalAbsoluteEnvelope S s plainBound₁ plainBound₂)^2+1)*Z^(π+A-c+R₁+E+Bc-144011/109800000) := by
  obtain ⟨profileBound,hprofile,τ,ν,orders,N,Ch,hν,hντ,hτdet,hheight,horders,hCh,hhigh⟩ :=
    actual_joint_high_source_matches_contribution η η₀ Q hQtop hQ72 hQη hβ M H hH hQM hQη₀ S₀
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
      V Aprofile Bprofile hA hVs hV ηcommon hanchor Wslot hVslot bslot hBslot
      Rwidth dmax ε e κ ηaux σmin σmax productLoss populationLoss loss B
      hRw hdmax hε he he' hκ hκone hη hbudget hprimebudget hproductLoss hpopulationLoss hB hloss
      τdetector dmin heightLoss I hτdetector hdmin hheightLoss
      W₁ W₂ a₁ b₁ a₂ b₂plain ha₁ ha₂ hs₁ hW₁ hs₂ hW₂ lo hi fiberLoss hfiberLoss
  obtain ⟨Nkernel,Ck,hCk,hkernel⟩ := joint_second_kernel_from_local_retained_absolute_uniform
    Wkernel decay ν (tailA+(16*B+1)+2*B+2*B+tailV) targetLower hν
  refine ⟨profileBound,hprofile,τ,ν,orders,N,Nkernel,(Ck+1)*(Ch+1),hν,hντ,hτdet,hheight,horders,
    mul_pos (by linarith) (by linarith),?_⟩
  filter_upwards [hhigh,eventually_joint_coarse_population B hB] with Z hZ hcoarse
  refine ⟨hZ.1,?_⟩
  intro d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
    hsup heq hproj hbin hnorm hNw hNr s Ds z t K Radius n rayWeight σ freq θ slotWidth aSource haSource
    hray hsourceIntervals hsourceNorm hprojectorNorm hphysical parentL parentR NL NR punctureL punctureR
    hpunctureL hpunctureR hplain hmatch hrowL hrowR hscale hprimeScale
    hcondL hcondR hfreq hfour htwo hσrange hslotfreq
    A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂ hlength
    hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
    hgeometryLoss hlengthLoss hW hP htotal htailA htailVolume htarget
  let outside := A-min c d₁+R₁+E-1+5*(3/500)+g₂-t₂cost-b₂+omegaLoss
  let target := π+A-c+R₁+E+Bc-144011/109800000
  let envelope := retainedProfileEnvelope S s aSource
  have henv : 0 ≤ envelope := retainedProfileEnvelope_nonneg S s aSource
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hlocal (ξ u₁ u₂ : ℝ) (hξ : ‖ξ‖ ≤ Z^ν) (hu₁ : ‖u₁‖ ≤ Z^ν) (hu₂ : ‖u₂‖ ≤ Z^ν) :
      secondProjectedJointRetained S s Ds t n z (Z^outside) ξ u₁ u₂ ≤ (Ch*envelope)*Z^target := by
    have hh := hZ.2 d P W hd hdmax' hbase hT hPB hWB p hp i hi hheightBin unit S w hw R hR
      hsup heq hproj hbin hnorm hNw hNr s Ds z
      (fun v => t v+2*Real.pi*(u₁-ξ)) (fun v => t v+2*Real.pi*(u₂-(-ξ)))
      (fun v => dyadicScale (n v 2)) (fun v => dyadicScale (n v 3))
      σ freq θ slotWidth aSource haSource hsourceIntervals hsourceNorm hprojectorNorm hphysical
      parentL parentR NL NR punctureL punctureR hpunctureL hpunctureR hplain hmatch
      (fun v hv => hrowL v hv _) (fun v hv => hrowR v hv _) hscale hprimeScale hcondL hcondR
      (hfreq ξ u₁ u₂ hξ hu₁ hu₂) hfour htwo hσrange (hslotfreq ξ u₁ u₂ hξ hu₁ hu₂)
      A c d₁ π R₁ R₀ E Bc L b₂ g₂ t₂cost omegaLoss geometryLoss lengthLoss missingLoss c₂ d₂ hb₂
      (hlength ξ u₁ u₂ hξ hu₁ hu₂) hδ hδtop hAtop hp₀ hpc hpd hRp hR₀ hE hBc hL hb₂₀ hg₂ ht₂
      hgeometryLoss hlengthLoss hW hP htotal
    exact hh
  have htailB : (S.card : ℝ) ≤ Z^(16*B+1) := by
    apply hcoarse.2 unit S (fun v hv => by rw [←hw v hv]; exact (w v).property)
      hsup heq hproj hnorm
    · intro v hv
      rw [←hw v hv]
      exact (hNw v hv).trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hWB)
    · intro v hv
      rw [←hw v hv]
      exact (hNr v hv).trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hPB)
  have hWzero₁ : W₁ 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt ha₁) (hs₁ hn).1
  have hWzero₂ : W₂ 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt ha₂) (hs₂ hn).1
  have habsolute := second_projected_absolute_physical_power S s Ds n Z (Z^outside)
    tailA (16*B+1) (2*B) (2*B) tailV plainBound₁ plainBound₂ aSource hZpos (by positivity)
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le htailA) htailB hplainBound₁ hplainBound₂ haSource
    (fun v hv => by
      rcases hplain v hv with ⟨hl,hr⟩
      rw [hl,hr]
      exact ⟨hWzero₁,hWzero₂,hplainNorm₁,hplainNorm₂⟩)
    htailVolume hprojectorNorm hsourceNorm hphysical
  let Eabs := 128/aSource*(originalAbsoluteEnvelope S s plainBound₁ plainBound₂)^2
  have hEabs : 0 ≤ Eabs := by positivity
  have hh := hkernel target htarget S s Ds t K Radius n z rayWeight hray
    Z (Z^outside) (Ch*envelope) Eabs hZ.1.le (by positivity) (by positivity) hEabs
    hlocal habsolute
  apply (show _ ≤ Ck*((Ch*envelope+Eabs)*Z^target) from by
    simpa only [mul_assoc] using hh).trans
  have hconst : Ck*(Ch*envelope+Eabs) ≤ (Ck+1)*(Ch+1)*(envelope+Eabs+1) := by
    nlinarith [mul_nonneg hCk henv,mul_nonneg hCh.le henv,mul_nonneg hCk hCh.le,
      mul_nonneg hCk hEabs,mul_nonneg hCh.le hEabs,
      mul_nonneg (mul_nonneg hCk hCh.le) hEabs]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hZpos.le target)

end FixedData
#print axioms actual_joint_high_kernel_contribution
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighKernel -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowKernelBridge ; sha256 ffa293a62f4a4c453d36a6fa0e9c44a77e6e845b9c748f7719c95f4392def696 -/
section


/-! Bounded-frequency low estimates pass through the actual second kernel;
outside the cube the original Input coefficient mass supplies the bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

theorem actual_second_kernel_of_local_values
    (W : 𝓢(ℝ,ℂ)) (decay : ℕ) (ν tailRows tailV tailCommon lower tailSaving : ℝ) (hν : 0 < ν) (htailRows : 0 ≤ tailRows) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (s : CommonSecondKernelLabel ι) (Ω : Finset O) (t K Radius : ℝ) (n : Fin 4 → ℤ)
      (Z target E B₁ B₂ aSource : ℝ), 1 < Z → lower ≤ target → 0 ≤ E → 0 ≤ B₁ → 0 ≤ B₂ → 0 < aSource →
      s.input.W₁ 0 = 0 → s.input.W₂ 0 = 0 →
      (∀ x, ‖s.input.W₁ x‖ ≤ B₁) → (∀ x, ‖s.input.W₂ x‖ ≤ B₂) →
      (∀ z ∈ Ω, normValue z ≤ Z^tailRows) → volume s.input.toData ≤ Z^tailV →
      (((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ Z^tailCommon) →
      (((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ Z^tailCommon) →
      aSource*volume s.input.toData/((s.firstCommon*s.second.val.1).absNorm : ℝ) ≤ dyadicScale (n 2) →
      aSource*volume s.input.toData/((s.firstCommon*s.second.val.2).absNorm : ℝ) ≤ dyadicScale (n 3) →
      (∀ θ u v : ℝ, ‖θ‖ ≤ Z^ν → ‖u‖ ≤ Z^ν → ‖v‖ ≤ Z^ν →
        (∑ z ∈ Ω, ‖s.toKernelLabel.leftValue (t+2*Real.pi*(u-θ)) z (dyadicScale (n 2))‖ *
          ‖s.toKernelLabel.rightValue (t+2*Real.pi*(v-(-θ))) z (dyadicScale (n 3))‖) ≤ E*Z^target) →
      (∑ z ∈ Ω, ‖(((1+SecondKernelLabel.kernelScale n)^decay : ℝ) : ℂ)*
        s.toKernelLabel.kernelRow t z W K Radius n‖) ≤
        C*((E+(128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2*Z^(-tailSaving))*Z^target) := by
  obtain ⟨N,hpoly⟩ := three_variable_polynomial_extension_lower ν (tailRows+tailCommon+tailV) (lower-tailSaving) hν
  obtain ⟨C,hC,hkernel⟩ := joint_second_kernel_norm_sum_from_values W decay N N N
  refine ⟨N,C,hC,?_⟩
  intro ι instF instD s Ω t K Radius n Z target E B₁ B₂ aSource hZ htarget hE hB₁ hB₂ haSource hz₁ hz₂ hb₁ hb₂
    hnorm hvolume hcommonL hcommonR hphysicalL hphysicalR hlocal
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hmass := actual_common_absolute_mass s B₁ B₂ hB₁ hB₂ hz₁ hz₂ hb₁ hb₂
  have hprofile : 0 ≤ originalAbsoluteProfile s.input B₁ B₂ := by
    unfold originalAbsoluteProfile
    have hM : 0 ≤ ∏ j,s.input.M j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (s.input.M_ge_one j))
    positivity
  have hrows : (Ω.card : ℝ) ≤ 128*Z^tailRows :=
    DescentFiberCost.finite_element_count_real Ω (Z^tailRows) (Real.one_le_rpow hZ.le htailRows)
      (by intro z hz; simpa only [normValue_eq_embedding] using hnorm z hz)
  have hNL : 0 < ((s.firstCommon*s.second.val.1).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (mul_ne_zero s.hfirst.1 s.toKernelLabel.hC.1))
  have hNR : 0 < ((s.firstCommon*s.second.val.2).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (mul_ne_zero s.hfirst.1 s.toKernelLabel.hD.1))
  have hphysical := physical_sqrt_volume_bound aSource (volume s.input.toData)
    (dyadicScale (n 2)) (dyadicScale (n 3)) _ _ (Z^tailCommon)
    haSource (volume_pos _) (dyadicScale_pos _) (dyadicScale_pos _) hNL hNR (by positivity)
    hphysicalL hphysicalR hcommonL hcommonR
  have henv : s.toKernelLabel.absoluteEnvelope (dyadicScale (n 2)) (dyadicScale (n 3)) ≤
      ((originalAbsoluteProfile s.input B₁ B₂)^2/aSource)*Z^(tailCommon+tailV) := by
    unfold SecondKernelLabel.absoluteEnvelope
    calc
      _ ≤ (Real.sqrt (dyadicScale (n 2)))⁻¹*(Real.sqrt (dyadicScale (n 3)))⁻¹*
          (originalAbsoluteProfile s.input B₁ B₂*volume s.input.toData)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sourceAbsoluteMass_nonneg _ _) hmass 2) (by positivity)
      _ = (originalAbsoluteProfile s.input B₁ B₂)^2*volume s.input.toData*
          (volume s.input.toData/(Real.sqrt (dyadicScale (n 2))*Real.sqrt (dyadicScale (n 3)))) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ ≤ (originalAbsoluteProfile s.input B₁ B₂)^2*volume s.input.toData*(Z^tailCommon/aSource) :=
        mul_le_mul_of_nonneg_left hphysical (mul_nonneg (sq_nonneg _) (volume_pos _).le)
      _ ≤ (originalAbsoluteProfile s.input B₁ B₂)^2*Z^tailV*(Z^tailCommon/aSource) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvolume (sq_nonneg _)) (by positivity)
      _ = _ := by rw [Real.rpow_add hZpos]; ring
  let f := fun θ u v : ℝ => ∑ z ∈ Ω,
    ‖s.toKernelLabel.leftValue (t+2*Real.pi*(u-θ)) z (dyadicScale (n 2))‖ *
    ‖s.toKernelLabel.rightValue (t+2*Real.pi*(v-(-θ))) z (dyadicScale (n 3))‖
  have hglobal (θ u v : ℝ) : f θ u v ≤
      (128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2*Z^(tailRows+tailCommon+tailV) := by
    calc
      _ ≤ (Ω.card : ℝ)*s.toKernelLabel.absoluteEnvelope (dyadicScale (n 2)) (dyadicScale (n 3)) := by
        simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum
          (fun z (_ : z ∈ Ω) => s.toKernelLabel.values_le_absoluteEnvelope
            (t+2*Real.pi*(u-θ)) (t+2*Real.pi*(v-(-θ))) z (dyadicScale (n 2)) (dyadicScale (n 3)))
      _ ≤ (128*Z^tailRows)*(((originalAbsoluteProfile s.input B₁ B₂)^2/aSource)*Z^(tailCommon+tailV)) :=
        mul_le_mul hrows henv (s.toKernelLabel.absoluteEnvelope_nonneg _ _) (by positivity)
      _ = _ := by simp only [Real.rpow_add hZpos]; ring
  have hlocal' (θ u v : ℝ) (hθ : ‖θ‖ ≤ Z^ν) (hu : ‖u‖ ≤ Z^ν) (hv : ‖v‖ ≤ Z^ν) :
      f θ u v ≤ (E*Z^tailSaving)*Z^(target-tailSaving) := by
    apply (hlocal θ u v hθ hu hv).trans_eq
    rw [mul_assoc,←Real.rpow_add hZpos]
    congr 2
    ring
  have hp := hpoly (target-tailSaving) (by linarith) Z (E*Z^tailSaving)
    ((128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2)
    hZ.le (mul_nonneg hE (Real.rpow_nonneg hZpos.le _)) (by positivity) f hlocal' hglobal
  have hk := hkernel Ω (fun _ => s.toKernelLabel) (fun _ => t) (fun _ => K) (fun _ => Radius)
    (fun _ => n) (fun z => z) (fun _ => (1 : ℂ))
    ((E*Z^tailSaving+(128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2)*Z^(target-tailSaving)) (by
      intro θ u v
      simpa only [norm_one,one_mul] using hp θ u v)
  have heq : (E*Z^tailSaving+(128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2)*Z^(target-tailSaving) =
      (E+(128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2*Z^(-tailSaving))*Z^target := by
    rw [sub_eq_add_neg,Real.rpow_add hZpos]
    have hp : Z^tailSaving*Z^(-tailSaving) = 1 := by
      rw [←Real.rpow_add hZpos,add_neg_cancel,Real.rpow_zero]
    calc
      _ = E*Z^target*(Z^tailSaving*Z^(-tailSaving))+
        (128/aSource)*(originalAbsoluteProfile s.input B₁ B₂)^2*Z^(-tailSaving)*Z^target := by ring
      _ = _ := by rw [hp]; ring
  rw [heq] at hk
  simpa only [mul_one] using hk

#print axioms actual_second_kernel_of_local_values
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowKernelBridge -/

/- BEGIN ORIGINAL MODULE Analytic.JointLowReflection ; sha256 8036f063c2c7cafcffedebd7b8851e7f38582ac514572dc515359008f1b03a16 -/
section


/-! The two physical children use opposite row signs. Reflection remains
inside the same fixed dictionary, so their low gates share one bin. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CompletedGauss RayFourExpansion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeExpansion CenteredMomentSourceRectangleMask CenteredMomentHeckeColumnWindow
open CenteredMomentEnergyState CenteredMomentCanonicalFirst CenteredMomentFirstPhysicalSource
open CenteredMomentSecondExceptionalFamily CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

private theorem naturalRow_cast_character {ψ : Character} {x y : O}
    (h : x = y) (N : NaturalRow ψ x) : (h ▸ N : NaturalRow ψ y).character = N.character := by
  cases h
  rfl

theorem jointNatural_negate (η : Character) (w : NonzeroElement)
    (parent : JointParentLabel η) (N : NaturalRow parent.val w.val)
    (R : Ideal O) (hR : R ≠ 0) :
    ∃ ψ : JointParentLabel η, ∃ N' : NaturalRow ψ.val (-w.val),
      ∀ I : Ideal O, idealCoeff (excluded N.character R) I = idealCoeff (excluded N'.character R) I := by
  obtain ⟨ψ,hψ⟩ := jointParentDictionary_reflect η parent
  let N' := naturalRow ψ.val (-w.val) (neg_ne_zero.mpr w.property)
  refine ⟨ψ,N',?_⟩
  intro I
  have hr : rowWeight parent.val fixedBadMask 1 w.val 0 I =
      rowWeight ψ.val fixedBadMask 1 (-w.val) 0 I := by simpa only [neg_neg] using hψ (-w.val) 0 I
  have hLam : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have htwo : (2 : O) ∣ fixedBadMask := dvd_mul_left _ _
  have hm : rowWeight parent.val (fixedBadMask*idealGenerator R) 1 w.val 0 I =
      rowWeight ψ.val (fixedBadMask*idealGenerator R) 1 (-w.val) 0 I := by
    rw [←rowWeight_ideal_mask _ _ _ _ _ hLam htwo,
      ←rowWeight_ideal_mask _ _ _ _ _ hLam htwo,hr]
  have hh := (naturalRow_masked_height N R hR 0 I).trans
    (hm.trans (naturalRow_masked_height N' R hR 0 I).symm)
  simpa only [heightCoeff,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh

lemma secondReconstructedRow_neg_val (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
    (E₁ : Finset (CommonIndex C₁ D₁)) (u : Oˣ)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (U : Finset (CommonIndex C₂ D₂))
    (left : Bool) (z : O) (hz : z ≠ 0) :
    (secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (-z) (neg_ne_zero.mpr hz)).val =
      -(secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z hz).val := by
  dsimp only [secondReconstructedRow]
  ring

variable (M : Ideal O) [NeZero M]
local instance lowReflectionFiniteQuotient : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem eventually_actual_second_reflected_low_gate
    {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
        (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      ∀ (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O), T ≠ 0 → (C₂ ∣ T ∨ D₂ ∣ T) → ∀ χ : RayCharacter,
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.character = family χ → s.puncture = 1 → s.width+Bmask+ξ ≤ d →
      ∀ (Q : Ideal O) (hQM : Q ≤ M) (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}),
      ∀ (z : O) (hz : (supportedNaturalState s).radial.keep (-z)),
      let w := secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left z
        (neg_ne_zero.mp (s.row_ne_zero (-z) hz.1))
      ∀ (τ e a : ℝ) (k : ℕ), 0 < e →
      ∀ (holes : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ label,holes label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right))
        holes hholes a (a+e) (3*(k+1 : ℕ)*Z^τ) w →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k (-z) hz := by
  filter_upwards [eventually_supported_low_gate_of_deleted_common_bin (Slot := Slot)
    M H hH η₀ radial ξ hξ] with Z hgate
  refine ⟨hgate.1,?_⟩
  intro η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F u left C₂ D₂ hC₂ hD₂ hCD U family hfamily
    T hT hCT χ Bmask d s hcharacter hpuncture hwidth Q hQM hQ hQ72 z hz w τ e a k he holes hholes hbin
  have hrows := (Classical.choose_spec (actual_second_side_deleted_dictionary η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F)).2
  obtain ⟨parent,N,hcoeff⟩ := hrows left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ (-z) (s.row_ne_zero (-z) hz.1)
  let wn := secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (-z) (s.row_ne_zero (-z) hz.1)
  have hcancel : firstSideCanceled C₁ D₁ left ≠ 0 := canceledIdeal_ne_zero C₁ D₁ hC₁ _
  obtain ⟨ψ,N',hreflect⟩ := jointNatural_negate η wn parent N (T*firstSideCanceled C₁ D₁ left) (mul_ne_zero hT hcancel)
  have hw : -wn.val = w.val := by
    dsimp only [wn,w]
    rw [secondReconstructedRow_neg_val,neg_neg]
  let NN : NaturalRow ψ.val w.val := hw ▸ N'
  have hreflect' (I : Ideal O) : idealCoeff (excluded N.character (T*firstSideCanceled C₁ D₁ left)) I =
      idealCoeff (excluded NN.character (T*firstSideCanceled C₁ D₁ left)) I := by
    have hNN : NN.character = N'.character := naturalRow_cast_character hw N' 
    rw [hNN]
    exact hreflect I
  apply hgate.2 Bmask d s hwidth η Q hQM hQ hQ72 w ψ NN
    (T*firstSideCanceled C₁ D₁ left) T (mul_ne_zero hT hcancel) hT (-z) hz
  · intro I
    have hh := (hcoeff (naturalRow (family χ) (-z) (s.row_ne_zero (-z) hz.1)) I).trans (hreflect' I)
    rw [excluded_ideal _ T hT,←hcharacter] at hh
    simpa only [hpuncture,excluded_ideal _ T hT,excluded_ideal _ 1 one_ne_zero,
      isCoprime_one_right,ite_true,supportedNaturalState] using hh
  · exact he
  · exact hbin

def lowSignedRow (reflect : Bool) (z : O) : O := if reflect then -z else z

lemma lowSignedRow_ne_zero (reflect : Bool) (z : O) (hz : z ≠ 0) : lowSignedRow reflect z ≠ 0 := by
  cases reflect <;> simp [lowSignedRow,hz]

theorem eventually_actual_second_signed_low_gate
    {Slot : Type*} [Fintype Slot] [Nonempty Slot]
    (η₀ : Character) (radial ξ : ℝ) (hξ : 0 < ξ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (η : Character) (C₁ D₁ : Ideal O) (hC₁ : Supported C₁)
        (E₁ : Finset (CommonIndex C₁ D₁)) (ξ₁ ξ₂ : RayCharacter)
        (F : FixedPair η C₁ D₁ hC₁ E₁ ξ₁ ξ₂),
      let u := firstSideDictionaryUnit η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
      activeConductor C₁ D₁ = (u : O)*∏ i,activePrimary C₁ D₁ i ∧
      ∀ (left : Bool) (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂),
      primeSupport C₂ = primeSupport D₂ →
      ∀ (U : Finset (CommonIndex C₂ D₂)) (family : RayCharacter → Character),
      Family (firstSideCharacter F left) C₂ D₂ hC₂ hD₂ U family →
      ∀ (T : Ideal O), T ≠ 0 → (C₂ ∣ T ∨ D₂ ∣ T) → ∀ (χ : RayCharacter),
      ∀ (Bmask d : ℝ) (s : NaturalState Z Bmask radial),
      s.character = family χ → s.puncture = 1 → s.width+Bmask+ξ ≤ d →
      ∀ (Q : Ideal O) (hQM : Q ≤ M) (hQ : s.fixedModulus = internalQ Q η₀)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72 : O)}),
      ∀ (reflect : Bool) (z : O) (hz : (supportedNaturalState s).radial.keep z),
      let w := secondReconstructedRow C₁ D₁ hC₁ E₁ u C₂ D₂ hC₂ U left (lowSignedRow reflect z)
        (lowSignedRow_ne_zero reflect z (s.row_ne_zero z hz.1))
      ∀ (τ e a : ℝ) (k : ℕ), 0 < e →
      ∀ (holes : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hholes : ∀ label,holes label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH (fun _ : Slot => η₀))
        (internalQ Q η₀) hQ72
        (relativeSlotTranslate_fixedQ M H hH (fun _ : Slot => η₀) (internalQ Q η₀)
          (inf_le_left.trans hQM) (fun _ => inf_le_right))
        holes hholes a (a+e) (3*(k+1 : ℕ)*Z^τ) w →
      NaturalLowGate M H hH (supportedNaturalState s) η₀ Q hQM hQ d τ e a k z hz := by
  filter_upwards [eventually_actual_second_low_gate (Slot := Slot) M H hH η₀ radial ξ hξ,
    eventually_actual_second_reflected_low_gate (Slot := Slot) M H hH η₀ radial ξ hξ] with Z hnormal hreflect
  refine ⟨hnormal.1,?_⟩
  intro η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F u
  obtain ⟨hu,hnormal⟩ := hnormal.2 η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F
  refine ⟨hu,?_⟩
  intro left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ Bmask d s hcharacter hpuncture hwidth
    Q hQM hQ hQ72 reflect z hz w τ e a k he holes hholes hbin
  cases reflect with
  | false =>
      exact hnormal left C₂ D₂ hC₂ hD₂ hCD U family hfamily T hT hCT χ Bmask d s
        hcharacter hpuncture hwidth Q hQM hQ hQ72 z hz τ e a k he holes hholes hbin
  | true =>
      have hh := hreflect.2 η C₁ D₁ hC₁ E₁ ξ₁ ξ₂ F left C₂ D₂ hC₂ hD₂ hCD U family hfamily
        T hT hCT χ Bmask d s hcharacter hpuncture hwidth Q hQM hQ hQ72 (-z)
        (by simpa only [neg_neg] using hz) τ e a k he holes hholes hbin
      simpa only [neg_neg] using hh

#print axioms eventually_actual_second_signed_low_gate
#print axioms jointNatural_negate
#print axioms eventually_actual_second_reflected_low_gate
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointLowReflection -/
