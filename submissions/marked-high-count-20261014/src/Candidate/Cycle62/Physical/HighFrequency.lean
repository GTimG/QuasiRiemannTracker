import Candidate.Cycle62.Moment.ActualJointDictionary
import Candidate.Cycle62.Moment.CanonicalFirstNorm
import Candidate.Cycle62.Physical.FinalRadius

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle62HighFrequency
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedWidth CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource Cycle62Moment Cycle62FinalRadius
local notation "O" => HeckeFamily.O

/-- Canonical label units leave only the fixed first factor in the norm. -/
theorem fixed_unit_norm (u₀ u : O) (hu : IsUnit u) : normValue (u₀*u)=normValue u₀ := by
  unfold normValue
  rw [Ideal.span_singleton_mul_right_unit hu]

/-- Literal first modulus contains the inactive subset and active conductor.
The two fixed presentation ideals only increase its norm. -/
theorem first_modulus_log_lower (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (normValue (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E))+
      Real.logb Z (normValue (activeConductor C D))≤Real.logb Z (τ.modulus.absNorm:ℝ) := by
  let S := primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  have hS : 0<normValue S := by
    change 0<((Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}).absNorm:ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (subsetGenerator_supported C D hC E).1)
  have hA : 0<normValue (activeConductor C D) := by exact active_norm_pos C D
  have hη : 0<(η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have ht : 0<(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have he : (τ.modulus.absNorm:ℝ)=(η.modulus.absNorm:ℝ)*
      ((Ideal.span {fixedBadMask}).absNorm:ℝ)*((Ideal.span {(72:O)}).absNorm:ℝ)*
      (normValue S*normValue (activeConductor C D)) := by
    rw [hmod]
    simp only [map_mul,Nat.cast_mul,←normValue_mul]
    rfl
  have hf : 0<((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
    by_contra h; have hn := (show (0:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ) by positivity)
    have hz : ((Ideal.span {fixedBadMask}).absNorm:ℝ)=0 := by linarith
    rw [hz] at he; simp only [mul_zero,zero_mul] at he; linarith
  have h72 : 0<((Ideal.span {(72:O)}).absNorm:ℝ) := by
    by_contra h; have hn := (show (0:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) by positivity)
    have hz : ((Ideal.span {(72:O)}).absNorm:ℝ)=0 := by linarith
    rw [hz] at he; simp only [mul_zero,zero_mul] at he; linarith
  have hf1 : (1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
    exact_mod_cast (show 1≤(Ideal.span {fixedBadMask}).absNorm from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hf.ne'))
  have h721 : (1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) := by
    exact_mod_cast (show 1≤(Ideal.span {(72:O)}).absNorm from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h72.ne'))
  have hh : (η.modulus.absNorm:ℝ)*(normValue S*normValue (activeConductor C D))≤(τ.modulus.absNorm:ℝ) := by
    rw [he]; nlinarith [mul_pos hη (mul_pos hS hA),mul_le_mul hf1 h721 (by norm_num) hf.le]
  have hl := Real.logb_le_logb_of_le hZ (mul_pos hη (mul_pos hS hA)) hh
  rw [Real.logb_mul hη.ne' (mul_pos hS hA).ne',Real.logb_mul hS.ne' hA.ne'] at hl
  simpa only [S,add_assoc] using hl

/-- The real nonzero retained second Fourier weight bounds the full literal
joint frequency, with its first inactive and signed numerator factors intact. -/
theorem actual_joint_frequency_log (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit) (η τ : Character)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex l.val.1.1.1 l.val.1.1.2=>P.val)
        l.val.1.2.val*activeConductor l.val.1.1.1 l.val.1.1.2}) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
      0≤Real.logb Z (normValue (jointSourceRow left u₀ unit l.val)) ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤
        Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+Real.logb Z fixedPresentationCost+
          2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z 4 := by
  dsimp only
  intro hret
  let C := l.val.1.1.1
  let D := l.val.1.1.2
  let E := l.val.1.2.val
  let S := primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let F := firstSourceNumerator left l.val.1
  let T := u₀*unit l.val.1
  let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
    nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
  have hfactor : jointSourceRow left u₀ unit l.val=((T*S)*F)*A := joint_source_row_factorization left u₀ unit l.val
  have hn : ((T*S)*F)*A≠0 := hfactor.symm ▸ l.property
  have hT : T≠0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hS : S≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hF : F≠0 := right_ne_zero_of_mul (left_ne_zero_of_mul hn)
  have hA : A≠0 := right_ne_zero_of_mul hn
  have hlog : Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))=
      Real.logb Z (normValue T)+Real.logb Z (normValue S)+Real.logb Z (normValue F)+Real.logb Z (normValue A) := by
    rw [hfactor,normValue_mul,normValue_mul,normValue_mul]
    simp only [Real.logb_mul (normValue_pos _ hT).ne' (normValue_pos _ hS).ne',
      Real.logb_mul (mul_pos (normValue_pos _ hT) (normValue_pos _ hS)).ne' (normValue_pos _ hF).ne',
      Real.logb_mul (mul_pos (mul_pos (normValue_pos _ hT) (normValue_pos _ hS)) (normValue_pos _ hF)).ne' (normValue_pos _ hA).ne']
  have hR := (retained_geometry _ _ _ _ hret).1
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos A hA) (retainedWeight_enclosure _ _ hret).2
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne'] at hh
  have hi := main_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N hK hV hZ hb hmod
  have hm := first_modulus_log_lower η τ C D hC E Z hZ hmod
  dsimp only at hi hm
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one _ l.property),?_⟩
  dsimp only [T,S,F,A,C,D,E] at hlog
  linarith

/-- Completed high-count scale for the actual supported frequency. A
negative proposed scale cannot have a nonzero retained physical row. -/
theorem actual_joint_frequency_bound (left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit) (η τ : Character)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex l.val.1.1.1 l.val.1.1.2=>P.val)
        l.val.1.2.val*activeConductor l.val.1.1.1 l.val.1.1.2}) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
    let q := Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+Real.logb Z fixedPresentationCost+
          2*(N:ℝ)*Real.logb Z b+ξ/2+Real.logb Z 4
    0≤q ∧ normValue (jointSourceRow left u₀ unit l.val)≤Z^q ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤q := by
  dsimp only
  intro hret
  have h := actual_joint_frequency_log left u₀ unit l η τ hC hD heq K V Z a δ reserve ξ b N
    hK hV hZ hb hmod hret
  exact ⟨h.1.trans h.2,(Real.logb_le_iff_le_rpow hZ (normValue_pos _ l.property)).mp h.2,h.2⟩

#print axioms actual_joint_frequency_bound
#print axioms fixed_unit_norm
#print axioms first_modulus_log_lower
#print axioms actual_joint_frequency_log
end
end OAI.SevenEighths.Cycle62HighFrequency
