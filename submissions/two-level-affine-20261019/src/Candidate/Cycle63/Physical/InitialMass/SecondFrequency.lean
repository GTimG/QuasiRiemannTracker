import Candidate.Cycle63.Physical.InitialMass.SecondChildCaps
import Candidate.Cycle63.Physical.HighFrequency

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentSectorLocalization
open CenteredMomentSecondRetainedWidth CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource Cycle63Moment Cycle63FinalRadius
open Cycle63HighFrequency

/-- The real nonzero retained second Fourier weight bounds the full literal
joint frequency, with its first inactive and signed numerator factors intact. -/
theorem actual_joint_frequency_log_oriented (reflected left : Bool) (u₀ : O) (unit : FirstSourceLabel→O)
    (l : NonzeroJointSourceLabel left u₀ unit)
    (hC : Supported l.val.1.1.1) (hD : Supported l.val.1.1.2)
    (heq : primeSupport l.val.1.1.1=primeSupport l.val.1.1.2)
    (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b) :
    let C := l.val.1.1.1
    let D := l.val.1.1.2
    let E := l.val.1.2.val
    let c := Real.logb Z ((if reflected then D else C).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then C else D).absNorm:ℝ)
    let Kmain := mainCommonRadius Z d
      (nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z)
      c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/((if reflected then D else C).absNorm:ℝ))^2/Kmain) Z ξ
    let A := (commonFrequencyGenerator l.val.2.1.1 l.val.2.1.2*
      nonunitFrequencyGenerator l.val.2.1.1 l.val.2.1.2 l.val.2.2.val.1)*l.val.2.2.val.2
    retainedWeight R (normValue A)≠0 →
      0≤Real.logb Z (normValue (jointSourceRow left u₀ unit l.val)) ∧
      Real.logb Z (normValue (jointSourceRow left u₀ unit l.val))≤
        Real.logb Z K-Real.logb Z (normValue (activeConductor C D))-max (c-d) 0+
          Real.logb Z (normValue (firstSourceNumerator left l.val.1))-6*a-δ-reserve+
          Real.logb Z (normValue (u₀*unit l.val.1))+
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
  have hSspan : Ideal.span {S}≠0 := Ideal.span_singleton_eq_bot.not.mpr hS
  have hi := main_fourier_frequency_log reflected C D (Ideal.span {S}) hC.1 hD.1
    hSspan heq K V Z (3*a) δ reserve ξ b N hK hV hZ hb
  dsimp only at hi
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one _ l.property),?_⟩
  dsimp only [T,S,F,A,C,D,E,normValue] at hlog hh hi ⊢
  linarith

end
end OAI.SevenEighths.Cycle63InitialMass
