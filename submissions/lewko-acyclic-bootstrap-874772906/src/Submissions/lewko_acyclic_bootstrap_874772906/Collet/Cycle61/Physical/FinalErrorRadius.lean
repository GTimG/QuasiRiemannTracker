import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.FinalRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

namespace OAI.SevenEighths.Cycle61FinalErrorRadius
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSectorLocalization CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRoot CenteredMomentFirstPhysicalSource
open CenteredMomentSecondRetainedWidth CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn

/-- The volume bound used in the error cutoff applies to the actual twice
allocated child, including extraction from either plain factor. -/
theorem actual_error_radius_admissible {ι : Type*} [Fintype ι]
    (N : ℕ) (b : ℝ) (hb : 1≤b)
    (s : Input ι) (hc : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (p : O) (hp : p≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime (Ideal.span {p}) I)
    (Bp : actualAllocations (child s C R B τ t).pools ((Ideal.span {p})^k))
    (υ : Character) (v K : ℝ) (hK : 0<K) :
    (volume (twiceChild s C R B τ t (Ideal.span {p}) k Bp υ v))^2/K ≤
      (b^N*volume s/((C.absNorm:ℝ)*(normValue p)^k))^2/K := by
  have hQ := Ideal.span_singleton_eq_bot.not.mpr hp
  have hnp := pow_pos (normValue_pos p hp) k
  have hv : volume (twiceChild s C R B τ t (Ideal.span {p}) k Bp υ v) ≤
      b^N*volume s/((C.absNorm:ℝ)*(normValue p)^k) := by
    rw [twiceChild,child_volume _ _ hQ k hslot]
    exact (div_le_div_of_nonneg_right
      (common_volume_le N b hb s hc hs C R B τ t hne) hnp.le).trans_eq (by ring)
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (volume_pos _).le hv 2) hK.le


/-- Exact cutoff identity for the extracted-prime branches, retaining the moving conductor cost. -/
theorem error_inverse_radius_log (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ) (p : O) (k : ℕ) (hp : p≠0)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kerror := errorCommonRadius Z d K0 c (3*a) δ reserve p k
    Real.logb Z (frequencyRadius ((b^N*V/((C.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ)+errorMoving p Z k =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hz : 0<Z := zero_lt_one.trans hZ
  have hnp := normValue_pos p hp
  have hwidth := actual_reference_width η τ C D hC E K Z hK hZ hmod
  unfold frequencyRadius errorCommonRadius nominalLog
  rw [nominal_equal_support C D _ hC.1 hD.1 heq K V]
  simp (disch := positivity) only [Real.logb_mul, Real.logb_div, Real.logb_pow,
    Real.logb_rpow hz hZ.ne']
  unfold errorRemoval
  by_cases h : Real.logb Z (C.absNorm:ℝ)+2*((k:ℝ)*Real.logb Z (normValue p))-errorMoving p Z k ≤ Real.logb Z (D.absNorm:ℝ)
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith

/-- The extracted character's moving conductor is paid exactly once. The
actual second natural conductor then cancels its radical in the retained ball. -/
theorem actual_error_final_width (η τ υ χ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b J : ℝ) (N : ℕ)
    (p : O) (k : ℕ) (hp : p≠0)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b) (hJ : 0<J)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hυ : (υ.modulus.absNorm:ℝ)≤J*(τ.modulus.absNorm:ℝ)*Z^(errorMoving p Z k))
    (G V₂ z : O) (U : Ideal O) (hU : U≠0)
    (hN : χ.modulus.absNorm≤υ.modulus.absNorm*fixedFactor*U.absNorm*(Ideal.span {V₂}).absNorm) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kerror := errorCommonRadius Z d K0 c (3*a) δ reserve p k
    let R := frequencyRadius ((b^N*V/((C.absNorm:ℝ)*(normValue p)^k))^2/Kerror) Z ξ
    retainedWeight R (normValue ((G*V₂)*z))≠0 →
      Real.logb Z (max 1 (4*R/(normValue G*normValue V₂)))+
        Real.logb Z (χ.modulus.absNorm:ℝ) ≤
      (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-
        max (c-d+2*errorRemoval p Z k-errorMoving p Z k) 0-3*a-δ-reserve-
        Real.logb Z (normValue G)+Real.logb Z (U.absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z J+Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hrow
  have hh := retained_log_budget υ χ G V₂ z U hU hN _ Z hZ hrow
  have he := error_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N
    p k hp hK hV hZ hb hmod
  dsimp only at he
  have hτ := norm_pos τ.modulus τ.modulus_ne_bot
  have hυpos := norm_pos υ.modulus υ.modulus_ne_bot
  have hl := Real.logb_le_logb_of_le hZ hυpos hυ
  rw [Real.logb_mul (mul_pos hJ hτ).ne' (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul hJ.ne' hτ.ne', Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hl
  linarith

end
end OAI.SevenEighths.Cycle61FinalErrorRadius
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.error_inverse_radius_log
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.actual_error_final_width
#print axioms OAI.SevenEighths.Cycle61FinalErrorRadius.actual_error_radius_admissible
