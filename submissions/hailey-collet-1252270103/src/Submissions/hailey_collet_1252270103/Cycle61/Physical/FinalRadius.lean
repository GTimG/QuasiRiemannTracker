import Submissions.hailey_collet_1252270103.Cycle61.Physical.ExceptionalReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

namespace OAI.SevenEighths.Cycle61FinalRadius
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

/-- This declared second Fourier radius dominates the genuine first common
child's squared volume divided by its physical radius. -/
theorem actual_second_radius_admissible {ι : Type*} [Fintype ι]
    (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t K : ℝ)
    (hK : 0<K) (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B τ t))^2/K≤(b^N*volume s/(C.absNorm:ℝ))^2/K := by
  have hh := common_volume_le N b hb s hcard hs C R B τ t hne
  apply div_le_div_of_nonneg_right _ hK.le
  exact pow_le_pow_left₀ (volume_pos _).le hh 2

/-- The same completed cutoff supplies an actual ball majorant for every
retained row, with no new arithmetic puncture. -/
theorem actual_retained_majorant (R : ℝ) (G V z : O)
    (h : retainedWeight R (normValue ((G*V)*z))≠0) :
    1≤(ballProfile (normValue z/(max 1 (4*R/(normValue G*normValue V))))).re := by
  obtain ⟨_,_,_,_,hz,hu,_⟩ := retained_geometry R G V z h
  have hH : 0<max 1 (4*R/(normValue G*normValue V)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  rw [ballProfile_one _ (div_nonneg (by linarith) hH.le)
    ((div_le_one hH).mpr (hu.trans (le_max_right _ _)))]
  norm_num

/-- All support and fixed-presentation losses are paid by one threshold
chosen before the moving characters, common parts, and retained rows. -/
theorem fixed_radius_loss_eventually (N : ℕ) (b ε : ℝ) (hb : 0<b) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
      Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+
        Real.logb Z (4*(fixedFactor:ℝ))≤ε := by
  have hf := fixedPresentationCost_pos
  have hg : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  let A := fixedPresentationCost*b^(2*N)*(4*(fixedFactor:ℝ))
  have hA : 0<A := by dsimp [A]; positivity
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) A,
    Filter.eventually_gt_atTop (1:ℝ)] with Z hAZ hZ
  refine ⟨hZ,?_⟩
  have hh := Real.logb_le_logb_of_le hZ hA hAZ
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  dsimp [A] at hh
  simp (disch := positivity) only [Real.logb_mul, Real.logb_pow] at hh
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh
  simpa only [Real.logb_mul (by norm_num : (4:ℝ)≠0) hg.ne'] using hh

/-- The second Fourier cutoff uses an upper bound for the actual first-child
volume. Its logarithm keeps the six-amplifier gain from the real main ball. -/
theorem main_inverse_radius_log (η τ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    Real.logb Z (frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ)+
      Real.logb Z (τ.modulus.absNorm:ℝ) =
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve+
        Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2 := by
  dsimp only
  have hc := norm_pos C hC.1
  have hd := norm_pos D hD.1
  have hE := norm_pos _ (subsetGenerator_supported C D hC E).1
  have hR := active_norm_pos C D
  have hz : 0<Z := zero_lt_one.trans hZ
  have hwidth := actual_reference_width η τ C D hC E K Z hK hZ hmod
  unfold frequencyRadius mainCommonRadius nominalLog
  rw [nominal_equal_support C D _ hC.1 hD.1 heq K V]
  simp (disch := positivity) only [Real.logb_mul, Real.logb_div, Real.logb_pow,
    Real.logb_rpow hz hZ.ne']
  by_cases h : Real.logb Z (C.absNorm:ℝ) ≤ Real.logb Z (D.absNorm:ℝ)
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    linarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    linarith

/-- The physical second row cutoff and its actual natural conductor cancel
the nonunit radical. Nonempty support justifies completing the scale at one. -/
theorem actual_main_final_width (η τ χ : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (heq : primeSupport C = primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z a δ reserve ξ b : ℝ) (N : ℕ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hb : 0<b)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (G V₂ z : O) (U : Ideal O) (hU : U≠0)
    (hN : χ.modulus.absNorm≤τ.modulus.absNorm*fixedFactor*U.absNorm*(Ideal.span {V₂}).absNorm) :
    let c := Real.logb Z (C.absNorm:ℝ)
    let d := Real.logb Z (D.absNorm:ℝ)
    let K0 := nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z
    let Kmain := mainCommonRadius Z d K0 c (3*a) δ reserve
    let R := frequencyRadius ((b^N*V/(C.absNorm:ℝ))^2/Kmain) Z ξ
    retainedWeight R (normValue ((G*V₂)*z))≠0 →
      Real.logb Z (max 1 (4*R/(normValue G*normValue V₂)))+
        Real.logb Z (χ.modulus.absNorm:ℝ) ≤
      (Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)-max (c-d) 0-6*a-δ-reserve-
        Real.logb Z (normValue G)+Real.logb Z (U.absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) := by
  dsimp only
  intro hrow
  have hh := retained_log_budget τ χ G V₂ z U hU hN _ Z hZ hrow
  have he := main_inverse_radius_log η τ C D hC hD heq E K V Z a δ reserve ξ b N
    hK hV hZ hb hmod
  dsimp only at he
  linarith

end
end OAI.SevenEighths.Cycle61FinalRadius
#print axioms OAI.SevenEighths.Cycle61FinalRadius.main_inverse_radius_log
#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_main_final_width

#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_second_radius_admissible
#print axioms OAI.SevenEighths.Cycle61FinalRadius.actual_retained_majorant
#print axioms OAI.SevenEighths.Cycle61FinalRadius.fixed_radius_loss_eventually
