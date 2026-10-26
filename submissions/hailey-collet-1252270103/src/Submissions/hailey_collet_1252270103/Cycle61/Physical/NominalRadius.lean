import Submissions.hailey_collet_1252270103.Cycle61.Physical.FinalRadius

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61NominalRadius
noncomputable section
open scoped Classical
open HeckeFamily ActualEisensteinCubic CenteredMomentFirstScale CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- The nominal radius is computed from the actual common labels, active
radical, subset radical, original volume, and original radial scale. -/
theorem actual_nominal_log (C D E : Ideal O) (hC : C≠0) (hD : D≠0)
    (hE : E≠0) (heq : primeSupport C=primeSupport D) (K V Z : ℝ)
    (hK : 0<K) (hV : 0<V) (_hZ : 1<Z) :
    nominalLog C D E K V Z = 2*Real.logb Z V-Real.logb Z (C.absNorm:ℝ)-
      Real.logb Z (D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+
      Real.logb Z (E.absNorm:ℝ)-Real.logb Z K := by
  have hc := norm_pos C hC
  have hd := norm_pos D hD
  have he := norm_pos E hE
  have hr := active_norm_pos C D
  unfold nominalLog
  rw [nominal_equal_support C D E hC hD heq K V]
  simp (disch := positivity) only [Real.logb_mul,Real.logb_div,Real.logb_pow]
  ring

/-- Specializing the original radial scale to Z^M removes the nominal-radius
gate in the second-zero estimate; only the actual original volume cap remains. -/
theorem actual_nominal_le (C D E : Ideal O) (hC : C≠0) (hD : D≠0)
    (hE : E≠0) (heq : primeSupport C=primeSupport D) (V Z M A : ℝ)
    (hV : 0<V) (hZ : 1<Z) (hvol : V≤Z^A) :
    nominalLog C D E (Z^M) V Z ≤ 2*A-Real.logb Z (C.absNorm:ℝ)-
      Real.logb Z (D.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)+
      Real.logb Z (E.absNorm:ℝ)-M := by
  have hz := zero_lt_one.trans hZ
  rw [actual_nominal_log C D E hC hD hE heq _ _ _ (Real.rpow_pos_of_pos hz _) hV hZ,
    Real.logb_rpow hz hZ.ne']
  have hh := Real.logb_le_logb_of_le hZ hV hvol
  rw [Real.logb_rpow hz hZ.ne'] at hh
  linarith

end
end OAI.SevenEighths.Cycle61NominalRadius
#print axioms OAI.SevenEighths.Cycle61NominalRadius.actual_nominal_log
#print axioms OAI.SevenEighths.Cycle61NominalRadius.actual_nominal_le
