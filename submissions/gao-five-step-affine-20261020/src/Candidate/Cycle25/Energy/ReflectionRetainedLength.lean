/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Moments/ReflectionRetainedLength.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectionLength
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.Cycle25CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (_hM : 0≤M) (hz : 0≤z) (hk : 7/10≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤37*M/48+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤15*M/16+xi := by
  have hkz : 16/5*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤5*M/96 := by linarith
  constructor <;> nlinarith

end SevenEighths.Cycle25CenteredMomentReflectionRetainedLength

end

end OAI
