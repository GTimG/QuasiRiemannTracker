import OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
import QRH.RobustReflectionGeometry

/-! Apache-2.0 adaptation of OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
OAI/NumberTheory/DirichletL/Moments/ReflectionRetainedLength.lean. Original objects imported unchanged.
Extended theorem names and explicit κ/reserve changes; untrusted until kernel checked. -/
namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma positive_slot_width_drop_extended (M A z xi kappa : ℝ)
    (hM : 0≤M) (hz : 0≤z) (hk : 13/18≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤14*M/15+xi := by
  have hkz : 10/3*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤M/20 := by linarith
  constructor <;> nlinarith

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI
