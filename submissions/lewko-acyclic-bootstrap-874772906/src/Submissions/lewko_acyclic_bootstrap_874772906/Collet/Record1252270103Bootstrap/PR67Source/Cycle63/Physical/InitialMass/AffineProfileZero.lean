import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentFiniteProfileExceptional

/-- A profile supported away from zero vanishes at zero. -/
theorem profile_zero_of_pos {ap bp : ℝ} (p : Profiles ap bp) (hap : 0 < ap) (i : Fin 2) : p.profile i 0 = 0 := by
  by_contra h
  have hh := (p.support i h).1
  linarith

/-- Profiles supply the actual full-source zero gate. -/
theorem affine_profile_zero (p : Profiles (1/4) (9/4)) (i : Fin 2) : p.profile i 0 = 0 :=
  profile_zero_of_pos p (by norm_num) i

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
