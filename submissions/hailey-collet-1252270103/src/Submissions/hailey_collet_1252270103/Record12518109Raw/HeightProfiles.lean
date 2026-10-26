/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Raw.Context
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109Raw
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentFiniteProfileExceptional

/-- Original common profiles have one fixed seminorm control at every
height. No source label or quotient dilation enters the control. -/
theorem raw_height_profile_control (a b : ℝ)(ha : 0<a)(S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃T : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(p : Profiles a b)(v : ℝ),
      sourceControl S (rawHeightProfile ha p 0 v)*sourceControl S (rawHeightProfile ha p 1 v)≤
        C*p.control T*(1+|v|)^J := by
  obtain ⟨n,T,C,hC,hprofile⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n+n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro p v
  have h0 : sourceControl S (rawHeightProfile ha p 0 v)≤
      C*sourceControl T (p.profile 0)*(1+|v|)^n := by
    simpa only [sourceControl,rawHeightProfile,Real.norm_eq_abs] using hprofile (p.profile 0) (p.support 0) v
  have h1 : sourceControl S (rawHeightProfile ha p 1 v)≤
      C*sourceControl T (p.profile 1)*(1+|v|)^n := by
    simpa only [sourceControl,rawHeightProfile,Real.norm_eq_abs] using hprofile (p.profile 1) (p.support 1) v
  apply (mul_le_mul h0 h1 (sourceControl_nonneg _ _) (by
    have hp:=sourceControl_nonneg T (p.profile 0)
    positivity)).trans_eq
  unfold Profiles.control
  rw [pow_add]
  ring

end
end OAI.SevenEighths.Record12518109Raw
#print axioms OAI.SevenEighths.Record12518109Raw.raw_height_profile_control
