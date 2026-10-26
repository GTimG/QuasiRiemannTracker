import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalProfiles
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

/-- On a surviving rectangle, the retained pair is exactly the two clipped
plain profiles used by the literal positive-row energy. -/
theorem actual_clipped_pair (a b : ℝ) (ha : 0<a) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀i,0<U i) (hret : ∀i,1≤U i*b) (i : Fin 2) :
    ((retainedPair a b ha p U hU 0).profile i : ℝ→ℂ) =
      dilated (p.profile i) (clipDilation (U i)) := by
  funext x
  change (sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) 0 x = _
  rw [Plain.profile_retained _ _ _ _ (hret i)]
  simpa only [sourcePlain,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,dilated] using
    retainedProfile_apply (p.profile i) a b ha (p.support i) ((p.profile i).smooth ⊤)
      (U i) (hU i) (hret i) 0 x

/-- The finite seminorm controls are chosen before both moving clipping
scales. At zero extra height the old uniform bound has no height loss. -/
theorem clipped_pair_control (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0<U i,
      (retainedPair a b ha p U hU 0).control S≤C*p.control T := by
  obtain ⟨n,T,C,hC,hbound⟩ := retained_pair_control a b ha S
  refine ⟨T,C,hC,?_⟩
  intro p U hU
  simpa using hbound p U hU 0

end
end OAI.SevenEighths.Cycle61FinalProfiles
#print axioms OAI.SevenEighths.Cycle61FinalProfiles.actual_clipped_pair
#print axioms OAI.SevenEighths.Cycle61FinalProfiles.clipped_pair_control
