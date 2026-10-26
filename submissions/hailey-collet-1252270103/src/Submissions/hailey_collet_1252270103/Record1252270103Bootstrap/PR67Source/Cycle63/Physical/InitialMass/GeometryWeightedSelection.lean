import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAllocationMass
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryColumnFibres
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic

/-- Variable label mass stays inside the selected sum, including labels
whose mass vanishes. No maximum over the varying masses is introduced. -/
theorem joint_variable_mass_selection {Label : Type*} [Fintype Label]
    {β : Label→Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (mass : Label→ℝ) (W E : ℝ) (hW : 0≤W)
    (hw : ∀l a,0≤weight l a) (hc : ∀l a,0≤ cost l a)
    (hm : ∀l,0≤ mass l) (hmass : ∀l,∑a,weight l a≤W*mass l)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∀l,weight l.val (pick l)≠0) →
      (∑l : S,mass l.val*cost l.val (pick l))≤E) :
    (∑l,∑a,weight l a*cost l a)≤W*E := by
  have hzero (l : Label)(h : mass l=0)(a : β l) : weight l a=0 := by
    have ht := (Finset.single_le_sum (fun a _=>hw l a) (Finset.mem_univ a)).trans (hmass l)
    rw [h,mul_zero] at ht
    exact le_antisymm ht (hw l a)
  have hh := joint_supported_weighted_selection
    (fun l a=>weight l a/mass l) (fun l a=>mass l*cost l a) W E hW
    (fun l a=>div_nonneg (hw l a) (hm l)) (fun l a=>mul_nonneg (hm l) (hc l a))
    (by
      intro l
      by_cases hz : mass l=0
      · simp only [hz,div_zero,Finset.sum_const_zero]; exact hW
      · rw [←Finset.sum_div]
        exact (div_le_iff₀ (lt_of_le_of_ne (hm l) (Ne.symm hz))).mpr (hmass l))
    (by
      intro S pick hne
      exact hjoint S pick (fun l hw0=>hne l (by simp [hw0])))
  have heq (l : Label)(a : β l) :
      weight l a/mass l*(mass l*cost l a)=weight l a*cost l a := by
    by_cases hz : mass l=0
    · simp [hz,hzero l hz a]
    · field_simp
  simpa only [heq] using hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
