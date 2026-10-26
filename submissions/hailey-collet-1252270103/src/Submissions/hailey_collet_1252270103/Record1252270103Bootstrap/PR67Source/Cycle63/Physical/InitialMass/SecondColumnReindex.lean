import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondNormalizedWindows
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentCommonRadialData
open CenteredMomentCommonLinearNormalization CenteredMomentAmplificationChildInput
open CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O

/-- The original row set with precisely the physical live-row conditions.
No canonical partition or reflection closure is required of `s.rows`. -/
def secondLiveColumnRows (s : SecondBlockSource) : Finset s.rows :=
  Finset.univ.filter (fun z=>logAnnulus s.rho≠0 ∧
    logAnnulus (s.x z.val)≠0 ∧ s.rowWeight z.val≠0)

/-- Residual ideals depend on the source label alone, not on either ray
or the physical row. -/
theorem actual_second_residual_ideals_label {Label : Type*}
    (s : Label→SecondBlockSource) (r : SecondRow s) :
    secondResidualIdeals s r=(s r.1).divisors.filter Squarefree := by
  ext L
  simp only [mem_second_residual_ideals,Finset.mem_filter]

/-- Fix the source label, both rays and residual ideal before summing the
entire physical live-row column. This is an exact finite-sum identity. -/
theorem actual_second_column_reindex {Label β : Type*} [Fintype Label]
    [AddCommMonoid β] (s : Label→SecondBlockSource)
    (f : SecondRow s→ Ideal O→β) :
    (∑r∈secondLiveRows s,∑D∈secondResidualIdeals s r,f r D)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(s l).divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (s l),f ⟨l,χ,ψ,z⟩ D := by
  have hrows : (∑r∈secondLiveRows s,∑D∈secondResidualIdeals s r,f r D)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑z∈secondLiveColumnRows (s l),
          ∑D∈(s l).divisors.filter Squarefree,f ⟨l,χ,ψ,z⟩ D := by
    simp only [actual_second_residual_ideals_label,secondLiveRows,
      secondLiveColumnRows,Finset.sum_filter,Fintype.sum_sigma,Fintype.sum_prod_type]
  rw [hrows]
  refine Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun χ hχ => Finset.sum_congr rfl fun ψ hψ => ?_
  exact Finset.sum_comm

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
