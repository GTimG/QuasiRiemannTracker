import Candidate.Cycle63.Physical.InitialMass.SecondNormalizedWindows

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
    (f : SecondRow s→Ideal O→β) :
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
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  exact Finset.sum_comm

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- The left normalized energy is a sum of complete row columns at a
fixed divisor and pair of rays. Its source weight stays inside the identity. -/
theorem actual_second_left_normalized_column_reindex
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.1)
            ((d r.1).input.t+2*Real.pi*(u-t)))
            (d r.1).C (d r.1).hC (d r.1).R (d r.1).seed D r.2.2.2.val‖^2)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*(d l).block.outside*volume (d l).input.toData)*
              ‖normalizedColumn (withHeight (d l).input ((d l).τ χ)
                ((d l).input.t+2*Real.pi*(u-t)))
                (d l).C (d l).hC (d l).R (d l).seed D z.val‖^2 := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

/-- The right energy uses the original live-row filter and the literal
negated Fourier row. No closure of the input row set under negation is assumed. -/
theorem actual_second_right_normalized_column_reindex
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    (∑r∈secondLiveRows (fun l=>(d l).block),
      ∑D∈secondResidualIdeals (fun l=>(d l).block) r,
        (‖w r.1‖*(d r.1).block.outside*volume (d r.1).input.toData)*
          ‖normalizedColumn (withHeight (d r.1).input ((d r.1).τ r.2.2.1⁻¹)
            ((d r.1).input.t+2*Real.pi*(u-(-t))))
            (d r.1).D (d r.1).hD (d r.1).R (d r.1).seed D (-r.2.2.2.val)‖^2)=
      ∑l,∑χ : RayCharacter,∑ψ : RayCharacter,
        ∑D∈(d l).block.divisors.filter Squarefree,
          ∑z∈secondLiveColumnRows (d l).block,
            (‖w l‖*(d l).block.outside*volume (d l).input.toData)*
              ‖normalizedColumn (withHeight (d l).input ((d l).τ ψ⁻¹)
                ((d l).input.t+2*Real.pi*(u-(-t))))
                (d l).D (d l).hD (d l).R (d l).seed D (-z.val)‖^2 := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_residual_ideals_label
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_column_reindex
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_left_normalized_column_reindex
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_right_normalized_column_reindex
