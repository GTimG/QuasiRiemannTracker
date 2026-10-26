/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.SecondRetainedContraction
import Candidate.Cycle63.Physical.InitialMass.SecondColumnReindex

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- One label's complete positive normalized energy, retaining both rays and
all residual projectors. Restricting the outer labels does not alter this term. -/
def secondNormalizedLabelSum (reflected : Bool) (d : SecondInputDatum α)
    (w : ℂ) (t u : ℝ) : ℝ :=
  ∑χ : RayCharacter, ∑ψ : RayCharacter,
    ∑D∈d.block.divisors.filter Squarefree,
      ∑z∈secondLiveColumnRows d.block,
        (‖w‖*d.block.outside*volume d.input.toData)*
          (if reflected then
            ‖normalizedColumn (withHeight d.input (d.τ ψ⁻¹)
              (d.input.t+2*Real.pi*(u-(-t))))
              d.D d.hD d.R d.seed D (-z.val)‖^2
           else
            ‖normalizedColumn (withHeight d.input (d.τ χ)
              (d.input.t+2*Real.pi*(u-t)))
              d.C d.hC d.R d.seed D z.val‖^2)

theorem second_normalized_sum_labels (reflected : Bool)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected d w t u =
      ∑l,secondNormalizedLabelSum reflected (d l) (w l) t u := by
  exact actual_second_column_reindex (fun l=>(d l).block) _

theorem second_normalized_label_nonneg (reflected : Bool)
    (d : SecondInputDatum α) (w : ℂ) (t u : ℝ) :
    0≤ secondNormalizedLabelSum reflected d w t u := by
  unfold secondNormalizedLabelSum
  apply Finset.sum_nonneg; intro χ _
  apply Finset.sum_nonneg; intro ψ _
  apply Finset.sum_nonneg; intro D _
  apply Finset.sum_nonneg; intro z _
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (second_outside_pos _).le)
      (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
  · split <;> exact sq_nonneg _

/-- Dropping labels can only reduce either positive normalized energy. No
count of labels, rays, or residual ideals is introduced. -/
theorem second_normalized_restrict_le (p : Label→Prop) [DecidablePred p]
    (reflected : Bool) (d : Label→SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected (fun l : {l // p l}=>d l.val)
      (fun l=>w l.val) t u ≤ secondNormalizedSum reflected d w t u := by
  rw [second_normalized_sum_labels,second_normalized_sum_labels]
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun l=>secondNormalizedLabelSum reflected (d l) (w l) t u)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun l _ _=>second_normalized_label_nonneg reflected (d l) (w l) t u)

/-- Effective weights are label-local, so the same restriction applies to
exact ratio fibers used by retained contraction. -/
theorem second_normalized_ratio_le (W : 𝓢(ℝ,ℂ)) (r : ℤ)
    (reflected : Bool) (d : Label→SecondInputDatum α) (w : Label→ℂ) (t u : ℝ) :
    secondNormalizedSum reflected
      (fun l : SecondRatioFiber (fun l=>(d l).block) r=>d l.val)
      (secondEffectiveWeight
        (fun l : SecondRatioFiber (fun l=>(d l).block) r=>(d l.val).block)
        (fun l=>w l.val) W) t u ≤
      secondNormalizedSum reflected d
        (secondEffectiveWeight (fun l=>(d l).block) w W) t u := by
  exact second_normalized_restrict_le (fun l=>secondRatioIndex (d l).block=r)
    reflected d (secondEffectiveWeight (fun l=>(d l).block) w W) t u

end
end OAI.SevenEighths.Cycle63InitialMass
