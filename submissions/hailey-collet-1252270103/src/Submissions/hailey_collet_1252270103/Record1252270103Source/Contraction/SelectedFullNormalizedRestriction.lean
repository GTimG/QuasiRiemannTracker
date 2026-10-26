/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Modified-coefficient adaptation of Cycle61 SecondNormalizedRestriction.
The inherited source notices remain required. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedSecondPhysicalRatio
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondColumnReindex
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentLogDyadic CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
open CenteredMomentAddedZeroUniform
open CenteredMomentSecondPhysicalBlock
open Cycle61InitialMass Cycle61Moment
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

def modifiedSecondNormalizedLabelSum (reflected : Bool) (d : SecondInputDatum α)
    (modifier : Tuple d.slots→ℂ) (w : ℂ) (t u : ℝ) : ℝ :=
  ∑χ : RayCharacter,∑ψ : RayCharacter,
    ∑D∈(modifiedDatumBlock d modifier).divisors.filter Squarefree,
      ∑z∈secondLiveColumnRows (modifiedDatumBlock d modifier),
        (‖w‖*d.block.outside*volume d.input.toData)*
          (if reflected then
            ‖modifiedPlainColumn d.input modifier d.D d.hD d.R d.seed D
              (d.τ ψ⁻¹) (d.input.t+2*Real.pi*(u-(-t))) (-z.val)‖^2
           else
            ‖modifiedPlainColumn d.input modifier d.C d.hC d.R d.seed D
              (d.τ χ) (d.input.t+2*Real.pi*(u-t)) z.val‖^2)

theorem modified_normalized_sum_labels (reflected : Bool)
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ)
    (w : Label→ℂ) (t u : ℝ) :
    modifiedSecondNormalizedSum reflected d modifier w t u=
      ∑l,modifiedSecondNormalizedLabelSum reflected (d l) (modifier l) (w l) t u := by
  exact actual_second_column_reindex (fun l=>modifiedDatumBlock (d l) (modifier l)) _

theorem modified_normalized_label_nonneg (reflected : Bool) (d : SecondInputDatum α)
    (modifier : Tuple d.slots→ℂ) (w : ℂ) (t u : ℝ) :
    0≤modifiedSecondNormalizedLabelSum reflected d modifier w t u := by
  unfold modifiedSecondNormalizedLabelSum
  apply Finset.sum_nonneg;intro χ _
  apply Finset.sum_nonneg;intro ψ _
  apply Finset.sum_nonneg;intro D _
  apply Finset.sum_nonneg;intro z _
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (second_outside_pos _).le)
      (CenteredMomentExceptionalAmplitudePair.volume_pos _).le
  · split <;> exact sq_nonneg _

/-- Subtype restriction preserves complete columns and both rays. -/
theorem modified_normalized_restrict_le (p : Label→Prop) [DecidablePred p]
    (reflected : Bool) (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ) (t u : ℝ) :
    modifiedSecondNormalizedSum reflected (fun l : {l // p l}=>d l.val)
      (fun l=>modifier l.val) (fun l=>w l.val) t u≤
      modifiedSecondNormalizedSum reflected d modifier w t u := by
  rw [modified_normalized_sum_labels,modified_normalized_sum_labels]
  rw [←Finset.sum_subtype (Finset.univ.filter p) (by simp)
    (fun l=>modifiedSecondNormalizedLabelSum reflected (d l) (modifier l) (w l) t u)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun l _ _=>modified_normalized_label_nonneg reflected (d l) (modifier l) (w l) t u)

theorem modified_normalized_ratio_le (W : 𝓢(ℝ,ℂ)) (r : ℤ)
    (reflected : Bool) (d : Label→SecondInputDatum α)
    (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ) (t u : ℝ) :
    modifiedSecondNormalizedSum reflected
      (fun l : SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>d l.val)
      (fun l=>modifier l.val)
      (secondEffectiveWeight
        (fun l : SecondRatioFiber (fun l=>modifiedDatumBlock (d l) (modifier l)) r=>
          modifiedDatumBlock (d l.val) (modifier l.val)) (fun l=>w l.val) W) t u≤
    modifiedSecondNormalizedSum reflected d modifier
      (secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W) t u := by
  exact modified_normalized_restrict_le
    (fun l=>secondRatioIndex (modifiedDatumBlock (d l) (modifier l))=r)
    reflected d modifier (secondEffectiveWeight (fun l=>modifiedDatumBlock (d l) (modifier l)) w W) t u

end
end QRH.Record1252270103Source.Contraction
#print axioms QRH.Record1252270103Source.Contraction.modified_normalized_sum_labels
#print axioms QRH.Record1252270103Source.Contraction.modified_normalized_label_nonneg
#print axioms QRH.Record1252270103Source.Contraction.modified_normalized_restrict_le
#print axioms QRH.Record1252270103Source.Contraction.modified_normalized_ratio_le
