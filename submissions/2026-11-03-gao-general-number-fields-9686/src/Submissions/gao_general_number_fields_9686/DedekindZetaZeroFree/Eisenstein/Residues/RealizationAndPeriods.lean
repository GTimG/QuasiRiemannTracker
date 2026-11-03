/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/RealizationAndPeriods.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Residues.FiniteSourceImage
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def realizationScalarContinuation (T : Realization R Q) : ScalarContinuation R Q :=
  ⟨T.E, T.meromorphic, T.chamber⟩

def realizationScalarGerm (T : Realization R Q) (v : R.A.UnitQuotient) :
    ScalarGerm (realizationScalarContinuation T) v where
  radius := T.radius
  radius_pos := T.radius_pos
  cleared := fun s => if hs : s ∈ Metric.ball (0 : ℂ) T.radius then
    ⟨T.cleared v s, (T.smooth v s hs).1⟩ else 0
  clears := by
    intro s hs hn
    simpa only [dif_pos hs, ContinuousMap.coe_mk, realizationScalarContinuation] using
      T.clears v s hs hn
  analytic := by
    intro g
    apply (T.analytic v g).congr Metric.isOpen_ball
    intro s hs
    simp only [dif_pos hs, ContinuousMap.coe_mk]

theorem realizationScalarGerm_cleared (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) :
    ((realizationScalarGerm T v).cleared s : Functions R) = T.cleared v s := by
  simp only [realizationScalarGerm, dif_pos hs, ContinuousMap.coe_mk]

theorem realized_residual_stage (T : Realization R Q) :
    scalarResidualStage (realizationScalarGerm T) =
      Submodule.span ℂ (Set.range T.theta) := by
  unfold scalarResidualStage
  congr 1
  have he : (fun v => ((realizationScalarGerm T v).cleared 0 : Functions R)) = T.theta := by
    funext v
    exact realizationScalarGerm_cleared T v 0 (Metric.mem_ball_self T.radius_pos)
  rw [he]

theorem realized_residual_stage_le_translateSpan (T : Realization R Q) :
    scalarResidualStage (realizationScalarGerm T) ≤ FourierContinuation.translateSpan T := by
  rw [realized_residual_stage]
  apply Submodule.span_le.mpr
  rintro f ⟨v, rfl⟩
  apply Submodule.subset_span
  exact ⟨v, 1, by simp⟩

def realizedSourceResidue (T : Realization R Q) :
    flatScalarStage Q →ₗ[ℂ] FourierContinuation.translateSpan T :=
  (finiteSourceResidue (realizationScalarGerm T)).codRestrict _ (fun x =>
    realized_residual_stage_le_translateSpan T
      (finiteSourceResidue_range_stage (realizationScalarGerm T) ▸
        LinearMap.mem_range_self (finiteSourceResidue (realizationScalarGerm T)) x))

theorem realizedSourceResidue_companion (T : Realization R Q) (v : R.A.UnitQuotient) :
    ((realizedSourceResidue T
      ⟨(Q.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩ : FourierContinuation.translateSpan T) : Functions R) =
      T.theta v := by
  change finiteSourceResidue (realizationScalarGerm T)
    ⟨(Q.flat v).val 0, _⟩ = T.theta v
  rw [finiteSourceResidue_companion]
  exact realizationScalarGerm_cleared T v 0 (Metric.mem_ball_self T.radius_pos)

end DedekindZetaZeroFree.SharedSource

end
