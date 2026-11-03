/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothGermRestrictionAndTransport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.ScalarGermUniqueness

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPScalarContinuation
open MomentSources EisensteinSmoothGerms

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

theorem upgrade_of_independent_smooth_germ {C D : ScalarContinuation R Q}
    {v : R.A.UnitQuotient} (H : ScalarGerm C v) (G : IndividualSmoothGerm D v) :
    ∃ J : IndividualSmoothGerm C v,
      J.radius ≤ H.radius ∧ ∀ s, s ∈ Metric.ball (0 : ℂ) J.radius →
        J.cleared s = (H.cleared s : Functions R) := by
  let ρ := min H.radius G.radius
  have hp : 0 < ρ := lt_min H.radius_pos G.radius_pos
  have hH : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 H.radius :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hG : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 G.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  let J : IndividualSmoothGerm C v := {
    radius := ρ
    radius_pos := hp
    cleared := G.cleared
    clears := by
      intro s hs hn
      rw [← scalar_smooth_cleared_unique H G s hs]
      exact H.clears s (hH hs) hn
    smooth := fun s hs => G.smooth s (hG hs)
    analytic := fun g => (G.analytic g).mono hG
    coefficients := G.coefficients
    coefficients_smooth := G.coefficients_smooth
    compact_smooth_taylor := fun g m K hK hKd r hr hrρ =>
      G.compact_smooth_taylor g m K hK hKd r hr (hrρ.trans_le (min_le_right _ _)) }
  exact ⟨J, min_le_left _ _, fun s hs => (scalar_smooth_cleared_unique H G s hs).symm⟩

end DedekindZetaZeroFree.KPScalarContinuation

end
