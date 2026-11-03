/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/SelectedJacquet/SelectedFourierGerm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedFourierChamber
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedCompactGerm

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory Filter
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def complexFourierExtraction (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq] :
    C(KPAdditiveQuotient F, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ q, h q * star (adelicTraceQuotientCharacter F q : ℂ) ∂dq
      map_add' := fun h k => by
        simp only [ContinuousMap.add_apply, add_mul]
        apply integral_add
        all_goals
          exact (Continuous.mul (by fun_prop)
            ((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
      map_smul' := fun c h => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _ }
    (dq.real Set.univ) (fun h => by
      change ‖∫ q, h q * star (adelicTraceQuotientCharacter F q : ℂ) ∂dq‖ ≤ dq.real Set.univ * ‖h‖
      rw [mul_comm]
      apply norm_integral_le_of_norm_le_const
      apply Eventually.of_forall
      intro q
      simpa only [norm_mul, norm_star, Circle.norm_coe, mul_one] using h.norm_coe_le_norm q)

theorem selected_cleared_fourier_integrable (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R) :
    Integrable (fun q => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  exact (CompactPeriodAnalyticity.CompactPeriod.cleared_integrable T v s hs g).mul_bdd
    ((continuous_subtype_val.comp (continuous_adelicTraceQuotientCharacter F)).star).aestronglyMeasurable
    (c := 1) (Eventually.of_forall (fun q => by simp))

theorem selected_fourier_cleared_analyticOnNhd (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    AnalyticOnNhd ℂ (fun s => fourier R Q.dq (T.cleared v s) g)
      (Metric.ball (0 : ℂ) T.radius) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hi := selected_cleared_fourier_integrable T v
  have ha := ((complexFourierExtraction Q.dq).differentiable.comp_differentiableOn
    (CompactPeriodAnalyticity.UpperPeriodContinuation.clearedIntegrand_holomorphic T v g)).analyticOnNhd Metric.isOpen_ball
  intro s hs
  apply (ha s hs).congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hs] with t ht
  change complexFourierExtraction Q.dq
    (CompactPeriodAnalyticity.UpperPeriodContinuation.clearedIntegrand T v t g) = _
  unfold complexFourierExtraction MomentSources.fourier
  apply integral_congr_ae
  filter_upwards with q
  rw [CompactPeriodAnalyticity.UpperPeriodContinuation.clearedIntegrand_apply T v t ht g q]

end DedekindZetaZeroFree.SheetRescaling

end
