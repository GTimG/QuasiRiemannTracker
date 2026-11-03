/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/FourierPeriodExtraction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.FourierContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

theorem continued_period_integrable (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (hne : s ≠ 0) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => T.E v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  have hi := (cleared_period_integrable T v s hs g).const_mul s⁻¹
  rw [T.clears v s hs hne] at hi
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul] using hi

theorem fourier_clearing (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (hne : s ≠ 0) (g : Group R) :
    fourier R Q.dq (T.cleared v s) g = s * fourier R Q.dq (T.E v s) g := by
  have _hi := continued_period_integrable T v s hs hne g
  rw [T.clears v s hs hne]
  unfold MomentSources.fourier
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul s _

theorem fourier_residue_tendsto (T : Realization R Q) (v : R.A.UnitQuotient) (g : Group R) :
    Tendsto (fun s : ℂ => s * fourier R Q.dq (T.E v s) g) (nhdsWithin 0 {0}ᶜ)
      (nhds (fourier R Q.dq (T.theta v) g)) := by
  have he : (fun s : ℂ => s * fourier R Q.dq (T.E v s) g) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun s => fourier R Q.dq (T.cleared v s) g) := by
    have hb : ∀ᶠ s : ℂ in nhdsWithin 0 {0}ᶜ, s ∈ Metric.ball (0 : ℂ) T.radius :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) T.radius_pos)
    have hn : ∀ᶠ s : ℂ in nhdsWithin 0 {0}ᶜ, s ∈ ({0}ᶜ : Set ℂ) := self_mem_nhdsWithin
    filter_upwards [hb, hn] with s hs hn
    exact (fourier_clearing T v s hs (by simpa using hn) g).symm
  exact ((fourier_cleared_tendsto_zero T v g).mono_left nhdsWithin_le_nhds).congr' he.symm

end DedekindZetaZeroFree.FourierContinuation

end
