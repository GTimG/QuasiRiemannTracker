/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/SelectedJacquet/SelectedCompactGerm.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.JointContinuity
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.ConstantTerms.ChamberIntegrability
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.Complex.CompactMeromorphicFamilies

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

def clearedIntegrand (T : Realization R Q) (v : R.A.UnitQuotient) (s : ℂ)
    (g : Group R) : C(KPAdditiveQuotient F, ℂ) :=
  if hs : s ∈ Metric.ball (0 : ℂ) T.radius then
    ⟨fun q => T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g),
      CompactPeriod.cleared_integrand_continuous T v s hs g⟩
  else 0

theorem clearedIntegrand_apply (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (g : Group R)
    (q : KPAdditiveQuotient F) :
    clearedIntegrand T v s g q = T.cleared v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) := by
  simp only [clearedIntegrand, dif_pos hs, ContinuousMap.coe_mk]

theorem clearedIntegrand_holomorphic (T : Realization R Q) (v : R.A.UnitQuotient)
    (g : Group R) :
    DifferentiableOn ℂ (fun s => clearedIntegrand T v s g)
      (Metric.ball (0 : ℂ) T.radius) := by
  have hc : ContinuousOn (fun p : ℂ × KPAdditiveQuotient F =>
      clearedIntegrand T v p.1 g p.2) (Metric.ball (0 : ℂ) T.radius ×ˢ Set.univ) := by
    apply continuousOn_iff_continuous_restrict.mpr
    let a : (Metric.ball (0 : ℂ) T.radius ×ˢ (Set.univ : Set (KPAdditiveQuotient F))) →
        Metric.ball (0 : ℂ) T.radius × KPAdditiveQuotient F :=
      fun p => (⟨p.val.1, p.property.1⟩, p.val.2)
    have ha : Continuous a :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    apply ((CompactPeriod.cleared_quotient_joint_continuous T v g).comp ha).congr
    intro p
    exact (clearedIntegrand_apply T v p.val.1 p.property.1 g p.val.2).symm
  have hd (q : KPAdditiveQuotient F) :
      DifferentiableOn ℂ (fun s => clearedIntegrand T v s g q)
        (Metric.ball (0 : ℂ) T.radius) := by
    exact (T.analytic v
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g)).differentiableOn.congr
        (fun s hs => clearedIntegrand_apply T v s hs g q)
  exact compact_family_holomorphic _ Metric.isOpen_ball
    (fun s => clearedIntegrand T v s g) hc hd

def localMeromorphicIntegrand (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (g : Group R) : C(KPAdditiveQuotient F, ℂ) :=
  s⁻¹ • clearedIntegrand T v s g

theorem localMeromorphicIntegrand_apply (T : Realization R Q) (v : R.A.UnitQuotient)
    (s : ℂ) (hs : s ∈ Metric.ball (0 : ℂ) T.radius) (hn : s ≠ 0)
    (g : Group R) (q : KPAdditiveQuotient F) :
    localMeromorphicIntegrand T v s g q = T.E v s
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) := by
  change s⁻¹ * clearedIntegrand T v s g q = _
  rw [clearedIntegrand_apply T v s hs, T.clears v s hs hn]
  simp [← mul_assoc, hn]

theorem localMeromorphicIntegrand_meromorphic (T : Realization R Q)
    (v : R.A.UnitQuotient) (g : Group R) :
    MeromorphicOn (fun s => localMeromorphicIntegrand T v s g)
      (Metric.ball (0 : ℂ) T.radius) := by
  intro s hs
  exact (analyticAt_id.meromorphicAt.inv).smul
    (((clearedIntegrand_holomorphic T v g).analyticOnNhd
      Metric.isOpen_ball s hs).meromorphicAt)

end DedekindZetaZeroFree.CompactPeriodAnalyticity.UpperPeriodContinuation

end
