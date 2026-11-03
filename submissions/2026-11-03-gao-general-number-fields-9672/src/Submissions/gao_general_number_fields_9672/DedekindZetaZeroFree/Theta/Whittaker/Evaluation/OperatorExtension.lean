/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Evaluation/OperatorExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.Complex.OperatorWordBounds
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CompactUniformLimits

@[expose] public section

noncomputable section
open scoped Classical Topology NNReal
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (hb : CompactBound E)

theorem extendedEvaluation_operator
    (A : complexCore →ₗ[ℂ] complexCore)
    (T : PrincipalSeries negativeParameter →L[ℂ] PrincipalSeries negativeParameter)
    (hT : ∀v,smoothInclusion (A v)=T (smoothInclusion v))
    (hA : CompactBound (E.comp A)) (g : α) (v : PrincipalSeries negativeParameter) :
    extendedEvaluation (E.comp A) hA g v = extendedEvaluation E hb g (T v) := by
  refine smoothInclusion_denseRange.induction_on v ?_ ?_
  · exact isClosed_eq (extendedEvaluation (E.comp A) hA g).continuous
      ((extendedEvaluation E hb g).continuous.comp T.continuous)
  · intro u
    rw [extendedEvaluation_core,← hT,extendedEvaluation_core]
    rfl

include hb in
theorem compactBound_operator (A : complexCore →ₗ[ℂ] complexCore) (hA : Continuous A) :
    CompactBound (E.comp A) := by
  intro K hK
  obtain ⟨orders,B,h⟩ := hb K hK
  let Q : Seminorm ℂ complexCore := (orders.sup coreSeminorm).comp A
  have hQ : Continuous Q :=
    (Seminorm.continuous_finsetSup (fun i _=>core_withSeminorms.continuous_seminorm i)).comp hA
  obtain ⟨orders₁,B₁,_,hb₁⟩ := Seminorm.bound_of_continuous core_withSeminorms Q hQ
  refine ⟨orders₁,B*B₁,?_⟩
  intro v g hg
  calc
    ‖(E.comp A) v g‖ ≤ B*(orders.sup coreSeminorm) (A v) := h (A v) g hg
    _ ≤ B*(B₁*(orders₁.sup coreSeminorm) v) := mul_le_mul_of_nonneg_left (hb₁ v) B.coe_nonneg
    _ = (B*B₁ : ℝ≥0)*(orders₁.sup coreSeminorm) v := by simp only [NNReal.coe_mul];ring
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
