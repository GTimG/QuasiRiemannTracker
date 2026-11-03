/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Jacquet/FiniteEvaluationSeparation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexWeylIntegralBounds
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.IndependentSlicesAndUniformBands
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SpectralJacquet

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SheetRescaling
open MeasureTheory KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPCplxJacquetFunctional KPCplxActualImage
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open _root_.DedekindZetaZeroFree.KPLiteralScalarArchIndependentSlices renaming finite_interpolation → finite_interpolation

def jacquetRightAction (g : ComplexPGL2) :
    PrincipalSeries positiveParameter →L[ℂ] PrincipalSeries positiveParameter where
  toFun := KPCplxPrincipalSeriesCharts.pi positiveParameter g
  map_add' x y := by
    induction g using Quotient.inductionOn with | _ g =>
    apply Subtype.ext
    rfl
  map_smul' c x := by
    induction g using Quotient.inductionOn with | _ g =>
    apply Subtype.ext
    rfl
  cont := (pi_continuous positiveParameter).comp
    (continuous_const.prodMk continuous_id)

theorem jacquet_evaluations_separate (f : PrincipalSeries positiveParameter)
    (hf : ∀ g : ComplexGL2, jacquetIntegral standardComplexParameter
      (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f) = 0) : f = 0 := by
  let J := jacquetFunctional standardComplexParameter
  let U : Submodule ℂ (PrincipalSeries positiveParameter) :=
    ⨅ g : ComplexPGL2, (J.comp (jacquetRightAction g)).ker
  have hmem (x : PrincipalSeries positiveParameter) :
      x ∈ U ↔ ∀ g : ComplexPGL2, J (KPCplxPrincipalSeriesCharts.pi positiveParameter g x) = 0 := by
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
    rfl
  have hc : IsClosed (U : Set (PrincipalSeries positiveParameter)) := by
    letI := principalSeries_t2 positiveParameter
    have he : (U : Set (PrincipalSeries positiveParameter)) =
        ⋂ g : ComplexPGL2, ((J.comp (jacquetRightAction g)).ker :
          Set (PrincipalSeries positiveParameter)) := by
      ext x
      change (x ∈ U) ↔ _
      rw [hmem]
      simp only [Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
        ContinuousLinearMap.coe_comp', Function.comp_apply]
      rfl
    rw [he]
    exact isClosed_iInter (fun g => (J.comp (jacquetRightAction g)).isClosed_ker)
  have hi : IsGInvariant positiveParameter U := by
    intro g x hx
    apply (hmem _).mpr
    intro h
    rw [← pi_mul]
    exact (hmem _).mp hx (h * g)
  have hn : U ≠ ⊤ := by
    intro ht
    apply jacquetFunctional_ne_zero standardComplexParameter
    ext x
    have hx : x ∈ U := by rw [ht]; trivial
    simpa only [pi_one, ContinuousLinearMap.zero_apply] using (hmem _).mp hx 1
  have hu : U = ⊥ := (exceptional_principalSeries_irreducible.1.2 U hc hi).resolve_right hn
  have hx : f ∈ U := by
    apply (hmem _).mpr
    intro g
    induction g using Quotient.inductionOn with | _ g => exact hf g
  simpa only [hu, Submodule.mem_bot] using hx

def jacquetEvaluation : PrincipalSeries positiveParameter →ₗ[ℂ] (ComplexGL2 → ℂ) where
  toFun f g := jacquetIntegral standardComplexParameter
    (KPCplxPrincipalSeriesCharts.pi positiveParameter (Matrix.ProjGenLinGroup.mk g) f)
  map_add' f h := by
    funext g
    exact (jacquetFunctional standardComplexParameter |>.comp
      (jacquetRightAction (Matrix.ProjGenLinGroup.mk g))).map_add f h
  map_smul' c f := by
    funext g
    exact (jacquetFunctional standardComplexParameter |>.comp
      (jacquetRightAction (Matrix.ProjGenLinGroup.mk g))).map_smul c f

theorem jacquetEvaluation_injective : Function.Injective jacquetEvaluation := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change f = 0
  apply jacquet_evaluations_separate
  intro g
  exact congrFun hf g

end DedekindZetaZeroFree.SheetRescaling

end
