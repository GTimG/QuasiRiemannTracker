/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Evaluation/DiagonalDerivative.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.Orbits.CompactCurveDerivatives
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Evaluation.OperatorExtension

@[expose] public section

noncomputable section
open scoped Classical Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
variable {α : Type*} [TopologicalSpace α]
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (he : ∀v,Continuous (E v)) (hb : CompactBound E)

include he in
theorem diagonal_derivative (γ : ℝ → α) (hγ : Continuous γ)
    (v : ℝ → PrincipalSeries negativeParameter) (D : PrincipalSeries negativeParameter)
    (hv : Tendsto (fun t : ℝ=>(t:ℂ)⁻¹ • (v t-v 0)) (𝓝[≠] 0) (𝓝 D))
    (d : ℂ) (hd : HasDerivAt (fun t=>extendedEvaluation E hb (γ t) (v 0)) d 0) :
    HasDerivAt (fun t=>extendedEvaluation E hb (γ t) (v t))
      (extendedEvaluation E hb (γ 0) D+d) 0 := by
  let I := Set.Icc (-1 : ℝ) 1
  let K := Set.image γ I
  have hK : IsCompact K := isCompact_Icc.image hγ
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let p : C(I,K) := ⟨fun r=>⟨γ r.val,⟨r.val,r.property,rfl⟩⟩,
    (hγ.comp continuous_subtype_val).subtype_mk _⟩
  let L := (ContinuousMap.compCLM ℂ ℂ p).comp (extendedCompact E he hb K hK)
  have hL (u : PrincipalSeries negativeParameter) (r : I) :
      L u r=extendedEvaluation E hb (γ r.val) u :=
    extendedCompact_eval E he hb K hK u (p r)
  have ht := L.continuous.tendsto D |>.comp hv
  have hf : HasDerivAt (fun t=>L (v t)) (L D) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    convert ht using 1
    funext t
    simp only [Function.comp_def,map_smul,map_sub,zero_add]
    ext r
    simp only [ContinuousMap.smul_apply,Complex.real_smul,Complex.ofReal_inv,smul_eq_mul]
  let c : ℝ → I := fun t=>⟨max (-1) (min 1 t),le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hc : Continuous c := (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
  have hc0 : (c 0).val=0 := by norm_num [c]
  have hce : ∀ᶠ t in 𝓝 (0:ℝ), (c t).val=t := by
    filter_upwards [Ioo_mem_nhds (show (-1:ℝ)<0 by norm_num) (show (0:ℝ)<1 by norm_num)] with t ht
    simp only [c,min_eq_right ht.2.le,max_eq_right ht.1.le]
  have hdf : HasDerivAt (fun t=>L (v 0) (c t)) d 0 := hd.congr_of_eventuallyEq (by
    filter_upwards [hce] with t ht
    rw [hL,ht])
  have H := moving_evaluation_derivative (fun t=>L (v t)) (L D) hf c hc.continuousAt d hdf
  rw [hL,hc0] at H
  exact H.congr_of_eventuallyEq (by
    filter_upwards [hce] with t ht
    rw [hL,ht])
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
