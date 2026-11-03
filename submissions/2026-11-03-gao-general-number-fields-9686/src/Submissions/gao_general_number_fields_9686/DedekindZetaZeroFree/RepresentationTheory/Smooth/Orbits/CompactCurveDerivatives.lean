/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/Orbits/CompactCurveDerivatives.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section
open scoped Classical Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
set_option backward.isDefEq.respectTransparency false
variable {β : Type*} [TopologicalSpace β] [CompactSpace β]

theorem moving_evaluation_derivative [LocallyCompactSpace β]
    (f : ℝ → C(β,ℂ)) (D : C(β,ℂ)) (hf : HasDerivAt f D 0)
    (γ : ℝ → β) (hγ : ContinuousAt γ 0) (d : ℂ)
    (hd : HasDerivAt (fun t=>f 0 (γ t)) d 0) :
    HasDerivAt (fun t=>f t (γ t)) (D (γ 0)+d) 0 := by
  have ht := hf.tendsto_slope_zero
  have hp := ht.prodMk (hγ.tendsto.mono_left nhdsWithin_le_nhds)
  rw [← nhds_prod_eq] at hp
  have he := (show Continuous (fun p : C(β,ℂ) × β => p.1 p.2) from continuous_eval).continuousAt.tendsto.comp
    hp
  have hs := he.add hd.tendsto_slope_zero
  rw [hasDerivAt_iff_tendsto_slope_zero]
  convert hs using 1
  funext t
  simp only [Function.comp_def,zero_add,ContinuousMap.smul_apply,ContinuousMap.sub_apply]
  simp only [Complex.real_smul]
  ring
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
