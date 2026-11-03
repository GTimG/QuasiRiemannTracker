/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Intertwining/TorusCovariance/AdelicDilationJacobian.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem adelic_integral_mul_idele_inv (μ : Measure (KPGlobalTorusFunctionData.Adeles F)) [μ.IsAddHaarMeasure]
    (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) (k : KPGlobalTorusFunctionData.Adeles F → ℂ) :
    (∫ x, k (x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F)) ∂μ) =
      ((addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ) : ℂ) * ∫ x, k x ∂μ := by
  let T := ContinuousAddEquiv.mulLeft a
  let m := addEquivAddHaarChar T
  have hm := addEquivAddHaarChar_smul_map μ T.symm
  rw [addEquivAddHaarChar_symm] at hm
  have hmap : μ.map T.symm = m • μ := by
    have hh := congrArg (fun ν : Measure (KPGlobalTorusFunctionData.Adeles F) => m • ν) hm
    simpa [m, smul_smul, mul_inv_cancel₀ (addEquivAddHaarChar_pos T).ne'] using hh
  have he : ⇑T.symm.toMeasurableEquiv = fun x : KPGlobalTorusFunctionData.Adeles F =>
      x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F) := by
    ext x
    apply T.injective
    change T (T.symm x) = (↑a : KPGlobalTorusFunctionData.Adeles F) * (x * ↑a⁻¹)
    rw [T.apply_symm_apply, mul_left_comm, Units.mul_inv, mul_one]
  have hh := integral_map_equiv (μ := μ) T.symm.toMeasurableEquiv k
  rw [he] at hh
  have heT : ⇑T.symm = fun x : KPGlobalTorusFunctionData.Adeles F => x * ↑a⁻¹ := he
  rw [heT] at hmap
  rw [← hh, hmap, integral_smul_nnreal_measure]
  rfl

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end
