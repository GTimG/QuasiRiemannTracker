/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/CompactPicture/TensorSectionSamplingGeneration.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ProductCovariantSlices

@[expose] public section

noncomputable section
open scoped TensorProduct
open Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000
namespace DedekindZetaZeroFree.ScalarFiniteSamplingGeneration

section Functions
variable {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ i, Fintype (C i)]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

 def functionTensorEquiv :
    PiTensorProduct ℂ (fun i => C i → V i) ≃ₗ[ℂ]
      ((∀ i, C i) → PiTensorProduct ℂ V) :=
  (PiTensorProduct.congr (fun i =>
    (Finsupp.linearEquivFunOnFinite ℂ (V i) (C i)).symm)).trans
    (PiTensorProduct.ofFinsuppEquiv.trans
      (Finsupp.linearEquivFunOnFinite ℂ (PiTensorProduct ℂ V) (∀ i, C i)))

 theorem functionTensorEquiv_formula
    (x : PiTensorProduct ℂ (fun i => C i → V i)) (c : ∀ i, C i) :
    functionTensorEquiv x c =
      PiTensorProduct.map (fun i => LinearMap.proj (c i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul]
    change r • functionTensorEquiv (PiTensorProduct.tprod ℂ x) c = _
    simp only [functionTensorEquiv, LinearEquiv.trans_apply, PiTensorProduct.congr_tprod,
      PiTensorProduct.map_tprod, PiTensorProduct.ofFinsuppEquiv_apply,
      Finsupp.linearEquivFunOnFinite_apply, Finsupp.linearEquivFunOnFinite_symm_apply,
      LinearMap.proj_apply]
  | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hx hy

end Functions

end DedekindZetaZeroFree.ScalarFiniteSamplingGeneration

end
