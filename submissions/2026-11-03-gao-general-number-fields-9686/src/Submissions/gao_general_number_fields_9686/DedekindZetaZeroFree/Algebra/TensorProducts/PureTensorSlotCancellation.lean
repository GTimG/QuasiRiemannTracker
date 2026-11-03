/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/TensorProducts/PureTensorSlotCancellation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.RestrictedTensorProductFunctional

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation
universe u v
variable {J : Type u} [Fintype J] [DecidableEq J] {V : J → Type v}
variable [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem pure_tensor_ne_zero (x : ∀ j, V j) (hx : ∀ j, x j ≠ 0) :
    PiTensorProduct.tprod ℂ x ≠ 0 := by
  let ell : ∀ j, Module.Dual ℂ (V j) := fun j =>
    Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hx j))
  have hell : ∀ j, ell j (x j) = 1 := fun j =>
    Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hx j))
  let f : Module.Dual ℂ (PiTensorProduct ℂ V) :=
    PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ ell)
  have hfx : f (PiTensorProduct.tprod ℂ x) = 1 := by
    simp [f, PiTensorProduct.dualDistrib_apply, hell]
  intro hz
  rw [hz, map_zero] at hfx
  exact zero_ne_one hfx

theorem pure_tensor_coordinates_ne_zero (x : ∀ j, V j)
    (hx : PiTensorProduct.tprod ℂ x ≠ 0) (i : J) : x i ≠ 0 := by
  intro hz
  have he : (PiTensorProduct.tprod ℂ).toLinearMap x i (x i) =
      PiTensorProduct.tprod ℂ x := by
    simp only [MultilinearMap.toLinearMap_apply, Function.update_eq_self]
  rw [hz, map_zero] at he
  exact hx he.symm

theorem pure_tensor_slot_injective (x : ∀ j, V j) (i : J)
    (hx : ∀ j, j ≠ i → x j ≠ 0) :
    Function.Injective ((PiTensorProduct.tprod ℂ).toLinearMap x i) := by
  intro a b hab
  apply sub_eq_zero.mp
  by_contra hzne
  have hz : (PiTensorProduct.tprod ℂ).toLinearMap x i (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  apply pure_tensor_ne_zero (Function.update x i (a - b)) _ hz
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hzne
  · simpa only [Function.update_of_ne hj] using hx j hj

theorem pure_tensor_update_cancel (x : ∀ j, V j)
    (hx : PiTensorProduct.tprod ℂ x ≠ 0) (i : J) (z : V i)
    (he : PiTensorProduct.tprod ℂ (Function.update x i z) = PiTensorProduct.tprod ℂ x) :
    z = x i := by
  apply pure_tensor_slot_injective x i (fun j _ => pure_tensor_coordinates_ne_zero x hx j)
  simpa only [MultilinearMap.toLinearMap_apply, Function.update_eq_self] using he

end DedekindZetaZeroFree.FourierContinuation

end
