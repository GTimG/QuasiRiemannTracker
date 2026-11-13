/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/RestrictedTensors/ExceptionalSetEquivalence.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

noncomputable section
open scoped Classical TensorProduct
namespace DedekindZetaZeroFree.RestrictedTensorSimple
variable {J : Type} (V : J → Type) [∀j, AddCommGroup (V j)] [∀j, Module ℂ (V j)]
variable (e : ∀j, V j) (B D : Finset J) (h : B = D)
def equalBadEquiv : Core V e B ≃ₗ[ℂ] Core V e D := by
  subst D
  exact LinearEquiv.refl ℂ _

theorem equalBadEquiv_stage (s : Level B) (x : Stage V s.val) :
    equalBadEquiv V e B D h (stageInclusion V e B s x) =
      stageInclusion V e D ⟨s.val, h ▸ s.property⟩ x := by
  subst D
  rfl
end DedekindZetaZeroFree.RestrictedTensorSimple

end
