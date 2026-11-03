/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Jacquet/Wild/PlaceReindexing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.Wild.InjectiveTensorInsertion
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Jacquet.Wild.CharacterTensorFibers

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentReindex
open MomentSources KPKirillovFiniteTensor KPKirillovGenuineSectionCharts WildCurrentTensor
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option quotPrecheck false
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

def places (W : Finset (KPFinitePlace F)) : Finset (KPHilbert.Place F) := W.image Sum.inr

def placeEquiv (W : Finset (KPFinitePlace F)) : W ≃ places W where
  toFun q := ⟨Sum.inr q.val,Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩⟩
  invFun p := ⟨Classical.choose (Finset.mem_image.mp p.property),
    (Classical.choose_spec (Finset.mem_image.mp p.property)).1⟩
  left_inv q := by
    apply Subtype.ext
    exact Sum.inr_injective (Classical.choose_spec
      (Finset.mem_image.mp (show Sum.inr q.val ∈ places W from
        Finset.mem_image.mpr ⟨q.val,q.property,rfl⟩))).2
  right_inv p := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp p.property)).2

def reindex (D : TensorActions R N) (W : Finset (KPFinitePlace F)) :
    AmbientTensor F W (fiber D W) ≃ₗ[ℂ]
      RestrictedTensorSimple.Stage (actualLocal R D.finiteData) (places W) :=
  (PiTensorProduct.reindex ℂ (fun p : places W => actualLocal R D.finiteData p)
    (placeEquiv W).symm).symm

theorem reindex_inverse_pure (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (z : ∀ p : places W, actualLocal R D.finiteData p) :
    (reindex D W).symm (PiTensorProduct.tprod ℂ z) =
      PiTensorProduct.tprod ℂ (fun q : W => z (placeEquiv W q)) := by
  exact PiTensorProduct.reindex_tprod ((placeEquiv W).symm) z

theorem reindex_pure_of (D : TensorActions R N) (W : Finset (KPFinitePlace F))
    (y : ∀ v : W, fiber D W v)
    (z : ∀ p : places W, actualLocal R D.finiteData p)
    (hz : ∀ q : W, z (placeEquiv W q) = y q) :
    reindex D W (PiTensorProduct.tprod ℂ y) = PiTensorProduct.tprod ℂ z := by
  apply (reindex D W).symm.injective
  rw [LinearEquiv.symm_apply_apply,reindex_inverse_pure]
  congr 1
  funext q
  exact (hz q).symm
end DedekindZetaZeroFree.FourierContinuation.WildCurrentReindex

end
