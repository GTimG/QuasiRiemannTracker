/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/Residual/ReflectedFinitePurity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWordDerivatives
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Residual.ReflectedNegativeSections

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices
open MomentSources KPGlobalTorusFiniteStages FaithfulSource FaithfulSource.RepairedInducing
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar KPGlobalResidualConstruction KPLiteralChamber
open KPLiteralScalarArchUniformBands KPAdelicCoverRestrictedProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
variable (s : RestrictedTensorSimple.Level (bad R P C))
variable (hs : ∀ w : InfinitePlace F, Sum.inl w ∈ s.val)
variable (r : Raw R) (hr : ∀ w : InfinitePlace F, r (.inl w) = 1)

include hs hr
theorem reflected_finite_pure
    (x : RestrictedTensorSimple.Stage (fun j => actualLocal R (imageData R N P C) j) s.val) :
    ∃ n : ℕ, ∃ d : Fin n → ℂ, ∃ f : Fin n → InfinitePlace F → PrincipalSeries negativeParameter,
      ∀ a : InfinitePlace F → ComplexGL2,
      (reflectedStage R N P C s (r * sectionTuple F ζ hζ a) x).val.val 1 =
        ∑j, d j * ∏w, f j w (a w) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    refine ⟨1,fun _ => c * CurrentMinusSlot.finiteScalar R N P C s x r,
      fun _ w => (x ⟨.inl w,hs w⟩).val,?_⟩
    intro a
    simp only [map_smul,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,
      reflected_section_pure R N P C s hs r hr,Fin.sum_univ_one]
    ring
  | add x y hx hy =>
    obtain ⟨n,d,f,hf⟩ := hx
    obtain ⟨m,e,g,hg⟩ := hy
    refine ⟨n+m,Fin.addCases d e,Fin.addCases f g,?_⟩
    intro a
    simp only [map_add,Submodule.coe_add,Pi.add_apply,hf,hg,Fin.sum_univ_add,
      Fin.addCases_left,Fin.addCases_right]
end DedekindZetaZeroFree.FourierContinuation.ResidualPrincipalSlices

end
