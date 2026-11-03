/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/HarishChandra/ScalarWordTranslations.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandra.ScalarWordSpan
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteTranslationLieCommutation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
local notation "W" => KPContActualSphericalRightFieldIdentification.actualRightWord
  F R.A.zeta12 R.A.primitive_zeta12
local notation "A" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12

theorem hcHeckeSpan_right (T : Realization R Q) {f : Functions R}
    (hf : f ∈ hcHeckeSpan T) (a : Group R) : A a f ∈ hcHeckeSpan T := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, b, w, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨v, a * b, w, ?_⟩
    funext g
    simp [KPLiteralRaw.rightAction, mul_assoc]
  | zero => simpa only [map_zero] using (hcHeckeSpan T).zero_mem
  | add f g hf hg ihf ihg =>
    simpa only [map_add] using (hcHeckeSpan T).add_mem ihf ihg
  | smul c f hf ihf => simpa only [map_smul] using (hcHeckeSpan T).smul_mem c ihf

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
