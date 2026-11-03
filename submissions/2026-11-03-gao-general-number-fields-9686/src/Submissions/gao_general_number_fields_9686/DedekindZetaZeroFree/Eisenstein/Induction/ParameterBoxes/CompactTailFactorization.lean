/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/ParameterBoxes/CompactTailFactorization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Approximation.CompactReferenceTails
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.Chambers.ParameterEvaluation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Induction.ExteriorFactors.CompactParameterIntegrals
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.Cofactors.HeightAndTailBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding
open NumberField MomentSources KPGlobalTorusFiniteStages FaithfulSource.RepairedInducing
open KPLocalPrincipalSeries KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open LiteralSource.CofactorChamber KPAdelicCoverRestrictedProduct KPLocalExceptionalConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem compact_split_tail (K : Set (FaithfulSource.RepairedInducing.Raw R)) (hK : IsCompact K)
    (E : Finset (KPFinitePlace F)) :
    ∃ Q : Finset (KPFinitePlace F), E ⊆ Q ∧ C.exceptional ⊆ Q ∧
      ∀ a ∈ K, ∀ q, q ∉ Q →
        KPPGLLocalCover.coverQuotient F ζ hζ (.inr q) (a (.inr q)) ∈
          (C.canonical q).iwasawa.compact.toOpenSubgroup := by
  obtain ⟨T,hT⟩ := LiteralSource.exists_uniform_compact_tail R.A K hK
  let Q := E ∪ C.exceptional ∪ T ∪ (bad_finite F).toFinset
  refine ⟨Q, ?_, ?_, ?_⟩
  · exact Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  · exact Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  · intro a ha q hq
    have hqC : q ∉ C.exceptional := by intro h; exact hq (by simp [Q,h])
    have hqT : q ∉ T := by intro h; exact hq (by simp [Q,h])
    have hqB : ¬ Bad F q := by intro h; exact hq (by simp [Q,h])
    have hk := hT a ha q hqT
    simp only [finiteCompact, dite_eq_right hqB, MonoidHom.mem_range] at hk
    obtain ⟨k,hk⟩ := hk
    obtain ⟨ht,hc⟩ := C.actual_compact q hqC
    change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
    rw [hc]
    refine ⟨k, ?_⟩
    rw [← hk]
    rfl

end DedekindZetaZeroFree.FourierContinuation.CurrentRepairedLocalBinding

end
