/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/HarishChandraHeckeDifferentialRecovery.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDerivativeCyclicSpan
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorDifferentialCyclicity

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources NumberField KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q Q' : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T) (T' : Realization R Q')

theorem tensor_compact_word_recovery (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (hm : _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T') :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
      (complexCoreCompactLinearMap k (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T' := by
  have he : _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
      (complexCoreCompactLinearMap k (x ⟨Sum.inl w,hw⟩))) =
      KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
        (complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)
        (_root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x) := funext (D.complex_intertwining w k s hw x)
  rw [he]
  exact wordRecovery_translate R T' _ hm

theorem selected_at_frozen_stage (s : RestrictedTensorSimple.Level D.bad)
    (hs : s.val = D.bad) (v : R.A.UnitQuotient) :
    ∃ x : ∀ p : s.val, actualLocal R D.finiteData p,
      tensorFunction R D s x = T.theta v := by
  obtain ⟨t,x,ht,hx⟩ := D.selected_frozen_stage v
  have hts : t = s := Subtype.ext (ht.trans hs.symm)
  subst t
  exact ⟨x, (congrArg D.coreMap hx).symm.trans (D.selected_eq v)⟩

theorem frozen_hc_recovery_of_differential_stability
    (B : Fin 6 → Module.End ℂ complexCore)
    (hcyc : ∀ v : complexCore, v ≠ 0 →
      Submodule.span ℂ (Set.range (fun a : NativeComplexHCSource.algebra B => a.val v)) = ⊤)
    (hdiff : ∀ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ p : s.val, actualLocal R D.finiteData p)
      (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) i,
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ∈ wordRecovery R T' →
      _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w,hw⟩
        (B i (x ⟨Sum.inl w,hw⟩))) ∈ wordRecovery R T')
    (hfrozen : ∀ v : R.A.UnitQuotient, ∃ (s : RestrictedTensorSimple.Level D.bad)
      (y : ∀ p : s.val, actualLocal R D.finiteData p),
      s.val = D.bad ∧ tensorFunction R D s y = T'.theta v ∧ (∀ p, y p ≠ 0)) :
    hcHeckeSpan T ≤ hcHeckeSpan T' := by
  apply hcHeckeSpan_le_of_word_recovery R T T'
  intro v
  obtain ⟨s,y,hs,hy,hyn⟩ := hfrozen v
  obtain ⟨x,hx⟩ := selected_at_frozen_stage R D s hs v
  rw [← hx]
  apply tensor_stage_word_recovery R D T' B hcyc s
    (tensor_compact_word_recovery R D T' s) (hdiff s) y hyn
  change _root_.DedekindZetaZeroFree.RootDerivatives.tensorFunction R D s y ∈ wordRecovery R T'
  rw [hy]
  exact theta_mem_wordRecovery R T' v
end DedekindZetaZeroFree.RootDerivatives

end
