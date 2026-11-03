/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/FirstRootFlatPreimageGerms.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.FirstRootNondegeneracy
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.FirstRootFlatPreimages
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.ProjectedRealization

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem first_root_flat_preimages_exists
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B) :
    ∃ Q : AdmissibleFlatSources R, Q.dq = J.base.sources.dq ∧
      Nontrivial (KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K) ∧
      ∀ v, ∃ C : RootDerivatives.FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v),
        C.numerator 0 = firstRootDerivatives R J.cutoffs (J.base.realization.theta v) ∧
        (Q.flat v).val 0 ≠ 0 ∧ C.numerator 0 ≠ 0 ∧
        fourier R J.base.sources.dq (C.numerator 0) 1 ≠ 0 := by
  obtain ⟨Q, hdq, hC⟩ := RootDerivatives.firstRoot_sources R J.base.sources J.base.realization J.cutoffs
  have hn := first_root_derivatives_nondegenerate R N A B J
  have hnonzero (v : R.A.UnitQuotient)
      (C : RootDerivatives.FlatScalarResidue F R.A.zeta12 R.A.primitive_zeta12 (Q.flat v))
      (hpin : C.numerator 0 = firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) :
      C.numerator 0 ≠ 0 := by
    rw [hpin]
    exact hn.2.1 v
  have hnt : Nontrivial (KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K) := by
    obtain ⟨C, hpin⟩ := hC (1 : R.A.UnitQuotient)
    exact RootDerivatives.flat_nontrivial_of_residue Q.iwasawa C (hnonzero _ C hpin)
  refine ⟨Q, hdq, hnt, ?_⟩
  intro v
  obtain ⟨C, hpin⟩ := hC v
  have hCne := hnonzero v C hpin
  refine ⟨C, hpin, C.zero_section_ne_zero Q.iwasawa hCne, hCne, ?_⟩
  rw [hpin]
  exact hn.1 v

theorem first_root_realization_exists
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R)
    (J : FirstRootProjected R N A B) :
    ∃ (Q : AdmissibleFlatSources R) (T : Realization R Q),
      Q.dq = J.base.sources.dq ∧
      (∀ v, T.theta v = firstRootDerivatives R J.cutoffs (J.base.realization.theta v)) ∧
      (∀ v, (Q.flat v).val 0 ≠ 0) ∧ (∀ v, T.theta v ≠ 0) ∧
      (∀ v, fourier R Q.dq (T.theta v) 1 ≠ 0) ∧
      Nontrivial (KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K) := by
  obtain ⟨Q, hdq, hnt, hC⟩ := first_root_flat_preimages_exists  R hR N A B J
  let P : JointRootAlignedSources R N := ⟨hR, N, rfl, Q⟩
  obtain ⟨C₀, ⟨H⟩⟩ := selected_scalar_source_exists  R P
  have hg := fun v => selected_source_smooth_germ_of_scalar_germ  R P C₀ v (H v)
  choose G hG using hg
  let T : Realization R Q := EisensteinSmoothGerms.assemble C₀ G
  have hp (v) : T.theta v = firstRootDerivatives R J.cutoffs (J.base.realization.theta v) := by
    obtain ⟨C, hpin, _, _, _⟩ := hC v
    exact (funext (fun g => RootDerivatives.FlatScalarResidue.value_unique
      (RootDerivatives.realizationScalarResidue T v) C g)).trans hpin
  have hn := first_root_derivatives_nondegenerate R N A B J
  exact ⟨Q, T, hdq, hp, fun v => (hC v).choose_spec.2.1,
    fun v => by rw [hp]; exact hn.2.1 v,
    fun v => by rw [hdq, hp]; exact hn.1 v, hnt⟩

end DedekindZetaZeroFree.ThetaExpansion

end
