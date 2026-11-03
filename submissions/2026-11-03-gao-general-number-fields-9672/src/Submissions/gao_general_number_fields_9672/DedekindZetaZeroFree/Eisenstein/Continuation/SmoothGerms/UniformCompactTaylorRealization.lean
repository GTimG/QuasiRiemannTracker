/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SmoothGerms/UniformCompactTaylorRealization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Continuation.CompactSmoothRealization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Continuation.SmoothGerms.CanonicalCauchyCoefficients
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.RealizationAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology ContDiff BigOperators
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q}

theorem scalar_family_realization_constructed (H : ∀ v, ScalarGerm C v) :
    ∃ T : Realization R Q, T.E = C.E ∧
      (∀ v, T.radius ≤ (H v).radius) ∧
      (∀ v s, T.cleared v s = ((H v).cleared s : Functions R)) ∧
      (∀ v n, T.coefficients v n = (H v).coefficients n) := by
  choose G hrad he hc using (fun v => scalarGerm_upgrade_canonical (H v))
  let T := EisensteinSmoothGerms.assemble C G
  have hb := (Classical.choose_spec (EisensteinSmoothGerms.common_radius G)).2.2
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · intro v
    exact (hb v).trans (hrad v)
  · intro v s
    exact congrFun (he v) s
  · intro v n
    exact congrFun (hc v) n

end DedekindZetaZeroFree.SharedSource

end
