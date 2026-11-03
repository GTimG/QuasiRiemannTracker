/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/FiniteGammaNormalization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Metaplectic.Weil.GlobalPhaseExtension

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SArithmeticData.GaussCorrection
noncomputable section
set_option autoImplicit false
variable {F : Type} [Field F] [NumberField F]

theorem finiteQuadraticStabilizes_free (A : SArithmeticData F) :
    ∀ (v : {v // v ∈ A.Sf}) (a : (v.val.adicCompletion F)ˣ),
      A.FiniteQuadraticStabilizes v.val a :=
  fun v a => A.finiteQuadratic_stabilizes v.val a

theorem finiteGamma_one_ne_zero_free (A : SArithmeticData F) :
    ∀ v : {v // v ∈ A.Sf}, A.finiteGamma v.val 1 ≠ 0 := by
  intro v h
  have hv := A.norm_finiteGamma v.val 1
  rw [h, norm_zero] at hv
  norm_num at hv

end
end DedekindZetaZeroFree.SArithmeticData.GaussCorrection
