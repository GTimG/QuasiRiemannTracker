/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/NormalizedLocalNormProduct.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.LocalAbsoluteValueFiniteSupport
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.TotallyComplexIdeleNorm

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
noncomputable section
set_option autoImplicit false

def localAbsUnit (F : Type) [Field F] [NumberField F]
    (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) : (ℝ≥0)ˣ :=
  Units.mk0 (KPGlobalCenterRationalCharacterExtension.localAbs F v y)
    (ne_of_gt (KPGlobalCenterRationalCharacterExtension.localAbs_pos F v y))

theorem idele_abs_finite_product (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (u : KPGlobalTorusFunctionData.Ideles F) :
    Function.HasFiniteMulSupport (fun v =>
      localAbsUnit F v (KPGlobalCubicIdelePairing.ideleEval F v u)) ∧
    (∏ᶠ v, localAbsUnit F v (KPGlobalCubicIdelePairing.ideleEval F v u)) =
      KPGlobalTorusFunctionData.ideleAbs F u := by
  letI : NumberField.IsTotallyComplex F :=
    NumberField.nrRealPlaces_eq_zero_iff.mp hF
  refine ⟨?_, ?_⟩
  · exact KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.idele_localAbs_hasFiniteMulSupport F u
  · exact KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct.idele_localAbs_finprod F u

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
