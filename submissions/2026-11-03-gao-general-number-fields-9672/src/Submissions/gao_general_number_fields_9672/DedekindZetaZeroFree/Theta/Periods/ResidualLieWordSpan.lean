/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/ResidualLieWordSpan.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.IdelicDilation
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Archimedean.RightLieWords

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}
variable {Q : AdmissibleFlatSources R}

def regularResidualFunctions (R : PrincipalMellin.ActualRecipe S η) :
    Submodule ℂ (Functions R) where
  carrier := {f | Continuous f ∧
    (∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g) ∧
    ∀ ε g, f (KPAdelicCoverRestrictedProduct.pglCentralInjection
      F R.A.zeta12 R.A.primitive_zeta12 ε * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 ε : ℂ) * f g}
  zero_mem' := by exact ⟨continuous_const, by intros; rfl, by intros; simp⟩
  add_mem' := by
    rintro f h ⟨fc, fr, fo⟩ ⟨hc, hr, ho⟩
    exact ⟨fc.add hc, by intros; simp only [Pi.add_apply, fr, hr],
      by intros; simp only [Pi.add_apply, fo, ho, mul_add]⟩
  smul_mem' := by
    rintro c f ⟨fc, fr, fo⟩
    refine ⟨continuous_const.smul fc, ?_, ?_⟩
    · intros; simp only [Pi.smul_apply, fr]
    · intros; simp only [Pi.smul_apply, smul_eq_mul, fo]; ring

def hcHeckeSpan (T : Realization R Q) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ {f | ∃ (v : R.A.UnitQuotient) (a : Group R)
    (word : List (Fin (AdelicRightLieWords.groupDimension F))),
    f = KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 a
      (AdelicRightLieWords.actualRightWord
        F R.A.zeta12 R.A.primitive_zeta12 word (T.theta v))}

def sameResidueModule (T : Realization R Q) : Submodule ℂ (Functions R) :=
  hcHeckeSpan T ⊓ regularResidualFunctions R

end DedekindZetaZeroFree.MomentSources

end
