/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/RootSubgroupEmbedding.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactTranslationBounds
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.ArchimedeanRootCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open ThetaExpansion MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

open KPCplxCharacterHaar KPSmoothActualFlowData
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCLocalCovariance
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion

def actualMatrixSlot (w : InfinitePlace F) (a : ComplexGL2) : KPLiteralRaw.G F ζ hζ :=
  archimedeanInsertion F ζ hζ (fun u=>Matrix.ProjGenLinGroup.mk (Function.update (1 : InfinitePlace F → ComplexGL2) w a u))

def actualRootAdele (w : InfinitePlace F) (z : ℂ) : KPAdeles F :=
  archRootAdele F ζ hζ (Pi.single w z)

theorem actualMatrixSlot_root (w : InfinitePlace F) (z : ℂ) :
    actualMatrixSlot R w (upperUnipotent z)=
      KPGlobalTorusFunctionData.N F ζ hζ (actualRootAdele R w z) := by
  have he : Function.update (1 : InfinitePlace F → ComplexGL2) w (upperUnipotent z)=
      fun u=>upperUnipotent ((Pi.single w z : InfinitePlace F → ℂ) u) := by
    funext u
    by_cases h:u=w
    · subst u;simp
    · simp [h,Ne.symm h,upperUnipotent]
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
  unfold actualMatrixSlot
  rw [he,←sectionTuple_insertion]
  exact archMatrixInsertion_upper F ζ hζ (Pi.single w z)

theorem actualRootAdele_character (w : InfinitePlace F) (z : ℂ) :
    adelicTraceQuotientCharacter F (QuotientAddGroup.mk (actualRootAdele R w z))=
      traceCharacter z := by
  have he : actualRootAdele R w z =
      ((Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).symm z)),0) := by
    apply Prod.ext
    · funext u
      by_cases h:u=w
      · subst u;simp [actualRootAdele,archRootAdele]
      · simp [actualRootAdele,archRootAdele,h,Ne.symm h]
    · rfl
  change adelicTraceCharacter F (actualRootAdele R w z)=_
  rw [he,adelicTraceCharacter_arch_single,archTraceCharacter_of_isComplex w
    (KPHilbert.infinite_isComplex F ζ hζ w)]
  simp only [RingEquiv.apply_symm_apply]
  change Circle.exp (2*Real.pi*(2*z.re))=Circle.exp (((traceFrequency:ℂ)*z).re)
  apply congrArg Circle.exp
  simp [traceFrequency,Complex.mul_re]
  ring
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
