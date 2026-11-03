/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/CompactKernelOrbitData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.WildPartialPeriodFactorization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.RankOne.ArchimedeanBigCellBasePoint
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.ResidualCoreAndUnitRotations
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open scoped NumberField TensorProduct Classical
open NumberField IsDedekindDomain MeasureTheory
namespace DedekindZetaZeroFree.KPWildActualCompactKernel
open KPLocalExceptionalConstruction
  KPWildPartialPeriodFactorization KPGlobalResidualConstruction

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance rawImageAdd (U : Submodule ℂ (KPGlobalTorusFunctionData.G F ζ hζ → ℂ)) :
    AddCommGroup U := Submodule.addCommGroup U

end DedekindZetaZeroFree.KPWildActualCompactKernel

end
