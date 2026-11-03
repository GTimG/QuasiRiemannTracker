/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Cubic/Wild/ResidualScalarSubmodules.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

noncomputable section

open scoped NumberField

namespace DedekindZetaZeroFree.KPWildActualResidual

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

instance kernelImageAdd (U : Submodule ℂ (KPGlobalTorusFunctionData.G F ζ hζ → ℂ)) :
    AddCommGroup U := Submodule.addCommGroup U

end DedekindZetaZeroFree.KPWildActualResidual

end
