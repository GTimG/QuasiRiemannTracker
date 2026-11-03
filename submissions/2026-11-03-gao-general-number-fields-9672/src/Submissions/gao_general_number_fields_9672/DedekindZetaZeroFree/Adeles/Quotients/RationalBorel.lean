/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/RationalBorel.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.AdelicChamberContinuationData

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalBorel : Subgroup (KPRationalAdelicSplitting.RationalPGL2 F) :=
  (KPGlobalTorusFunctionData.borel F ζ hζ).comap
    (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ)

abbrev RationalQuotient := Quotient (QuotientGroup.rightRel (rationalBorel F ζ hζ))

end DedekindZetaZeroFree.KPGlobalResidualKernel

end
