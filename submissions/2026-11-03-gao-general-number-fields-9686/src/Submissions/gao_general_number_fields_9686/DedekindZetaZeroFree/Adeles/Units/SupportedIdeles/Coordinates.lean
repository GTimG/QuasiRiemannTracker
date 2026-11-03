/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Units/SupportedIdeles/Coordinates.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Adeles.Units.SupportedIdeles.Topology

@[expose] public section

open scoped NumberField NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SupportedChartDefinitions

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

def H : Subgroup (IdeleGroup.normOneSubgroup (K := F)) :=
  (IdeleGroup.supportedAt (K := F) (A.Sf : Set (HeightOneSpectrum (𝓞 F)))).subgroupOf
    (IdeleGroup.normOneSubgroup (K := F))

abbrev C :=
  (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ A.Sf}) →
    (v.val.adicCompletionIntegers F).units

def sCoordinatesRaw (a : IdeleGroup F) : A.G :=
  (fun w => ContinuousMulEquiv.piUnits a.1 w,
   fun v => a.2 v.val)

def exteriorCoordinates (a : (SupportedChartDefinitions.H A)) : (SupportedChartDefinitions.C A) :=
  fun v => ⟨a.1.1.2 v.val,
    (IdeleGroup.mem_supportedAt_iff
      (A.Sf : Set (HeightOneSpectrum (𝓞 F))) a.1.1).mp a.2 v.val v.prop⟩

end
end SupportedChartDefinitions
end DedekindZetaZeroFree
