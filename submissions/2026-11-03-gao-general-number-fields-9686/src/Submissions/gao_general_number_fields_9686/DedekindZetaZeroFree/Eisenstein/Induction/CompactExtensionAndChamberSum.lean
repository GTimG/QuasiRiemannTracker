/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/CompactExtensionAndChamberSum.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralChamber
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def iwasawaTriple (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (g : G F ζ hζ) :
    KPGlobalTorusFunctionData.E F ζ hζ × KPAdeles F × K :=
  let t := Classical.choose (hK.2.1 g)
  let x := Classical.choose (Classical.choose_spec (hK.2.1 g))
  let k := Classical.choose (Classical.choose_spec
    (Classical.choose_spec (hK.2.1 g)))
  (t, x, k)

def compactExtension (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (v : Functions F ζ hζ)
    (s : ℂ) (g : G F ζ hζ) : ℂ :=
  let p := iwasawaTriple F ζ hζ K hK g
  KPGlobalExceptionalParameter.realLogPower
    (((KPGlobalTorusFunctionData.delta F ζ hζ p.1 : NNReal) : ℝ)) s *
    v (p.1.val * p.2.2.val)

end DedekindZetaZeroFree.KPLiteralChamber

end
