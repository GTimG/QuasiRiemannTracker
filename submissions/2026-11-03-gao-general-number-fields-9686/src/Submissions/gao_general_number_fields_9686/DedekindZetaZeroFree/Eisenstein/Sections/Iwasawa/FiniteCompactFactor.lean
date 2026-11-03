/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Sections/Iwasawa/FiniteCompactFactor.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance instCubicRawTopFinite (v : KPHilbert.Place F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
  KPAdelicCoverRestrictedProduct.localTopology F ζ hζ v

theorem localCompactFactor_compact_finite (q : HeightOneSpectrum (𝓞 F)) :
    IsCompact (localCompactFactor F ζ hζ (Sum.inr q) :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))) := by
  simpa [localCompactFactor] using
    (KPAdelicCoverRestrictedProduct.finiteCompact_compact_open F ζ hζ q).1

end DedekindZetaZeroFree.PrincipalOfKP

end
