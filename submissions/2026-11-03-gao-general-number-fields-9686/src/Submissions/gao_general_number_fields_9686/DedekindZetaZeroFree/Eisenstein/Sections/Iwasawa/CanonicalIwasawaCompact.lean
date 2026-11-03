/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Sections/Iwasawa/CanonicalIwasawaCompact.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactDecomposition
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.MaximalCompactness

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem iwasawaCompactSubgroupMax_isIwasawa :
    KPLiteralRaw.IwasawaCompact F ζ hζ (iwasawaCompactSubgroupMax F ζ hζ) :=
  ⟨iwasawaCompactSubgroupMax_compact F ζ hζ,
    iwasawaCompactSubgroupMax_decomposition F ζ hζ,
    complexCompactLift_mem_iwasawaCompactSubgroupMax F ζ hζ⟩

end DedekindZetaZeroFree.PrincipalOfKP

end
