/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Sections/Iwasawa/BorelSplitting.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem borel_lift_splitting (b : KPGlobalTorusFunctionData.borel F ζ hζ) :
    ∃ (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F),
      b.val = t.val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  exact KPGlobalTorusBorelNormTwistTransport.actual_borel_factorization F ζ hζ b

end DedekindZetaZeroFree.PrincipalOfKP

end
