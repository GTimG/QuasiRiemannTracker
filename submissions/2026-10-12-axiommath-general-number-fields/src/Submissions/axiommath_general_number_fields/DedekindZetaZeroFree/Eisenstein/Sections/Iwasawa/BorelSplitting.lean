/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Sections/Iwasawa/BorelSplitting.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Induction.IwasawaNormTransport

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
