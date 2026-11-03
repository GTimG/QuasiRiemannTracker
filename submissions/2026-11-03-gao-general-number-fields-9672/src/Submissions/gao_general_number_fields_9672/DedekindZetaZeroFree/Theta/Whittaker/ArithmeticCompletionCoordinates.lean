/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/ArithmeticCompletionCoordinates.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaActualArithmeticBinding
open NumberField IsDedekindDomain
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

def actualPlace {F : Type} [Field F] [NumberField F] : KPPlace F → KPHilbert.Place F
  | Sum.inl p => Sum.inr p
  | Sum.inr v => Sum.inl v

def completionEquiv {F : Type} [Field F] [NumberField F] (v : KPPlace F) :
    KPCompletion F v ≃+* KPHilbert.Completion F (actualPlace v) := by
  cases v <;> exact RingEquiv.refl _

end DedekindZetaZeroFree.ThetaActualArithmeticBinding

end
