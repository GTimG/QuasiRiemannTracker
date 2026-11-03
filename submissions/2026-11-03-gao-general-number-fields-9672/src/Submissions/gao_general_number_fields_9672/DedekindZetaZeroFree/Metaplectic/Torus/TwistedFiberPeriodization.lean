/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Torus/TwistedFiberPeriodization.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.Borel.TwistedAveragingContinuity

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport
open KPGlobalTorusBorelTwistCompatibilityBorelInduction
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalRep (C : ModelData F ζ hζ) :
    KPGlobalTorusPeriodizationInverse.PeriodizationRepresentatives F ζ hζ C :=
  Classical.choose (KPGlobalTorusPeriodizationInverse.rational_representatives_exist F ζ hζ C)

theorem rationalRep_rational (C : ModelData F ζ hζ) :
    ∀ a, ∃ y : Fˣ, (rationalRep F ζ hζ C).lift a =
      KPGlobalTorusPeriodizationInverse.rationalLift F ζ hζ y :=
  Classical.choose_spec
    (KPGlobalTorusPeriodizationInverse.rational_representatives_exist F ζ hζ C)

def chartTerm (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (g : G F ζ hζ)
    (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    GroupArch F → ℂ :=
  fun z => (f.val (groupArchChart F ζ hζ z * g)).val.val ((rationalRep F ζ hζ C).lift a).val

end
end DedekindZetaZeroFree.TorusChartTransport
