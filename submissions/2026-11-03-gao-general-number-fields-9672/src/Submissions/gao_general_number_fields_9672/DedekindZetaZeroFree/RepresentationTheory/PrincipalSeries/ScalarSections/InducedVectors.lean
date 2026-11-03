/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/ScalarSections/InducedVectors.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.BorelRationalFibers

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPActualReflectionData.ScalarFiberInverse renaming fiber_covariance → fiber_covariance
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false

def inducedVector (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f) :
    KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ
      (KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ) :=
  ⟨inducedRationalFiber A f hf, by
    intro t x g
    apply Subtype.ext
    apply Subtype.ext
    funext u
    exact fiber_covariance F ζ hζ (inducedBorel A f hf) t x g u⟩

@[simp] theorem inducedVector_apply (f : Functions F ζ hζ) (hf : Induced F ζ hζ 0 f)
    (g : G F ζ hζ) (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    ((inducedVector A f hf).val g).val.val t =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * f (t.val * g) := rfl

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
