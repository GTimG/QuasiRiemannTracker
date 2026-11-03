/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Approximation/IntegralCompletionCRT.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Approximation.IntegralProductCRTDensity

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open NumberField IsDedekindDomain

abbrev finiteIntegralAdeles (F : Type*) [Field F] [NumberField F] :=
  (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F

def integralDiagonal (F : Type*) [Field F] [NumberField F] :
    𝓞 F →+* finiteIntegralAdeles F :=
  Pi.ringHom (fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F))

theorem integralCompletion_dense (F : Type*) [Field F] [NumberField F] :
    DenseRange (integralDiagonal F) := by
  exact denseRange_ringOfIntegers_integralDiagonal F

end
end DedekindZetaZeroFree
