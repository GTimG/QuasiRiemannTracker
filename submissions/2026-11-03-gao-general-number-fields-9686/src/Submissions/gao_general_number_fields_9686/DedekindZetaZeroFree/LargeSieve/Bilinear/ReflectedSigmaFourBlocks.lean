/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Bilinear/ReflectedSigmaFourBlocks.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.ReflectedCoprimeTruncation
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.LargeSieve.Bilinear.SigmaFourDyadicExpansion

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff BigOperators

namespace DedekindZetaZeroFree.LargeSieve.ReflectedSigma4

variable {F : Type} [Field F] [NumberField F]

def unitRows (c m : Ideal (𝓞 F)) (K : ℝ) : Finset (Ideal (𝓞 F)) :=
  ({⊤} : Finset (Ideal (𝓞 F))).filter
    (fun a => Squarefree a ∧ a ⊔ m = ⊤ ∧ Bilinear.sc c a ≤ K)

end DedekindZetaZeroFree.LargeSieve.ReflectedSigma4

end
