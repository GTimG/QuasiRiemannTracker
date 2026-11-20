/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Mellin/OriginRegularization.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Mellin.PositiveLineInversion

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinH (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℂ s * originMellinQ h s

end DedekindZetaZeroFree.LargeSieve.Vendor

end
