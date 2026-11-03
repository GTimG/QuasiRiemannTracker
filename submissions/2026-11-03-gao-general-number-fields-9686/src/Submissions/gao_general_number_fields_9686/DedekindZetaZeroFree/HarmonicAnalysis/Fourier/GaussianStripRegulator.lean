/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Fourier/GaussianStripRegulator.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Analysis.MellinVerticalIntegral

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

def gaussianRegulator (f : ℂ → ℂ) (ε : ℝ) (s : ℂ) : ℂ :=
  f s * Complex.exp ((ε : ℂ) * s ^ 2)

end DedekindZetaZeroFree.LargeSieve.Vendor.Subquadratic

end
