/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/ComplexCoordinateBoxes.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.CorrectionFactors.Contour

theorem isOpen_box (a b c : ℝ) :
    IsOpen {x : ℂ × ℂ × ℂ | a < x.1.re ∧ b < x.2.1.re ∧ c < x.2.2.re} := by
  exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
    ((isOpen_lt continuous_const (Complex.continuous_re.comp
      (continuous_fst.comp continuous_snd))).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp
      (continuous_snd.comp continuous_snd))))

end DedekindZetaZeroFree.CorrectionFactors.Contour
