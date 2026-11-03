/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Comparison/TripleMellinKernel.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.VerticalContourShift

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section

def comparisonA : ℝ := 9 / 10

def comparisonB : ℝ := 133 / 1000

def comparisonH₀ : ℝ := 1 / 10

def comparisonX (Z : ℝ) : ℝ := Z ^ comparisonA

def comparisonY (Z : ℝ) : ℝ := Z ^ comparisonB

def comparisonDelta : ℝ := 1 / 10000000

def comparisonSigma₁ : ℝ := 1 + comparisonDelta

def comparisonZeta₁ : ℝ := 1 / 6 + comparisonDelta

def comparisonR₀ : ℝ := 350000

def comparisonE (x w z : ℝ) : ℝ :=
  comparisonA / 2 + x - 1 + comparisonH₀ * z + comparisonB * (w - 1)

def comparisonC (s : ℂ) : ℂ := s - 8 / 15

def comparisonRealPower (Z : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log Z : ℂ))

def comparisonTripleVerticalIntegral (σξ σw σz : ℝ)
    (κ : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
    ∫ t : ℝ × ℝ × ℝ,
      κ ((σξ : ℂ) + (t.1 : ℂ) * Complex.I)
        ((σw : ℂ) + (t.2.1 : ℂ) * Complex.I)
        ((σz : ℂ) + (t.2.2 : ℂ) * Complex.I)

end
end DedekindZetaZeroFree
