/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/ReflectedSquareResidueData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LFunctions.Dedekind.PrincipalHeckeData
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.InverseMellinRepresentation

@[expose] public section

noncomputable section
open scoped NumberField Classical ContDiff Topology
open Filter
namespace DedekindZetaZeroFree.LargeSieve.SquarePoisson

def weight (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  fieldTransform D r h (x ^ 2)

def spectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  B D r h (s / 2) / 2

def reflectedSpectrum (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  (D : ℂ) ^ (s - 1 / 2) * Complex.Gammaℂ s ^ r *
    (Complex.Gammaℂ (1 - s))⁻¹ ^ r * spectrum D r h (1 - s)

def reflectedTransform (D : ℝ) (r : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then mellinInv (3 / 2) (reflectedSpectrum D r h) x else 0
variable {F : Type} [Field F] [NumberField F]

def kappa (data : PrincipalHeckeData F) : ℂ :=
  data.E 1 / ((Real.sqrt (principalDiscriminant F) : ℂ) *
    Complex.Gammaℂ 1 ^ principalComplexPlaces F)

end DedekindZetaZeroFree.LargeSieve.SquarePoisson

end
