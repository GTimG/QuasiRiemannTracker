/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/ReflectedDualCutoffTail.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

def dualCutoffSummand (F : Type*) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ) (d b : Ideal (𝓞 F)) : ℂ :=
  if b ≠ ⊥ ∧ L < (Ideal.absNorm b : ℝ)
  then k (T * (Ideal.absNorm b : ℝ) / (Ideal.absNorm d : ℝ)) else 0

def dualCutoffTail (F : Type*) [Field F] [NumberField F]
    (k : ℝ → ℂ) (T L : ℝ) (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ d ∈ D, a d * (T / (Ideal.absNorm d : ℝ) : ℂ) *
    ∑' b : Ideal (𝓞 F), dualCutoffSummand F k T L d b

end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
