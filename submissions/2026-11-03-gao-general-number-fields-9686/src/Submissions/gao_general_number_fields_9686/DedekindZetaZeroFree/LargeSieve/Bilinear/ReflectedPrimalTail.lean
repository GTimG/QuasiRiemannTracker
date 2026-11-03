/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Bilinear/ReflectedPrimalTail.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.InverseNormPowerSums
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.Ideals.DivisorFinsets

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.ReflectedTails

def primalSummand (F : Type*) [Field F] [NumberField F]
    (g : ℝ → ℂ) (T : ℝ) (d b : Ideal (𝓞 F)) : ℂ :=
  if b = ⊥ then 0 else g ((Ideal.absNorm d : ℝ) * (Ideal.absNorm b : ℝ) / T)

def primalTail (F : Type*) [Field F] [NumberField F]
    (g : ℝ → ℂ) (T : ℝ) (D : Finset (Ideal (𝓞 F)))
    (a : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ d ∈ D, a d * ∑' b : Ideal (𝓞 F), primalSummand F g T d b

end DedekindZetaZeroFree.LargeSieve.ReflectedTails

end
