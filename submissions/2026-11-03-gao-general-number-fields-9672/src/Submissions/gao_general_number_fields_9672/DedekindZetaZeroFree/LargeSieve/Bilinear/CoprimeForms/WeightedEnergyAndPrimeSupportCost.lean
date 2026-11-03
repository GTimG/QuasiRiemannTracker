/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Bilinear/CoprimeForms/WeightedEnergyAndPrimeSupportCost.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LargeSieve.Bilinear.QuadraticFormsAndSieveExponents

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

def primeSupportCost {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) : ℝ :=
  (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card

def maskedRowWeight {F : Type} [Field F] [NumberField F]
    (W : ℝ → ℝ) (q d : Ideal (𝓞 F)) (M : ℝ)
    (rowMask : Ideal (𝓞 F) → ℝ) (a : Ideal (𝓞 F)) : ℝ :=
  if a ⊔ (q * d) = ⊤ then W ((Ideal.absNorm a : ℝ) / M) * rowMask a else 0

def weightedEnergy {F : Type} [Field F] [NumberField F]
    {R : Type*} (rows : Finset R) (cols : Finset (Ideal (𝓞 F)))
    (w : R → ℝ) (A : R → Ideal (𝓞 F) → ℂ)
    (alpha : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ r ∈ rows, w r * ‖∑ u ∈ cols, A r u * alpha u‖ ^ 2

def coprimeForm {F : Type} [Field F] [NumberField F]
    {R : Type*} (rows : Finset R) (cols : Finset (Ideal (𝓞 F)))
    (w : R → ℝ) (A : R → Ideal (𝓞 F) → ℂ)
    (alpha : Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ r ∈ rows, (w r : ℂ) *
    ∑ u ∈ cols, ∑ v ∈ cols,
      if u ⊔ v = ⊤ then (A r u * alpha u) * star (A r v * alpha v) else 0

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end
