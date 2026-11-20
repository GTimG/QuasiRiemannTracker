/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LFunctions/Dedekind/WeightedIdealEulerProducts.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Dedekind.WeightedIdealSummability
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LFunctions.Dedekind.MultiplicativeIdealEulerProduct

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField BigOperators

theorem weightedIdealEulerProduct_hasProd
    (K : Type*) [Field K] [NumberField K]
    (w : Ideal (𝓞 K) → ℂ)
    (hmul : ∀ I J, w (I * J) = w I * w J)
    (htop : w ⊤ = 1) (hbot : w ⊥ = 0)
    (hnorm : ∀ I, ‖w I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd
      (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        (1 - w P.asIdeal * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
      (∑' I : Ideal (𝓞 K), w I * (Ideal.absNorm I : ℂ) ^ (-s)) := by
  obtain ⟨g, hg⟩ := weightedIdealSummandHom_exists K w hmul htop hbot hnorm s hs
  have hsum : Summable (fun I : Ideal (𝓞 K) => ‖g I‖) := by
    simpa only [hg] using weightedIdealSummability K w hmul htop hbot hnorm s hs
  simpa only [hg] using genericIdealEulerProduct K g hsum

theorem dedekindZeta_hasSum_nonzeroIdeals
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasSum
      (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))
      (NumberField.dedekindZeta K s) := by
  exact DedekindZetaZeroFree.Odlyzko.hasSum_nonzeroIdeal_inverseNormPower K hs

theorem dedekindZeta_idealEulerProduct_hasProd
    (K : Type*) [Field K] [NumberField K] (s : ℂ) (hs : 1 < s.re) :
    HasProd
      (fun P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  exact DedekindZetaZeroFree.Odlyzko.dedekindZeta_primeIdeal_eulerProduct_hasProd K hs

end DedekindZetaZeroFree.AbelianQuotient
