/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/SpectralTheory/FiniteCenterSums/ConjugateWordPairing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.SpectralTheory.FiniteCenterSums.WordPairing

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
 abbrev rightPairingWordDerivative := KPSmoothActualFlowData.wordDerivative F ζ hζ

theorem conjugate_pairing (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (f g : KPSmoothLocalQuotientCharts.X F ζ hζ → ℂ) :
    star (∫ q, star (f q) * g q ∂ R.quotientHaar) =
      ∫ q, star (g q) * f q ∂ R.quotientHaar := by
  rw [Complex.star_def, ←integral_conj]
  apply integral_congr_ae
  filter_upwards with q
  simp only [map_mul, starRingEnd_self_apply, mul_comm]

theorem finite_word_pairing_right
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (f : ι → smoothAllWordL2 R) (g : smoothAllWordL2 R)
    (w : ι → List (KPSmoothActualFlowData.B F)) :
    (∫ q, star (g.val q) * (∑ i ∈ s, a i * rightPairingWordDerivative (w i) (f i).val q) ∂ R.quotientHaar) =
      ∑ i ∈ s, a i * (-1 : ℂ)^(w i).length *
        ∫ q, star (rightPairingWordDerivative (w i).reverse g.val q) * (f i).val q ∂ R.quotientHaar := by
  have he := congrArg star (finite_word_pairing R s a f g w)
  rw [conjugate_pairing] at he
  simp only [star_sum, star_mul, star_star, star_pow, star_neg, star_one] at he
  simp only [conjugate_pairing] at he
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
