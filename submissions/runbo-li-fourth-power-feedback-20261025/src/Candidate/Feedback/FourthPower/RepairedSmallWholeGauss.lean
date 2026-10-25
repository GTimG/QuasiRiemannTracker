/- Copyright (c) 2026 Sil. Apache-2.0.
Exact four-piece positive bound for the whole small sigma Gauss energy,
at original K and its original cutoff. The scalar zero matches the plain
remainder supplier; the native term matches RepairedSmallOriginalScale.

-/
import Candidate.Feedback.FourthPower.RepairedSmallEmptyGauss
import Candidate.Feedback.FourthPower.MixedFirstLiveEnergy
import Candidate.Feedback.FourthPower.MixedLocalizedDictionary

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedSmallWholeGauss
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open EisensteinSchwartzPoisson RayFourExpansion
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondEnergySplit
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open MixedPrincipalPair MixedPrincipalWindow MixedFirstLiveEnergy MixedPoissonLocalization
open MixedLocalizedDictionary RepairedSmallEmptyGauss
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem original_scale_four_parts (s : Source ι a b) (ha : 0<a) (seed : Id)
    (η : Character) (χ : RayCharacter) (Q : Id) (m : HeckeFamily.O)
    (t K T Z ξ H : ℝ) (hK : 0<K) :
    (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed)
      (heightCoeff η t) ballProfile K).re≤
      ‖(K:ℂ)*paperRadialFourier ballProfile 0*
        sourceSecondZero (sourceColumns s) (sourceCoefficient s ha seed) η t‖+
      ‖secondRetainedEnergy η t (sourceColumns s) (sourceCoefficient s ha seed)
          ballProfile K T Z ξ-
        partEnergy true η χ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
          ballProfile K T Z ξ H‖+
      ‖partEnergy true η χ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
        ballProfile K T Z ξ H‖+
      ‖secondDiscardedEnergy η t (sourceColumns s) (sourceCoefficient s ha seed)
        ballProfile K T Z ξ‖ := by
  have hscale : 16*(K/16)*(1:ℝ)^4=K := by ring
  have he := live_density_four_parts s ha seed η t (K/16) 1 (frequencyRadius T Z ξ)
    (by positivity) (by norm_num)
    (partEnergy true η χ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
      ballProfile K T Z ξ H)
  rw [source_retained η t (sourceColumns s) (sourceCoefficient s ha seed)
      (K/16) 1 T Z ξ (by norm_num),
    source_discarded η t (sourceColumns s) (sourceCoefficient s ha seed)
      (K/16) 1 T Z ξ (by norm_num)] at he
  simp only [hscale,Complex.ofReal_one,div_one] at he
  have hzero : zeroDensity Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s) => sourceCoefficient s ha seed I*heightCoeff η t I)
      (K/16) 1=(K:ℂ)*paperRadialFourier ballProfile 0*
        sourceSecondZero (sourceColumns s) (sourceCoefficient s ha seed) η t := by
    unfold zeroDensity sourceSecondZero
    simp only [one_pow,mul_one,show (16:ℝ)*(K/16)=K by ring]
  rw [hzero] at he
  convert he using 1 <;> ring

/-- Assembly only: these four inputs name the exact proved provider terms,
not an opaque replacement energy or a new source estimate. -/
theorem original_scale_energy_of_bounds (s : Source ι a b) (ha : 0<a) (seed : Id)
    (η : Character) (χ : RayCharacter) (Q : Id) (m : HeckeFamily.O)
    (t K T Z ξ H A0 A1 A2 A3 : ℝ) (hK : 0<K)
    (h0 : ‖(K:ℂ)*paperRadialFourier ballProfile 0*
      sourceSecondZero (sourceColumns s) (sourceCoefficient s ha seed) η t‖≤A0)
    (h1 : ‖secondRetainedEnergy η t (sourceColumns s) (sourceCoefficient s ha seed)
        ballProfile K T Z ξ-
      partEnergy true η χ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
        ballProfile K T Z ξ H‖≤A1)
    (h2 : ‖partEnergy true η χ Q m t (sourceColumns s) (sourceCoefficient s ha seed)
      ballProfile K T Z ξ H‖≤A2)
    (h3 : ‖secondDiscardedEnergy η t (sourceColumns s) (sourceCoefficient s ha seed)
      ballProfile K T Z ξ‖≤A3) :
    (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed)
      (heightCoeff η t) ballProfile K).re≤A0+A1+A2+A3 :=
  (original_scale_four_parts s ha seed η χ Q m t K T Z ξ H hK).trans
    (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)

end
end Candidate.Feedback.FourthPower.RepairedSmallWholeGauss
