/- Copyright (c) 2026 Sil. Apache-2.0.
Unamplified first-column windows at independent KL and KR.
The raw-side estimate is an explicit input.
-/
import Candidate.Feedback.FourthPower.RepairedFirstRawSides

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedFirstRawWindows
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open CenteredMomentSmoothedWindowEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondWindowSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentSmooth
open CenteredMomentCauchy CenteredMomentLogDyadic
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication
open MixedOriginalSecondZero RepairedFirstRawSides
open ActualEisensteinCubic CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def windowPolynomial (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (right : Bool) (t θ X : ℝ) (z : O) : ℂ :=
  gaussPolynomial Finset.univ (element opposite G hG.1 (sourceColumns s))
    (element_supported opposite G hG.1 (sourceColumns s))
    (fun I : columns opposite G hG.1 (sourceColumns s) =>
      originalResidual s ha 1 G u I*heightCoeff τ t I*
        windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z

theorem selected_one_window (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (right : Bool) (t θ X : ℝ) (z : O) :
    selectedRow s ha opposite G 1 u hG.1 τ t right logAnnulus X θ 1 z=
      windowPolynomial s ha opposite G hG u τ right t θ X z := by
  unfold selectedRow base windowPolynomial gaussPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  have hs : Supported I.val := by
    simpa only [element_span] using element_supported opposite G hG.1 (sourceColumns s) I
  simp only [primaryGenerator_one,idealRowHom_one_supported I.val hs,one_pow,mul_one]

theorem finite_window_le_energy (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (right : Bool) (t θ X K : ℝ) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀z∈rows,‖eisEmbedding z‖^2 ≤ K) :
    (∑z∈rows,‖windowPolynomial s ha opposite G hG u τ right t θ X z‖^2) ≤
      windowEnergy s ha opposite G hG u τ right t θ X K := by
  have hb := finite_weighted_le_gaussEnergy Finset.univ
    (element opposite G hG.1 (sourceColumns s)) (element_supported opposite G hG.1 (sourceColumns s))
    (fun I : columns opposite G hG.1 (sourceColumns s) =>
      originalResidual s ha 1 G u I*heightCoeff τ t I*
        windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
    ballProfile K hK (fun z => ballProfile_nonneg _) rows
  have hm (z : O) (hz : z∈rows) : ballProfile (‖eisEmbedding z‖^2/K)=1 :=
    ballProfile_one _ (div_nonneg (sq_nonneg _) hK.le) ((div_le_one hK).mpr (hrows z hz))
  have heq : (∑z∈rows,‖windowPolynomial s ha opposite G hG u τ right t θ X z‖^2)=
      ∑z∈rows,‖windowPolynomial s ha opposite G hG u τ right t θ X z‖^2*
        (ballProfile (‖eisEmbedding z‖^2/K)).re := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hm z hz,Complex.one_re,mul_one]
  rw [heq]
  exact hb

theorem left_column_bound (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (t θ X K : ℝ) (hX : 0 < X) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀z∈rows,‖eisEmbedding z‖^2 ≤ K)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀v : ℝ, rawEnergy s ha opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J)) :
    (∑z∈rows,‖leftColumn Finset.univ
      (rowVector s ha opposite G 1 u hG.1 τ t (fun _ => 1) 1 false (1,z)) logAnnulus
      (fun I : Columns s opposite G hG.1 => Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2) ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simp only [left_column,one_div,inv_one,Real.sqrt_one,Complex.ofReal_one,one_mul,
    selected_one_window s ha opposite G hG u τ false t θ X]
  exact (finite_window_le_energy s ha opposite G hG u τ false t θ X K hK rows hrows).trans
    (window_from_raw_heights s ha opposite G hG u τ K hK J E hE hraw false t θ X hX)

theorem right_column_bound (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (t θ X K : ℝ) (hX : 0 < X) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀z∈rows,‖eisEmbedding z‖^2 ≤ K)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀v : ℝ, rawEnergy s ha opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J)) :
    (∑z∈rows,‖rightColumn Finset.univ
      (rowVector s ha opposite G 1 u hG.1 τ t (fun _ => 1) 1 true (1,z)) logAnnulus
      (fun I : Columns s opposite G hG.1 => Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2) ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simp only [right_column,one_div,inv_one,Real.sqrt_one,Complex.ofReal_one,one_mul,norm_star,
    selected_one_window s ha opposite G hG u τ true t θ X]
  have hneg : ∀z∈rows.image Neg.neg,‖eisEmbedding z‖^2 ≤ K := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    simpa only [map_neg,norm_neg] using hrows y hy
  have hb := (finite_window_le_energy s ha opposite G hG u τ true t θ X K hK (rows.image Neg.neg) hneg).trans
    (window_from_raw_heights s ha opposite G hG u τ K hK J E hE hraw true t θ X hX)
  rw [Finset.sum_image (fun x _ y _ h => neg_injective h)] at hb
  exact hb

end
end Candidate.Feedback.FourthPower.RepairedFirstRawWindows
