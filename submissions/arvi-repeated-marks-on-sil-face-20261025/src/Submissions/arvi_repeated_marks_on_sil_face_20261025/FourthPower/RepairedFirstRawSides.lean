/- Copyright (c) 2026 Sil. Apache-2.0.
EXPLICIT intermediate RawSideBounds contract. This is a mechanism,
not a proof that Raw/Small already supply the contract. Both physical
radii, common allowances and original u norm remain. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstPhysicalApplication
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstExceptionalNormalization
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedFirstRawSides
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open CenteredMomentSmoothedWindowEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondWindowSource
open CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization CenteredMomentSmooth
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication MixedOriginalSecondZero
open MixedFirstExceptionalNormalization
open MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- RAW first residual Gauss energy at its own physical radius. -/
def rawEnergy (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (v K : ℝ) : ℝ :=
  (gaussEnergy Finset.univ (element opposite G hG.1 (sourceColumns s))
    (element_supported opposite G hG.1 (sourceColumns s))
    (fun I : columns opposite G hG.1 (sourceColumns s) =>
      originalResidual s ha 1 G u I*heightCoeff τ v I)
    ballProfile K).re

def windowEnergy (s : Source ι a b) (ha : 0 < a) (opposite G : Id) (hG : Supported G)
    (u : Id) (τ : Character) (right : Bool) (t θ X K : ℝ) : ℝ :=
  (gaussEnergy Finset.univ (element opposite G hG.1 (sourceColumns s))
    (element_supported opposite G hG.1 (sourceColumns s))
    (fun I : columns opposite G hG.1 (sourceColumns s) =>
      originalResidual s ha 1 G u I*heightCoeff τ t I*
        windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
    ballProfile K).re

def sideBudget (s : Source ι a b) (τ : Character) (G opposite u : Id) (A Z loss : ℝ) : ℝ :=
  A*reference τ G opposite (sourceVolume s) Z*Z^loss/(u.absNorm:ℝ)

theorem sideBudget_nonneg (s : Source ι a b) (τ : Character) (G opposite u : Id)
    (A Z loss : ℝ) (hA : 0 ≤ A) (hZ : 0 ≤ Z) : 0 ≤ sideBudget s τ G opposite u A Z loss := by
  unfold sideBudget reference
  positivity

/-- Exact remaining analytical supply from Raw/Small, deliberately not
asserted here. A will be the explicit original profile/height factor. -/
def RawSideBounds (s : Source ι a b) (ha : 0 < a) (η : Character)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss : ℝ) (J : ℕ) : Prop :=
  ∀ u ∈ artificialDivisors s C D hD.1,
    (UniqueFactorizationMonoid.moebius u:ℂ)≠0 → ∀ χ ξ : RayCharacter,
    let F := fixedPair η C D hC E χ (ξ⁻¹)
    (∀ v : ℝ, rawEnergy s ha D C hC u F.left v KL ≤
      sideBudget s F.left C D u A Z loss*(1+‖v‖)^(2*J)) ∧
    (∀ v : ℝ, rawEnergy s ha C D hD u F.right v KR ≤
      sideBudget s F.right D C u A Z loss*(1+‖v‖)^(2*J))

/-- Direct column smoothing at K, without a 16*K or fourth-power
amplification. The right window is the genuine conjugate window. -/
theorem window_from_raw_heights (s : Source ι a b) (ha : 0 < a)
    (opposite G : Id) (hG : Supported G) (u : Id) (τ : Character)
    (K : ℝ) (hK : 0 < K) (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀ v : ℝ, rawEnergy s ha opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J))
    (right : Bool) (t θ X : ℝ) (hX : 0 < X) :
    windowEnergy s ha opposite G hG u τ right t θ X K ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  have hleft (θ : ℝ) : windowEnergy s ha opposite G hG u τ false t θ X K ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
    have he := smoothed_window_energy_from_height logAnnulus logAnnulus_compact logAnnulus_smooth
      J Finset.univ (element opposite G hG.1 (sourceColumns s))
      (element_supported opposite G hG.1 (sourceColumns s))
      (fun I : columns opposite G hG.1 (sourceColumns s) => originalResidual s ha 1 G u I)
      τ t θ X hX ballProfile K hK (fun z => ballProfile_nonneg _) E hE
      (fun v => by simpa only [rawEnergy,element_span] using hraw v)
    have he' : windowEnergy s ha opposite G hG u τ false t θ X K ≤
        (E*heightCost t θ^(2*J))*profileMoment J^2 := by
      simpa only [windowEnergy,windowFactor,Bool.false_eq_true,if_false,element_span,profileMoment] using he
    exact he'.trans (shifted_window_budget J t θ E hE)
  cases right
  · exact hleft θ
  · simpa only [windowEnergy,windowFactor,Bool.false_eq_true,if_false,if_true,
      star_logAnnulus_column,norm_neg] using hleft (-θ)

end
end Candidate.FourthPower.RepairedFirstRawSides
