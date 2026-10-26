/- Copyright (c) 2026 Sil. Apache-2.0.
The right-short reference is the SAME finite rectangle after exchanging
its two ordinary profiles and displayed lengths. Original source scales,
prefixes, marked slots, punctures, character and residual phase stay fixed.

-/
import Candidate.FourthPower.MixedFirstReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstReferenceOrientation
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentLattice CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentScaleSupremum
open CenteredMomentFiniteProfileExceptional CenteredMomentOriginalRadialComparison
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
open CenteredExceptionalProfile ReferencePrimeEnclosure
open MixedPrincipalPair MixedPrincipalHeights MixedCommonHeights
open MixedCommonRestriction MixedLiveNormalization
open MixedFirstReferenceDispatch MixedFirstReferenceChoice MixedFirstReferenceEnergy
open MixedFirstPuncturedReference MixedCanonicalSource ReferenceHeckeProducts
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Only the ordinary profiles and their frequencies are exchanged.
In particular X, Y, d and the product in the residual phase do not move.
The source record's geometric/support data are independent of W1/W2. -/
def swapProfiles (s : Source ι a b) : Source ι a b :=
  {s with
    W₁ := s.W₂
    W₂ := s.W₁
    hs₁ := s.hs₂
    hs₂ := s.hs₁
    t₁ := s.t₂
    t₂ := s.t₁}

/-- Exact finite reindexing, including all tuple restrictions, the whole
ordinary puncture, every marked coefficient and the original character. -/
theorem rectangle_swap (χ : Character) (S H : Finset PrimeIdeal) (R : Id)
    (pool : ι → Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    rectangleRow χ S H R pool ν Wslot P W₁ W₂ b X₁ X₂ =
      rectangleRow χ S H R pool ν Wslot P W₂ W₁ b X₂ X₁ := by
  unfold rectangleRow
  rw [mul_comm X₁ X₂]
  apply congrArg (normalization (X₂*X₁) P * ·)
  exact finite_swap pool (idealBall (b*X₁)) (idealBall (b*X₂)) (punctureProduct S H) R
    ν Wslot P W₁ W₂ X₁ X₂ 1 1 1 (idealCoeff χ)

/-- The original residual phase is literally unchanged: its source
length product and original prefixes were not exchanged. -/
theorem height_rectangle_swap (s : Source ι a b) (ha : 0 < a)
    (χ : Character) (t X₁ X₂ : ℝ) :
    heightRectangle (swapProfiles s) ha χ t X₂ X₁ = heightRectangle s ha χ t X₁ X₂ := by
  dsimp only [heightRectangle,swapProfiles,shiftSource]
  rw [rectangle_swap]

theorem height_energy_swap (s : Source ι a b) (ha : 0 < a)
    (χ : O → Character) (t X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z => heightRectangle (swapProfiles s) ha (χ z) t X₂ X₁) keep Φ K =
      radialEnergy (fun z => heightRectangle s ha (χ z) t X₁ X₂) keep Φ K := by
  unfold radialEnergy
  apply tsum_congr
  intro z
  simp only [height_rectangle_swap]

/-- Actual right-short orientation of the checked uniform energy bound.
The short scale is X2; therefore the volume cap is b*X2*prod(2P), not the
left-oriented cap. The long profile/height are the original W1 and t1. -/
theorem uniform_reference_energy_right
    (ε L Kcap a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hKcap : 0 < Kcap) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ n : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ (T : Finset ι) (s : Source T a b) (Z R Pexp sWidth d l δ : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ sWidth → 0 ≤ d → 0 ≤ l → 0 ≤ δ →
      Pexp+2*sWidth+4*d < R → R+(l+(R+d)/2+sWidth+2*δ) ≤ L →
      l+(R+d)/2+sWidth+2*δ ≤ (4/5)*R → R+d+2*l-Pexp+sWidth+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card T ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m : O) (F Q : Id)
        (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m),
      ∀ (keep : O → Prop), (∀ z, keep z → z ≠ 0) →
      (∀ z, keep z → ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) →
      ∀ (U X₁ X₂ Height t t₀ Bshort : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      s.ν = slotCoefficient ν R₀ t₀ →
      1 ≤ U → U ≤ Z^Kcap → U ≤ Z^(R+d) →
      0 < X₁ → 0 < X₂ → X₁*X₂ = Z^Pexp → X₂ ≤ Z^l →
      0 ≤ Height → ‖(s.t₁+t)/(2*Real.pi)‖ ≤ Height →
      0 ≤ Bshort → (∀ (j : Fin 2) (x : ℝ), ‖scaleTest (s.W₂ : ℝ → ℂ) j x‖ ≤ Bshort) →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∀ i I, I ∈ s.pool i →
        ‖slotCoefficient ν R₀ (t₀+t) i I*s.Wslot i (I.absNorm/s.P i)‖ ≤ Bf) →
      (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₂*(∏ i, 2*s.P i) ≤ Z^L →
      (∏ i, s.P i) ≤ Z^sWidth →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ), 0 < K → 0 ≤ bΦ →
      Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ → bΦ*K ≤ Z^R →
      conductorFactor η m F * (bΦ*K) ≤ U →
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η m F hm hF hmLam hm2 z) t X₁ X₂) keep Φ K ≤
        radialControl Φ * (C*(sourceControl control s.W₁)^2*
          (1+Height)^(2*n)*Z^(R+ε)*Bshort^2) := by
  obtain ⟨n,control,C,hC,h00,hbound⟩ := uniform_reference_energy (ι := ι)
    ε L Kcap a b xi Bf hε hL hKcap ha hb hxi hBf
  refine ⟨n,control,C,hC,h00,?_⟩
  intro T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₁ X₂ Height t t₀ Bshort ν R₀ hν hU hUcap hUsharp
    hX₁ hX₂ hprod hshort hHeight ht₁ hBshort htest hholes hS henclose
    hβ hHR hVcap hvolume hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  have hprod' : X₂*X₁ = Z^Pexp := by simpa only [mul_comm] using hprod
  have henclose' (I : Id) (hI : Supported I)
      (hN : (I.absNorm : ℝ) ≤ b*X₂ ∨ (I.absNorm : ℝ) ≤ b*X₁) :
      primeSupport I ⊆ primeValues s.S := henclose I hI hN.symm
  have he := hbound T (swapProfiles s) Z R Pexp sWidth d l δ
    hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₂ X₁ Height t t₀ Bshort ν R₀ hν hU hUcap hUsharp
    hX₂ hX₁ hprod' hshort hHeight ht₁ hBshort htest hholes hS henclose'
    hβ hHR hVcap hvolume hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  rw [height_energy_swap] at he
  exact he

/-- A common homogeneous reference estimate for either short ordinary factor. -/
theorem uniform_profiled_reference_energy_either
    (ε L Kcap a b xi Bf : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hKcap : 0 < Kcap) (ha : 0 < a)
    (hb : 0 ≤ b) (hxi : 0 < xi) (hBf : 1 ≤ Bf) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ (T : Finset ι) (s : Source T a b) (Z R Pexp sWidth d l δ : ℝ),
      1 ≤ Z → 0 ≤ R → 0 ≤ sWidth → 0 ≤ d → 0 ≤ l → 0 ≤ δ →
      Pexp+2*sWidth+4*d < R → R+(l+(R+d)/2+sWidth+2*δ) ≤ L →
      l+(R+d)/2+sWidth+2*δ ≤ (4/5)*R → R+d+2*l-Pexp+sWidth+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card T ≤ Z^δ → xi/2 ≤ δ →
      ∀ (η : Character) (m : O) (F Q : Id)
        (hm : m ≠ 0) (hF : Supported F) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m),
      ∀ (keep : O → Prop), (∀ z, keep z → z ≠ 0) →
      (∀ z, keep z → ¬FixedInducingRow η Q m ((primaryGenerator F)^2) z) →
      ∀ (U X₁ X₂ t t₀ V : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      s.ν = slotCoefficient ν R₀ t₀ →
      1 ≤ U → U ≤ Z^Kcap → U ≤ Z^(R+d) →
      0 < X₁ → 0 < X₂ → X₁*X₂ = Z^Pexp → (X₁ ≤ Z^l ∨ X₂ ≤ Z^l) →
      0 ≤ V →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∀ i I, I ∈ s.pool i →
        ‖slotCoefficient ν R₀ (t₀+t) i I*s.Wslot i (I.absNorm/s.P i)‖ ≤ Bf) →
      (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₁*(∏ i, 2*s.P i) ≤ Z^L → b*X₂*(∏ i, 2*s.P i) ≤ Z^L →
      (∏ i, s.P i) ≤ Z^sWidth →
      ∀ (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ), 0 < K → 0 ≤ bΦ →
      Function.support (Φ : ℝ → ℂ) ⊆ Iic bΦ → bΦ*K ≤ Z^R →
      conductorFactor η m F * (bΦ*K) ≤ U →
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η m F hm hF hmLam hm2 z) t X₁ X₂) keep Φ K ≤
        radialControl Φ * (C*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (MixedFirstProfileEnvelope.height t V s.t₁ s.t₂)^J*Z^(R+ε)) := by
  obtain ⟨J,control,C,hC,h00,hbound⟩ := uniform_profiled_reference_energy (ι := ι)
    ε L Kcap a b xi Bf hε hL hKcap ha hb hxi hBf
  refine ⟨J,control,C,hC,h00,?_⟩
  intro T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m F Q hm hF hmLam hm2 keep hkeep heligible
    U X₁ X₂ t t₀ V ν R₀ hν hU hUcap hUsharp
    hX₁ hX₂ hprod hshort hV hholes hS henclose
    hβ hHR hVcap hvolume₁ hvolume₂ hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  rcases hshort with hshort|hshort
  · exact hbound T s Z R Pexp sWidth d l δ hZ hR hs hd hl hδ hcap htotal hmax
      href hfixed hξ η m F Q hm hF hmLam hm2 keep hkeep heligible
      U X₁ X₂ t t₀ V ν R₀ hν hU hUcap hUsharp hX₁ hX₂ hprod hshort hV
      hholes hS henclose hβ hHR hVcap hvolume₁ hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
  · have hprod' : X₂*X₁ = Z^Pexp := by simpa only [mul_comm] using hprod
    have henclose' (I : Id) (hI : Supported I)
        (hN : (I.absNorm : ℝ) ≤ b*X₂ ∨ (I.absNorm : ℝ) ≤ b*X₁) :
        primeSupport I ⊆ primeValues s.S := henclose I hI hN.symm
    have he := hbound T (swapProfiles s) Z R Pexp sWidth d l δ
      hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
      η m F Q hm hF hmLam hm2 keep hkeep heligible
      U X₂ X₁ t t₀ V ν R₀ hν hU hUcap hUsharp hX₂ hX₁ hprod' hshort hV
      hholes hS henclose' hβ hHR hVcap hvolume₂ hVsharp Φ K bΦ hK hbΦ hΦ hradial hconductor
    rw [height_energy_swap] at he
    have hh : MixedFirstProfileEnvelope.height t V s.t₂ s.t₁ =
        MixedFirstProfileEnvelope.height t V s.t₁ s.t₂ := by
      unfold MixedFirstProfileEnvelope.height
      ring
    simpa only [swapProfiles,hh,mul_comm (sourceControl control s.W₂) (sourceControl control s.W₁)] using he

end
end Candidate.FourthPower.MixedFirstReferenceOrientation
