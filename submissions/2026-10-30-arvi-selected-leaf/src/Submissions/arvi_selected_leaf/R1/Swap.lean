/-
Reduction of R1 to ordered plain lengths `X₂ ≤ X₁` (the energy, the profile control and the length sum are
symmetric in the two plain sums).
-/
import Submissions.arvi_selected_leaf.R1.Helpers
import Submissions.arvi_selected_leaf.R1Statement

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open Cycle61Moment
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentEnergyCapacityRemoval
open CenteredMomentNaturalRowSource
open CenteredMomentCoreFloor CenteredMomentWholeSlotDeletion
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRayMaskedFloor
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

/-- R1 for ordered plain lengths. -/
def SelectedRootEnergyOrd (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ smin Mmin Mcap : ℝ, 0 < smin → 0 < Mmin → Mmin ≤ Mcap →
  ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, mesh ≤ meshMax →
  ∀ (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
  ∀ (κ : Type) [Fintype κ] (anchors : κ → Character) (η₀ : Character) (bΦ : ℝ), 2 ≤ bΦ →
  ∃ degree : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
  ∀ (j : κ) (st : NaturalState Z 0 bΦ), st.character = anchors j → st.puncture = 1 →
    Mmin ≤ st.rowWidth → st.width ≤ Mcap →
  ∀ (T D : Finset α), D ⊆ T →
  ∀ (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ 33/50) →
    0 ≤ height → (∀ i, |v i| ≤ height) → smin ≤ ∑ i ∈ D, w i →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₂ ≤ X₁ →
    length Z X₁ ≤ 4 → length Z X₂ ≤ 4 →
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : T => primePool rayM H 2 (Z^(w i)))
      (fun (i : T) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : T => Z^(w i)) X₁ X₂
      (fun z => st.radial.keep z ∧
        Z^(K * ∑ i ∈ D, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z D z)
      st.radial.profile st.radial.scale ≤
    C * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
      (1+|t|+height)^degree *
      Z^(st.rowWidth + selExcess (length Z X₁ + length Z X₂) (∑ i ∈ T, w i) st.rowWidth + ε)

/-- The profiles with the two plain sums exchanged. -/
def swapProfiles {lo hi : ℝ} (p : Profiles lo hi) : Profiles lo hi where
  profile := ![p.profile 1, p.profile 0]
  support := by
    intro i
    fin_cases i
    · exact p.support 1
    · exact p.support 0

theorem swapProfiles_control {lo hi : ℝ} (p : Profiles lo hi) (S : Finset (ℕ×ℕ)) :
    (swapProfiles p).control S = p.control S := by
  show sourceControl S ((swapProfiles p).profile 0) * sourceControl S ((swapProfiles p).profile 1) =
    sourceControl S (p.profile 0) * sourceControl S (p.profile 1)
  have h0 : (swapProfiles p).profile 0 = p.profile 1 := rfl
  have h1 : (swapProfiles p).profile 1 = p.profile 0 := rfl
  rw [h0, h1, mul_comm]

/-- **Reduction to ordered plain lengths.** -/
theorem selectedRootEnergy_of_ord (K : ℝ) (h : SelectedRootEnergyOrd K) : SelectedRootEnergy K := by
  intro ε hε smin Mmin Mcap hsmin hMmin hMcap
  obtain ⟨meshMax, hmeshMax, h⟩ := h ε hε smin Mmin Mcap hsmin hMmin hMcap
  refine ⟨meshMax, hmeshMax, ?_⟩
  intro mesh hmesh α _ _ rayM _ H hH W hW hWs κ _ anchors η₀ bΦ hbΦ
  obtain ⟨degree, S, C, hC, hev⟩ := h mesh hmesh α rayM H hH W hW hWs κ anchors η₀ bΦ hbΦ
  refine ⟨degree, S, C, hC, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro j st hchar hpunc hM1 hM2 T D hDT θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD p X₁ X₂ hX₁ hX₂
    hl₁ hl₂
  rcases le_total X₂ X₁ with h21 | h12
  · exact hZ.2 j st hchar hpunc hM1 hM2 T D hDT θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD p X₁ X₂
      hX₁ hX₂ h21 hl₁ hl₂
  · have hs := hZ.2 j st hchar hpunc hM1 hM2 T D hDT θ w σ v t height hw hwm hσ1 hσ2 hh hv hsD
      (swapProfiles p) X₂ X₁ hX₂ hX₁ h12 hl₂ hl₁
    rw [swapProfiles_control, add_comm (length Z X₂) (length Z X₁)] at hs
    rw [R1.energy_swap]
    exact hs

end
end QRH.ArviSelectedLeaf
