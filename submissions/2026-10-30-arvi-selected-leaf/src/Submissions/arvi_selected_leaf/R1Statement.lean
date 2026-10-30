/-
The analytic input of the selected leaf (R1), as a statement.

On the rows of a natural state whose slot block `D` carries large mass,
`Z^{K·w(D)} ≤ ∏_{i∈D} ‖normalizedSlot_i‖²`, the energy of the whole packed polynomial (both plain sums,
all slots `T ⊇ D`) is bounded by the reflected selected large sieve summed over sixth roots:

  `Z^{M + selExcess (ℓX₁ + ℓX₂) (∑_T w) M + ε}`.

This is the only new analytic estimate of the selected-leaf chain. Its intended proof combines PR 93's
per-root selected all-source norm with the baseline's reflected energy engine
(`UniformOriginalComparison.actual_original_comparison`); see `research/selected-leaf/R1_NOTE.md`.
-/
import Submissions.arvi_selected_leaf.Price
import Submissions.sil_density_split_20261026.CubeFree.Leaf.Contract
import Submissions.sil_density_split_20261026.CubeFree.Leaf.PartialDeletion

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

/-- The mass of the slot block `D` at a row `z` (product of squared normalized slots). -/
def blockMass {α : Type} (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ) (η₀ ψ : Character)
    (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ) (t Z : ℝ) (D : Finset α) (z : O) : ℝ :=
  ∏ i ∈ D, ‖normalizedSlot ψ fixedBadMask 1 z (primePool rayM H 2 (Z^(w i)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t (Z^(w i))‖^2

/-- **R1: the selected root energy.** For the cut `K`, uniformly in the finite anchor family and in the
slot data, the energy of the rows whose block `D` (width `≥ smin`) has mass `≥ Z^{K w(D)}` is paid by
`selExcess`. -/
def SelectedRootEnergy (K : ℝ) : Prop :=
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
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
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

end
end QRH.ArviSelectedLeaf
