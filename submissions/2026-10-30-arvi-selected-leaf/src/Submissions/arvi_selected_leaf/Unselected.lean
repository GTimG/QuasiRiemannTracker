/-
The unselected branch of the selected leaf: on the rows where the deleted block `D = A \ R` carries small
mass, `blockMass D < Z^{K w(D)}`, the block is deleted at the cut `K` and the retained energy is bounded on
all rows.
-/
import Submissions.arvi_selected_leaf.R1Statement
import Submissions.sil_density_split_20261026.Density.LeafRows

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

/-- **Deletion at the cut on the unselected rows.** -/
theorem unselected_delete {α : Type} [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ)
    (η₀ : Character) {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (hu : st.puncture = 1)
    (A R : Finset α) (hRA : R ⊆ A) (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ)
    (t K : ℝ) (hZ : 0 < Z) (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : A => primePool rayM H 2 (Z^(w i)))
      (fun (i : A) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : A => Z^(w i)) X₁ X₂
      (fun z => st.radial.keep z ∧
        ¬ Z^(K * ∑ i ∈ A \ R, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z (A \ R) z)
      st.radial.profile st.radial.scale ≤
    Z^(K * ∑ i ∈ A \ R, w i) *
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : R => primePool rayM H 2 (Z^(w i)))
        (fun (i : R) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i : R => Z^(w i)) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale := by
  set L : O → Prop := fun z =>
    ¬ Z^(K * ∑ i ∈ A \ R, w i) ≤ blockMass rayM H hH W η₀ st.character θ w σ v t Z (A \ R) z
    with hLdef
  let s' := QRH.SilDensitySplit.Density.restrictState st L
  have hu' : s'.puncture = 1 := hu
  have hdel := SilDensitySplit.CubeFree.energy_partial_delete s' hu' A R hRA
    (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) (fun _ => Real.rpow_nonneg hZ.le _) (p.profile 0) (p.profile 1) t X₁ X₂
    (Z^(K * ∑ i ∈ A \ R, w i)) (mul_pos hX₁ hX₂).le (by
      intro z hk _
      have hL : L z := hk.2
      have hlt := not_le.mp hL
      rw [norm_prod, ← Finset.prod_pow]
      exact hlt.le)
  have hmono := QRH.SilDensitySplit.Density.energy_mono_keep st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun i : R => primePool rayM H 2 (Z^(w i)))
    (fun (i : R) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i : R => Z^(w i)) X₁ X₂ st.radial.keep (fun z => st.radial.keep z ∧ L z)
    (fun z h => h.1) st.radial.profile st.radial.scale bΦ (fun z => st.radial.nonneg _)
    st.radial.scale_pos st.radial_support
  calc _ = energy s'.character s'.mask 1 t (p.profile 0) (p.profile 1)
        (fun i : A => primePool rayM H 2 (Z^(w i)))
        (fun (i : A) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i : A => Z^(w i)) X₁ X₂ s'.radial.keep s'.radial.profile s'.radial.scale := rfl
    _ ≤ _ := hdel
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hZ.le _)

end
end QRH.ArviSelectedLeaf
