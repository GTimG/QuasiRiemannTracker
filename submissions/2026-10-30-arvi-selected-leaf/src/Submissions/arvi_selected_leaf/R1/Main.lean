/-
R1: the selected root energy for ordered plain lengths and bounded slot weight (`SelectedRootEnergyCap K`,
`K ∈ [0.500001, 3/4]`), hence `SelectedRootEnergy K` (`Swap`, `Peel`).

The energy of the heavy rows is split over sixth-root classes (`radial_root_split`). On each class:
* the direct bound: PR 93's selected norm on the row polynomial (`root_bound_direct`);
* if the long plain length is at least one, the reflected bound: the baseline's reflected engine with the
  radical row characters, whose conductor is `≲ Z^M N(r)^{-5}` (`root_bound_reflected`).
The classes are summed with the root zeta series and the interpolation of minima (`root_class_sum`), and the
exponent arithmetic (`bracket_bound`) gives `Z^{M + selExcess + ε}`.
-/
import Submissions.arvi_selected_leaf.R1.Arith
import Submissions.arvi_selected_leaf.JointDetector.FineCanonicalFromNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalUniformNear
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseUniformScale
import Submissions.arvi_selected_leaf.JointDetector.RefinedSupplier

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
open Qrh.JointDetector
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem norm_le_control (S : Finset (ℕ×ℕ)) (hS : ((0:ℕ),(0:ℕ)) ∈ S) (W : 𝓢(ℝ,ℂ)) (x : ℝ) :
    ‖W x‖ ≤ sourceControl S W := by
  have h1 : ‖W x‖ ≤ SchwartzMap.seminorm ℝ 0 0 W := SchwartzMap.norm_le_seminorm ℝ W x
  have h2 : schwartzSeminormFamily ℝ ℝ ℂ ((0:ℕ),(0:ℕ)) W ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    Seminorm.le_finset_sup_apply hS
  rw [SchwartzMap.schwartzSeminormFamily_apply] at h2
  exact h1.trans h2

theorem control_mono (S T : Finset (ℕ×ℕ)) (h : T ⊆ S) (W : 𝓢(ℝ,ℂ)) :
    T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ sourceControl S W :=
  Seminorm.le_def.mp (Finset.sup_mono h) W

/-- Rows outside the radial support do not contribute. -/
theorem energy_support_restrict {ι : Type*} [Fintype ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ) (hK : 0 < K)
    (hsupp : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      energy η m A t W₁ W₂ S β P X₁ X₂ (fun z => keep z ∧ ‖eisEmbedding z‖^2 ≤ bΦ * K) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · by_cases hz : ‖eisEmbedding z‖^2 ≤ bΦ * K
    · simp [hk, hz]
    · have hΦ0 : Φ (‖eisEmbedding z‖^2/K) = 0 := by
        by_contra hne
        have h1 := hsupp hne
        simp only [Set.mem_Iic] at h1
        rw [div_le_iff₀ hK] at h1
        exact hz (by linarith)
      simp [hk, hz, hΦ0]
  · simp [hk]

/-- PR 93's slot mass of the heavy block is the block mass. -/
theorem slotMass_eq_blockMass {α : Type} [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H) {Z bΦ : ℝ}
    (st : NaturalState Z 0 bΦ) (hpunc : st.puncture = 1) (η₀ : Character) (W : ℝ → ℂ)
    (θ : α → RayQuotient.Characters rayM H) (w σ v : α → ℝ) (t : ℝ) (D : Finset α) (z : O)
    (hz : z ≠ 0) :
    RefinedSupplier.slotMass rayM H hH st η₀ W (fun k : D => θ k) (fun k : D => w k)
      (fun k : D => σ k) (fun k : D => v k) t z =
      blockMass rayM H hH W η₀ st.character θ w σ v t Z D z := by
  have hm : st.mask = fixedBadMask * idealGenerator 1 := by rw [NaturalState.mask, hpunc]
  unfold RefinedSupplier.slotMass blockMass
  rw [hm]
  simp only [SilDensitySplit.Density.slot_unit_mask (naturalRow st.character z hz)]
  exact Finset.prod_coe_sort D (fun i => ‖normalizedSlot st.character fixedBadMask 1 z
    (primePool rayM H 2 (Z^(w i)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t (Z^(w i))‖^2)

/-- **Combining the direct and the reflected bound of a class** into the form of the root sum. -/
theorem class_combine (A Y Xd Xe Y₀ Bsix N Dd Rr Q f : ℝ) (hA : 0 ≤ A)
    (hY : Y ≤ Y₀ + Bsix * N^(-(6:ℝ))) (hXd : Xd ≤ Dd)
    (hXe : Xe ≤ Rr * max 1 (Q * N^(-(5:ℝ))))
    (hX0 : 0 ≤ Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ)))))
    (hfd : f ≤ A * (Xd + Y)) (hfe : f ≤ A * (Xe + Y)) :
    f ≤ (9/4) * A * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ))))) := by
  have h1 : f ≤ A * (min Xd Xe + Y) := by
    rcases le_total Xd Xe with h | h
    · rw [min_eq_left h]; exact hfd
    · rw [min_eq_right h]; exact hfe
  have h2 : min Xd Xe ≤ min Dd (Rr * max 1 (Q * N^(-(5:ℝ)))) := min_le_min hXd hXe
  have h3 : A * (min Xd Xe + Y) ≤ A * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ))))) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h4 : A * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ))))) ≤
      (9/4) * A * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ))))) := by
    have := mul_nonneg hA hX0
    nlinarith
  linarith

/-- The direct-only variant (long plain length below one: `Dd ≤ 9/4·Rr`). -/
theorem class_combine_direct (A Y Xd Y₀ Bsix N Dd Rr Q f : ℝ) (hA : 0 ≤ A)
    (hY : Y ≤ Y₀ + Bsix * N^(-(6:ℝ))) (hXd : Xd ≤ Dd) (hDd0 : 0 ≤ Dd) (hRr : 0 ≤ Rr)
    (hDd : Dd ≤ (9/4) * Rr) (hY0 : 0 ≤ Y) (hfd : f ≤ A * (Xd + Y)) :
    f ≤ (9/4) * A * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ))))) := by
  have hm : Dd ≤ (9/4) * min Dd (Rr * max 1 (Q * N^(-(5:ℝ)))) := by
    rcases le_total Dd (Rr * max 1 (Q * N^(-(5:ℝ)))) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]
      have : Rr ≤ Rr * max 1 (Q * N^(-(5:ℝ))) := le_mul_of_one_le_right hRr (le_max_left _ _)
      linarith
  have hYs : Y ≤ (9/4) * (Y₀ + Bsix * N^(-(6:ℝ))) := by
    have : 0 ≤ Y₀ + Bsix * N^(-(6:ℝ)) := hY0.trans hY
    linarith
  calc f ≤ A * (Xd + Y) := hfd
    _ ≤ A * ((9/4) * (Y₀ + Bsix * N^(-(6:ℝ)) + min Dd (Rr * max 1 (Q * N^(-(5:ℝ)))))) := by
        apply mul_le_mul_of_nonneg_left _ hA
        linarith
    _ = _ := by ring

end
end QRH.ArviSelectedLeaf
