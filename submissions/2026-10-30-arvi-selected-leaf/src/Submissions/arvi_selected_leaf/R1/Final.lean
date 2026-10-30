/-
R1: `SelectedRootEnergyCap K` for `K ∈ [0.500001, 3/4]`, hence `SelectedRootEnergy K`.
-/
import Submissions.arvi_selected_leaf.R1.Main

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

theorem rpow_root_shift (Z a N : ℝ) (hZ : 1 < Z) (hN : 0 < N) :
    Z^(a - 5 * Real.logb Z N) = Z^a * N^(-(5:ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  rw [Real.rpow_sub hZ0, mul_comm 5 (Real.logb Z N), Real.rpow_mul hZ0.le,
    Real.rpow_logb hZ0 (ne_of_gt hZ) hN, Real.rpow_neg hN.le, div_eq_mul_inv]

theorem max_one_rpow_max (Z a : ℝ) (_hZ : 1 < Z) : max 1 (Z^(max 0 a)) ≤ max 1 (Z^a) := by
  rcases le_total 0 a with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, Real.rpow_zero, max_self]; exact le_max_left (1:ℝ) _

theorem weaken_lead (a x y c d e r : ℝ) (ha : 0 ≤ a) (hxy : x ≤ y) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hr : 0 ≤ r) : a * (x * c * d * e) * r ≤ a * (y * c * d * e) * r := by
  apply mul_le_mul_of_nonneg_right _ hr
  apply mul_le_mul_of_nonneg_left _ ha
  apply mul_le_mul_of_nonneg_right _ he
  apply mul_le_mul_of_nonneg_right _ hd
  exact mul_le_mul_of_nonneg_right hxy hc

/-- The product of the prime-slot norm bounds. -/
theorem prod_slot_bounds {α : Type} (T : Finset α) (w : α → ℝ) (Z : ℝ) (hZ : 0 < Z) :
    ∏ i : T, (2 * Z^(w i)) = 2^(Fintype.card T) * Z^(∑ i ∈ T, w i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.rpow_sum_of_pos hZ, Finset.sum_coe_sort T w]

theorem one_le_rpow_w (Z x : ℝ) (hZ : 1 ≤ Z) (hx : 0 ≤ x) : 1 ≤ Z^x := Real.one_le_rpow hZ hx

end
end QRH.ArviSelectedLeaf
