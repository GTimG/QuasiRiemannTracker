/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Whole-slot erasure on the actual final live type, with all three cost branches. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularLowActualCapacityCorners
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.CommonCapacity
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.CommonCost
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowActualCapacity
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentEnergyBands QRH.Record1252270103Low QRH.Record12518109Source
open QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O
local instance regularLowErasureDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem subtype_width_le {α : Type*} [Fintype α] (S : Finset α) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) : (∑ i : S, w i.val) ≤ ∑ i, w i := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)

variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁)
      C₂ (R*C₁) B₂ τ₂ t₂).pools C₃) (τ₃ : Character) (t₃ : ℝ)

theorem three_live_width_bounds (w : ι → ℝ) (b : ℝ)
    (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i, w i) ≤ b) :
    let f := (∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val
    0 ≤ f ∧ f ≤ b ∧ (∑ i : liveIndices B₃.val, w i.val.val.val) ≤ b-f := by
  intro f
  have h₁ := subtype_width_le (liveIndices B₁.val) w hw
  have h₂ := subtype_width_le (liveIndices B₂.val) (fun i => w i.val) (fun i => hw i.val)
  have h₃ := subtype_width_le (liveIndices B₃.val) (fun i => w i.val.val) (fun i => hw i.val.val)
  have hnon : 0 ≤ ∑ i : liveIndices B₃.val, w i.val.val.val :=
    Finset.sum_nonneg (fun i _ => hw i.val.val.val)
  dsimp only [f]
  exact ⟨sub_nonneg.mpr (h₃.trans (h₂.trans h₁)),by linarith,by linarith⟩

/-- The set is chosen from actual final live widths, before profiles, characters,
row labels and the choice of positive corner. -/
theorem three_live_erasure (w : ι → ℝ) (S : Finset (liveIndices B₃.val))
    (b cap mesh : ℝ) (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i, w i) ≤ b)
    (hmesh : 0 ≤ mesh) (hwm : ∀ i ∈ S, w i.val.val.val ≤ mesh) (hcap : 0 ≤ cap) :
    let f := (∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val
    ∃ E : Finset (liveIndices B₃.val), E ⊆ S ∧
      (∑ i ∈ S\E, w i.val.val.val) ≤ cap ∧
      (∑ i ∈ E, w i.val.val.val) ≤ max 0 (b-f-cap)+mesh := by
  intro f
  have hf := three_live_width_bounds s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ w b hw htotal
  have hS : (∑ i ∈ S, w i.val.val.val) ≤ b-f :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => hw i.val.val.val)).trans hf.2.2
  obtain ⟨E,hE,hleft,hcost⟩ := erase_to_first_cap S (fun i => w i.val.val.val)
    mesh (b-f) (min cap (b-f)) hmesh (le_min hcap (sub_nonneg.mpr hf.2.1))
    (min_le_right _ _) (fun i _ => hw i.val.val.val) hwm hS
  refine ⟨E,hE,?_,?_⟩
  · convert hleft.trans (min_le_left _ _) using 1
    congr 1
    ext i
    simp
  have he : b-f-min cap (b-f) = max 0 (b-f-cap) := by
    rcases le_total cap (b-f) with h|h
    · rw [min_eq_left h,max_eq_right (by linarith)]
    · rw [min_eq_right h,max_eq_left (by linarith)];ring
  simpa only [he] using hcost

/-- The geometric guard pays the actual support and rounding loss. Newton
divisors improve the cap; their nonnegative norm logs are retained. -/
theorem three_live_cap_nonneg (w : ι → ℝ) (Z b F t delta rho B lam h loss d₁ d₂ : ℝ)
    (hZ : 1 < Z) (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i, w i) ≤ b)
    (hB : B ≤ 1) (hlam : 0 < lam) (hd : 0 ≤ delta)
    (hdc : delta ≤ Real.logb Z (C₁.absNorm:ℝ)) (hh : 0 ≤ h)
    (hQ : 0 ≤ F-delta-rho) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂)
    (hguard : loss+B*rho ≤ B*F-t-b) :
    let c := Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ)
    let f := (∑ i, w i) - ∑ i : liveIndices B₃.val, w i.val.val.val
    0 ≤ min ((B*(F-delta-rho)-(t-c+f+loss-Real.logb Z d₁-Real.logb Z d₂))/lam)
      (h*(F-delta-rho)) := by
  intro c f
  have hc₂ := Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _
    (allocation_ne (child s C₁ R B₁ τ₁ t₁) C₂ B₂))
  have hc₃ := Real.logb_nonneg hZ (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _
    (allocation_ne (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ B₃))
  have hf := three_live_width_bounds s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ w b hw htotal
  have hn₁ := Real.logb_nonneg hZ hd₁
  have hn₂ := Real.logb_nonneg hZ hd₂
  have hc : delta ≤ c := by dsimp [c];linarith only [hdc,hc₂,hc₃]
  have hg : (loss-Real.logb Z d₁-Real.logb Z d₂)+B*rho ≤ B*F-t-b := by linarith
  convert raw_loss_cap_nonneg B lam F t b c delta f
    (loss-Real.logb Z d₁-Real.logb Z d₂) rho h hB hlam hd hc hf.2.1 hh hQ hg using 1 <;> ring

end
end QRH.Record1252270103Source.RegularLowActualCapacity
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.subtype_width_le
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_live_width_bounds
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_live_erasure
#print axioms QRH.Record1252270103Source.RegularLowActualCapacity.three_live_cap_nonneg
