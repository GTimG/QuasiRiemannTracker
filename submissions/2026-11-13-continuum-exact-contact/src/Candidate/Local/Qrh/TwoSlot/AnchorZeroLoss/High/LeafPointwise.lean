/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `actual_high_slots` (`Cycle61/Moment/HighSlots.lean`) and
`whole_source_upper_actual_low` (`Cycle61/Moment/WholeSourceFamily.lean`), Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.RowSplit
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafSlots
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighSlots
import Submissions.hailey_collet_1252270103.Cycle61.Moment.WholeSourceFamily

/-!
# High.LeafPointwise

The pointwise row inputs of the HIGH leaf. The slots of
`HighBranchMesh` are indexed by a `T : Finset α`; they are extended to `α` (`extSlot`) so that the
core batches can use the fixed slot type `α` (chosen before the scale). For a HIGH row `z` with
upper guard `< b + 2e` at the height `3(i+1)Z^τ`:

* `‖row z‖² ≤ K ctl² Z^((2b-1)(ℓ₁+ℓ₂) + 2ε₁d) ∏_{x∈T} slotNs x` (`High.RowSplit.high_row_split`);
* `slotNs x ≤ Cs Z^(2ε₁d) Z^((2b-1) w_x)` for every slot (HC `actual_high_slots`, through
  `whole_source_upper_actual_low`).

`slotNs x` is the squared normalized slot at `x`; for a raw row `z = u·B⁶` of a unit-puncture state it
equals HC's squared raw slot (`slotNs_eq_raw`, from `High.LeafSlots.state_slot_norm_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000000000

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open LocalMoment Cycle61HighProfiles HeckeDetectorZeros
open QRH.SilDensitySplit.Density HeckeDyadic HeckeDetectorCoefficientTransfer
local notation "O" => HeckeFamily.O

/-- A slot datum on `T` extended to `α` by a default value. -/
def extSlot {α β : Type*} {T : Finset α} (f : T → β) (d : β) (x : α) : β :=
  if hx : x ∈ T then f ⟨x, hx⟩ else d

theorem extSlot_coe {α β : Type*} {T : Finset α} (f : T → β) (d : β) (k : T) :
    extSlot f d k.val = f k := by
  unfold extSlot
  rw [dif_pos k.2]

theorem extSlot_mem {α β : Type*} {T : Finset α} (f : T → β) (d : β) {x : α} (hx : x ∈ T) :
    extSlot f d x = f ⟨x, hx⟩ := by
  unfold extSlot
  rw [dif_pos hx]

section
variable (rayM : Ideal O) [NeZero rayM]
local instance leafPointwiseQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The squared normalized slot of the packed row at the (extended) slot `x`. -/
def slotNs {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character) (W : ℝ → ℂ)
    {α : Type*} {T : Finset α} (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t : ℝ)
    (z : O) (x : α) : ℝ :=
  ‖normalizedSlot st.character st.mask 1 z (primePool rayM H 2 (Z^(extSlot w 0 x)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (extSlot θ 1 x)) I *
      HeckePrimeAnnular.annularWeight W (Z^(extSlot w 0 x)) (extSlot σ (33/50) x)
        (extSlot v' 0 x) I) t (Z^(extSlot w 0 x))‖^2

theorem slotNs_nonneg {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (W : ℝ → ℂ) {α : Type*} {T : Finset α} (θ : T → RayQuotient.Characters rayM H)
    (w σ v' : T → ℝ) (t : ℝ) (z : O) (x : α) :
    0 ≤ slotNs rayM H hH st η₀ W θ w σ v' t z x := sq_nonneg _

/-- The product over the slots of `T`, as a product over `T ⊆ α`. -/
theorem prod_slot_eq {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (W : ℝ → ℂ) {α : Type*} (T : Finset α) (θ : T → RayQuotient.Characters rayM H)
    (w σ v' : T → ℝ) (t : ℝ) (z : O) :
    ∏ k : T, ‖normalizedSlot st.character st.mask 1 z (primePool rayM H 2 (Z^(w k)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I) t (Z^(w k))‖^2 =
      ∏ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t z x := by
  rw [← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold slotNs
  rw [extSlot_coe, extSlot_coe, extSlot_coe, extSlot_coe]

/-- **Raw slot dictionary at an extended slot.** -/
theorem slotNs_eq_raw {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hpunct : st.puncture = 1) (W : ℝ → ℂ) {α : Type*} {T : Finset α}
    (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t : ℝ) (z : O) (hz0 : z ≠ 0)
    (x : α) :
    slotNs rayM H hH st η₀ W θ w σ v' t z x =
      ‖CenteredMomentCommonMaskExpansion.naturalSlot
        (excluded (naturalRow st.character z hz0).character 1)
        (primePool rayM H 2 (Z^(extSlot w 0 x)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (extSlot θ 1 x)) I *
          HeckePrimeAnnular.annularWeight W (Z^(extSlot w 0 x)) (extSlot σ (33/50) x)
            (t + extSlot v' 0 x) I) (Z^(extSlot w 0 x))‖^2 := by
  unfold slotNs
  have hpool : ∀ I ∈ primePool rayM H 2 (Z^(extSlot w 0 x)), I ≠ 0 := by
    intro I hI h0
    have hp := (Finset.mem_filter.mp hI).2.1
    rw [h0] at hp
    exact hp.ne_zero rfl
  have hP : 0 < Z^(extSlot w 0 x) := Real.rpow_pos_of_pos (zero_lt_one.trans_le st.base_ge_one) _
  rw [state_slot_norm_eq st (naturalRow st.character z hz0) _ hpool _ W _ _ _ t hP, hpunct]

/-- **Pointwise inputs of a HIGH row.** -/
theorem high_row_pointwise {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ Mcap Lplain τ ε₁ e kap v d : ℝ) (hbΦ : 0 ≤ bΦ) (hL : 0 ≤ Lplain)
    (hτ : 0 < τ) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap)
    (hkap' : kap ≤ 1) (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hslot : 8*e*(1/d)+kap ≤ ε₁) (hplain : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁) :
    ∃ K : ℝ, 0 < K ∧ ∃ Cs : ℝ, 1 ≤ Cs ∧ ∃ S₀ : Finset (ℕ×ℕ), ∀ η₀ : Character,
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.puncture = 1 → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (b : ℝ) (i : ℕ),
      51/100 ≤ b → b ≤ 1 →
    ∀ z : O, ∀ hz : st.radial.keep z,
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz
        (3*(i+1 : ℕ)*Z^τ) < b + 2*e →
    ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ) (t height : ℝ),
      (∀ k, 0 ≤ w k) → (∀ k, w k ≤ 1) → (∀ k, (33/50:ℝ) ≤ σ k) → (∀ k, σ k ≤ 33/50) →
      0 ≤ height → (∀ k, |v' k| ≤ height) →
      |t| + height + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
          (fun k => primePool rayM H 2 (Z^(w k)))
          (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
          (fun k => Z^(w k)) t X₁ X₂‖^2 ≤
        K * (p.control S₀)^2 * Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
          ∏ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t z x ∧
      ∀ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t z x ≤
        Cs * Z^(2*ε₁*d) * Z^((2*b-1)*extSlot w 0 x) := by
  obtain ⟨K, hK, S₀, hrs⟩ := high_row_split rayM H hH bΦ Mcap Lplain τ ε₁ e kap v d hbΦ hL hτ
    hε₁ he he' hkap hkap' hv hd hdsupply hplain
  obtain ⟨Cs, hCs, hsl⟩ := actual_high_slots rayM H hH W 1 2 one_pos hWs hW (1/d) d τ ε₁ e kap v
    (33/50) (33/50) bΦ Mcap 0 1 d (by positivity) hd.le hτ hε₁ he he' hkap hv hslot hbΦ one_pos hd
    (by linarith) le_rfl
  refine ⟨K, hK, max Cs 1, le_max_right _ _, S₀, ?_⟩
  intro η₀
  filter_upwards [hrs η₀, hsl η₀] with Z hZ hZs
  refine ⟨hZ.1, ?_⟩
  intro st hpunct hwidth hQM hQη b i hb hb1 z hz hp hupper T θ w σ v' t height hw0 hw1 hσ hσ' hh0
    hv' hwin hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZτ0 : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hwinP : |t| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
    linarith
  refine ⟨?_, ?_⟩
  · have hrow := hZ.2 st hpunct hwidth hQM hQη b i hb hb1 z hz hp hupper (ι := T)
      (fun k => primePool rayM H 2 (Z^(w k)))
      (fun k I => idealCoeff (relativeCharacter rayM H hH η₀ (θ k)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w k)) (σ k) (v' k) I)
      (fun k => Z^(w k)) t (fun k => Real.rpow_pos_of_pos hZ0 _) hwinP hgate p X₁ X₂ hX₁ hX₂
      hl₁ hl₂
    rw [prod_slot_eq rayM H hH st η₀ W T θ w σ v' t z] at hrow
    exact hrow
  · intro x hx
    set k : T := ⟨x, hx⟩ with hk
    have hlow : LowBranch.ActualLow rayM H hH st η₀ hQM hQη b e (3*(i+1 : ℕ)*Z^τ) z := by
      apply whole_source_upper_actual_low rayM H hH st η₀ hQM hQη z hz _ _ _ hp
      change Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz _ < _
      exact hupper
    have hfreq : |t + extSlot v' 0 x| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ := by
      rw [extSlot_mem v' 0 hx]
      have := abs_add_le t (v' k)
      have := hv' k
      linarith
    have hheight : (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^v := by
      have h3 : (1:ℝ) ≤ 3+(3*i+2 : ℕ)*Z^τ := by
        have : (0:ℝ) ≤ ((3*i+2 : ℕ) : ℝ) := by positivity
        nlinarith
      exact le_trans (pow_le_pow_right₀ h3 (by norm_num)) hgate
    have hb' := hZs.2 st hwidth hQM hQη b i hb hb1 (extSlot w 0 x) (extSlot σ (33/50) x) t
      (extSlot v' 0 x) (by rw [extSlot_mem w 0 hx]; exact hw0 k)
      (by rw [extSlot_mem w 0 hx]; exact div_le_div_of_nonneg_right (hw1 k) hd.le)
      (by rw [extSlot_mem σ _ hx]; exact hσ k) (by rw [extSlot_mem σ _ hx]; exact hσ' k)
      hfreq hheight z hz hlow (extSlot θ 1 x)
    unfold slotNs
    refine hb'.trans ?_
    have hZe : 0 ≤ Z^(2*ε₁*d) := Real.rpow_nonneg hZ0.le _
    have hZe' : 0 ≤ Z^((2*b-1)*extSlot w 0 x) := Real.rpow_nonneg hZ0.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hZe) hZe'

end
end
end Qrh.TwoSlot.AnchorZeroLoss.High
