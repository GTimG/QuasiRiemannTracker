/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `masked_natural_slot_eq` (`Record12518109Natural/SlotMaximumTransport.lean`,
Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafContract
import Submissions.hailey_collet_1252270103.Record12518109Natural.SlotMaximumTransport

/-!
# High.LeafSlots

The slot dictionary of the HIGH leaf.

The packed energy of `HighBranchMesh` carries the slots
`normalizedSlot st.character st.mask 1 z (primePool (Z^w)) (fun I => θ I * annularWeight W (Z^w) σ v I) t (Z^w)`.
HC's raw/core slot comparison (`eventually_whole_original_raw_max_comparison`) is stated for
`naturalSlot (excluded (naturalRow η z).character R) (primePool (Z^w)) (fun I => θ I * annularWeight W (Z^w) σ (t+v) I) (Z^w)`,
where the row height `t` is moved into the annular weight.

The two slots differ by the constant phase `(Z^w)^(-it)`, so they have the same norm:
* `annularWeight_shift` — the weight at `t + v` is the weight at `v` times `N(I)^(it)` times
  `(P⁻¹)^(it)`;
* `naturalSlot_height_shift` — the same identity for the whole slot;
* `normalizedSlot_norm_eq` / `state_slot_norm_eq` — the norm identity.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion CenteredMomentEnergyState
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem absNorm_pos_of_ne {I : Ideal O} (hI : I ≠ 0) : (0 : ℝ) < (I.absNorm : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- The annular weight at height `t + v`. -/
theorem annularWeight_shift (W : ℝ → ℂ) (P σ v t : ℝ) (hP : 0 < P) (I : Ideal O) (hI : I ≠ 0) :
    HeckePrimeAnnular.annularWeight W P σ (t + v) I =
      (((P⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) *
        (HeckePrimeAnnular.annularWeight W P σ v I * (I.absNorm : ℂ) ^ (Complex.I * t)) := by
  have hN := absNorm_pos_of_ne hI
  have hne : ((((I.absNorm : ℝ) / P : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (div_pos hN hP).ne'
  have hexp : -HeckeDyadic.shift σ (t + v) = -HeckeDyadic.shift σ v + (t : ℂ) * Complex.I := by
    unfold HeckeDyadic.shift; push_cast; ring
  have hX : ((((I.absNorm : ℝ) / P : ℝ)) : ℂ) ^ ((t : ℂ) * Complex.I) =
      (((P⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) * (I.absNorm : ℂ) ^ (Complex.I * t) := by
    rw [div_eq_mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hN.le (inv_nonneg.mpr hP.le), mul_comm,
      mul_comm Complex.I (t : ℂ), Complex.ofReal_natCast]
  unfold HeckePrimeAnnular.annularWeight
  rw [hexp, Complex.cpow_add _ _ hne, hX]
  ring

/-- The phase has norm one. -/
theorem phase_norm (P t : ℝ) (hP : 0 < P) : ‖(((P⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hP)]
  simp

/-- The whole slot at height `t + v` is the height-twisted slot at `v`, up to the phase. -/
theorem naturalSlot_height_shift (χ : Character) (pool : Finset (Ideal O))
    (hpool : ∀ I ∈ pool, I ≠ 0) (ν : Ideal O → ℂ) (W : ℝ → ℂ) (P σ v t : ℝ) (hP : 0 < P) :
    naturalSlot χ pool (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ (t + v) I) P =
      (((P⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) *
        naturalSlot χ pool
          (heightCoefficient (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ v I) t) P := by
  unfold naturalSlot
  have hs : (∑ I ∈ pool, idealCoeff χ I * (ν I * HeckePrimeAnnular.annularWeight W P σ (t + v) I)) =
      (((P⁻¹ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) * ∑ I ∈ pool, idealCoeff χ I *
        heightCoefficient (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ v I) t I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    rw [annularWeight_shift W P σ v t hP I (hpool I hI)]
    unfold heightCoefficient
    ring
  rw [hs]
  ring

/-- **Slot dictionary.** The normalized slot of the packed row and HC's raw natural slot (row
height moved into the annular weight) have the same norm. -/
theorem normalizedSlot_norm_eq {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O)
    (hR : R ≠ 0) (pool : Finset (Ideal O)) (hpool : ∀ I ∈ pool, I ≠ 0) (ν : Ideal O → ℂ)
    (W : ℝ → ℂ) (P σ v t : ℝ) (hP : 0 < P) :
    ‖normalizedSlot η (fixedBadMask * idealGenerator R) 1 z pool
        (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ v I) t P‖ =
      ‖naturalSlot (excluded F.character R) pool
        (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ (t + v) I) P‖ := by
  rw [Record12518109Natural.WeightedHigh.masked_natural_slot_eq F R hR,
    naturalSlot_height_shift _ pool hpool ν W P σ v t hP, norm_mul, phase_norm P t hP, one_mul]

/-- The state form (`st.mask = fixedBadMask * idealGenerator st.puncture`). -/
theorem state_slot_norm_eq {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) {z : O}
    (F : NaturalRow st.character z) (pool : Finset (Ideal O)) (hpool : ∀ I ∈ pool, I ≠ 0)
    (ν : Ideal O → ℂ) (W : ℝ → ℂ) (P σ v t : ℝ) (hP : 0 < P) :
    ‖normalizedSlot st.character st.mask 1 z pool
        (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ v I) t P‖ =
      ‖naturalSlot (excluded F.character st.puncture) pool
        (fun I => ν I * HeckePrimeAnnular.annularWeight W P σ (t + v) I) P‖ := by
  rw [NaturalState.mask]
  exact normalizedSlot_norm_eq F st.puncture st.puncture_ne_zero pool hpool ν W P σ v t hP

end
end Qrh.TwoSlot.AnchorZeroLoss.High
