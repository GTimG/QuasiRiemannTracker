/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite source anchors and repeated descriptor banks, chosen before the scale. -/
import Candidate.C092.transport.MediumInversePriceGuards
import Candidate.C092.transport.MediumInversePriceShort

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open QRH.Cycle092.Source QRH.SourceCertificate QRH.ContactContinuation

/-- A single finite anchor grid works for every actual length in the given
closed interval. Every anchor stays within two grid steps of that interval. -/
theorem finite_anchor_grid {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ J : ℕ, (∀ j ∈ Finset.range J,
      a ≤ a+((j : ℝ)+2)*δ ∧ a+((j : ℝ)+2)*δ ≤ b+2*δ) ∧
      ∀ r : ℝ, a ≤ r → r ≤ b →
        ∃ k ∈ Finset.range J,
          r+δ ≤ a+((k : ℝ)+2)*δ ∧ a+((k : ℝ)+2)*δ ≤ r+2*δ := by
  let J := ⌊(b-a)/δ⌋₊+1
  refine ⟨J,?_,?_⟩
  · intro j hj
    have hj' : j ≤ ⌊(b-a)/δ⌋₊ := by
      simpa only [J,Finset.mem_range,Nat.lt_add_one_iff] using hj
    have hfloor := Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hδ.le)
    have hjreal : (j : ℝ) ≤ (⌊(b-a)/δ⌋₊ : ℝ) := Nat.cast_le.mpr hj'
    have hjδ : (j : ℝ)*δ ≤ b-a :=
      (mul_le_mul_of_nonneg_right hjreal hδ.le).trans ((le_div_iff₀ hδ).mp hfloor)
    exact ⟨by nlinarith [mul_nonneg (show (0 : ℝ) ≤ (j : ℝ)+2 by positivity) hδ.le],by nlinarith⟩
  · intro r har hrb
    let k := ⌊(r-a)/δ⌋₊
    have hkJ : k ∈ Finset.range J := by
      apply Finset.mem_range.mpr
      dsimp [J,k]
      exact Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right (by linarith : r-a ≤ b-a) hδ.le))
    have hklo := Nat.floor_le (div_nonneg (sub_nonneg.mpr har) hδ.le)
    have hkhi := Nat.lt_floor_add_one ((r-a)/δ)
    have hlo : (k : ℝ)*δ ≤ r-a := (le_div_iff₀ hδ).mp hklo
    have hhi : r-a < ((k : ℝ)+1)*δ := (div_lt_iff₀ hδ).mp hkhi
    exact ⟨k,hkJ,by nlinarith,by nlinarith⟩

/-- An attaining descriptor has width at least a fixed positive b. Therefore
the early repetition bank supplies the administrative quota and contains an
inward-rounded repeat selection for every later quota up to 7/37. -/
theorem finite_repeat_selection {b w P mesh : ℝ}
    (hb : 0 < b) (hbw : b ≤ w) (hwm : w ≤ mesh)
    (hP : 0 ≤ P) (hPmax : P ≤ 7/37) :
    let Kbig := ⌈(7/37 : ℝ)/b⌉₊+1
    (7/37 : ℝ) ≤ (Kbig : ℝ)*w ∧
    ∃ selected : Finset (Fin Kbig),
      (selected.card : ℝ)*w ≤ P ∧ P-mesh < (selected.card : ℝ)*w := by
  dsimp only
  let Kbig := ⌈(7/37 : ℝ)/b⌉₊+1
  have hw : 0 < w := hb.trans_le hbw
  have hceil := Nat.le_ceil ((7/37 : ℝ)/b)
  have hKb : (7/37 : ℝ) ≤ (Kbig : ℝ)*b := by
    have h := (div_le_iff₀ hb).mp hceil
    dsimp [Kbig]
    push_cast
    nlinarith
  refine ⟨hKb.trans (mul_le_mul_of_nonneg_left hbw (Nat.cast_nonneg _)),?_⟩
  obtain ⟨k,hk,hkP,hPk⟩ := repeat_count_rounding hP hPmax hb hbw
  have hkK : k ≤ Kbig := hk.trans ((Nat.floor_le_ceil ((7/37 : ℝ)/b)).trans (Nat.le_succ _))
  obtain ⟨selected,_,hcard⟩ := Finset.exists_subset_card_eq
    (show k ≤ (Finset.univ : Finset (Fin Kbig)).card by simpa using hkK)
  refine ⟨selected,?_,?_⟩
  · simpa only [hcard] using hkP
  · rw [hcard]
    linarith

/-- Close to the 7/9 seam the native quota loses at most one open-grid
step, so no ideal source at or above its strict upper endpoint is needed. -/
theorem native_collar_quota {r δ : ℝ} (hδ : 0 ≤ δ)
    (hr : 3/4 ≤ r) (hrtop : r ≤ 7/9) (hcollar : 7/9-3*δ ≤ r) :
    inverseQuota r-δ ≤ (1-r)/2 := by
  by_cases hrt : r < 7/9
  · have hq : inverseQuota r=curvedQuota r := by
      simp [inverseQuota,not_lt.mpr hr,not_le.mpr hrt]
    have hd := radical_increment_le hr hrtop (by norm_num : (7/9 : ℝ) ≤ 7/9)
    have hs := inverse_native_seam
    change radical (7/9)-radical r ≤ 7/9-r at hd
    unfold curvedQuota at hs
    change (1-(7/9 : ℝ))/2+11/16*(7/9)-7/24-radical (7/9)=(1-(7/9 : ℝ))/2 at hs
    rw [hq]
    change (1-r)/2+11/16*r-7/24-radical r-δ ≤ (1-r)/2
    nlinarith
  · rw [inverseQuota_native (le_of_not_gt hrt)]
    linarith

theorem near_native_quota {r δ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hcollar : 7/9-3*δ ≤ r) : inverseQuota r-δ ≤ (1-r)/2 := by
  by_cases hr : r ≤ 7/9
  · exact native_collar_quota hδ (by linarith) hr hcollar
  · rw [inverseQuota_native (lt_of_not_ge hr).le]
    linarith

/-- The last finite collar uses no marks: its entire missing inverse quota
is within the same prescribed open-decrement budget. -/
theorem top_unmarked_quota {r δ ζ : ℝ} (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/1000)
    (hcollar : 1-3*δ ≤ r) (hζ : 3*δ ≤ ζ) : inverseQuota r-ζ ≤ 0 := by
  rw [inverseQuota_native (by linarith)]
  linarith

/-- Every actual inverse quota in the checked range is below the fixed
7/37 physical-source supply cap, including the curved arm. -/
theorem inverse_quota_supply_cap {r : ℝ} (hr : 367/500 ≤ r) :
    inverseQuota r ≤ 3/16 ∧ (3/16 : ℝ) < 7/37 := by
  refine ⟨?_,by norm_num⟩
  unfold inverseQuota
  split_ifs with hlo hhi
  · linarith
  · linarith
  · have hrlo : (3/4 : ℝ) ≤ r := le_of_not_gt hlo
    have hrsub : 0 ≤ r-2/3 := by linarith
    have hrad : (1/6 : ℝ) ≤ radical r := by
      apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1/6)
        (by unfold radical;positivity) (by decide : (5 : ℕ) ≠ 0)).mp
      rw [radical_pow (by linarith)]
      calc
        (1/6 : ℝ)^5 ≤ (5/16 : ℝ)^5*7*(3/4 : ℝ)^4*(1/12 : ℝ) := by norm_num
        _ ≤ (5/16 : ℝ)^5*7*r^4*(r-2/3) := by gcongr <;> linarith
    change (1-r)/2+11/16*r-7/24-radical r ≤ 3/16
    linarith

/-- Applying an early genuine source bank to an actual attaining width
needs only an inward-rounded finite selection. It loses one descriptor mesh
in addition to the already paid open-anchor loss. -/
theorem admitted_inverse_repeat_selection
    {ρ : Qrh.MarkedAnchor.Interface.Contract.AnchorRect} {r ζ b w mesh : ℝ}
    (hr : 367/500 ≤ r) (hζ : 0 ≤ ζ)
    (ha : ρ.Admissible r (inverseQuota r-ζ) 1)
    (hb : 0 < b) (hbw : b ≤ w) (hwm : w ≤ mesh) :
    let Kbig := ⌈(7/37 : ℝ)/b⌉₊+1
    (7/37 : ℝ) ≤ (Kbig : ℝ)*w ∧
    ∃ selected : Finset (Fin Kbig),
      ρ.Admissible r ((selected.card : ℝ)*w) 1 ∧
      inverseQuota r-(ζ+mesh) < (selected.card : ℝ)*w := by
  have hP : 0 ≤ inverseQuota r-ζ := ha.2.2.1
  have hcap : inverseQuota r-ζ ≤ 7/37 := by
    have hc := inverse_quota_supply_cap hr
    linarith
  obtain ⟨hSupply,selected,hle,hlt⟩ := finite_repeat_selection hb hbw hwm hP hcap
  refine ⟨hSupply,selected,?_,?_⟩
  · exact Qrh.MarkedAnchor.Interface.Contract.AnchorRect.admissible_downward ha ha.1 le_rfl (mul_nonneg (Nat.cast_nonneg _) (hb.trans_le hbw).le) hle
  · linarith

#print axioms finite_anchor_grid
#print axioms finite_repeat_selection
#print axioms native_collar_quota
end
end QRH.Cycle092.MediumInversePrice
