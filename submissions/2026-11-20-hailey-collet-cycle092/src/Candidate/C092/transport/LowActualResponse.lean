/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact calibration of original normalized slot responses, including zero widths. -/
import Candidate.C092.transport.WholeSlotP3
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentSlotNormalization CenteredMomentWholeSlotDeletion
open QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

/-- The response is measured on the original slot, before a radius is selected.
Zero width is handled by its separate amplitude bound, never by division. -/
def slotResponse (U pay width amplitude : ℝ) : ℝ :=
  Real.logb U (amplitude/pay)/width

/-- Include zero in the finite maximum, also when there are no marked slots. -/
def response {Slot : Type*} [Fintype Slot] (U pay : ℝ) (w amplitude : Slot → ℝ) : ℝ :=
  Finset.univ.sup' ⟨none,Finset.mem_univ _⟩
    (fun i : Option Slot => i.elim 0 (fun j => slotResponse U pay (w j) (amplitude j)))

theorem response_nonneg {Slot : Type*} [Fintype Slot]
    (U pay : ℝ) (w amplitude : Slot → ℝ) : 0 ≤ response U pay w amplitude := by
  exact Finset.le_sup' (fun i : Option Slot => i.elim 0 (fun j => slotResponse U pay (w j) (amplitude j))) (Finset.mem_univ none)

theorem response_le_iff {Slot : Type*} [Fintype Slot]
    (U pay : ℝ) (w amplitude : Slot → ℝ) (e : ℝ) :
    response U pay w amplitude ≤ e ↔
      0 ≤ e ∧ ∀ i, slotResponse U pay (w i) (amplitude i) ≤ e := by
  constructor
  · intro h
    refine ⟨(response_nonneg U pay w amplitude).trans h,?_⟩
    intro i
    exact (Finset.le_sup' _ (Finset.mem_univ (some i : Option Slot))).trans h
  · rintro ⟨he,hi⟩
    apply Finset.sup'_le
    rintro (_|i) _
    · exact he
    · exact hi i

theorem slotResponse_le_iff {U pay width amplitude e : ℝ}
    (hU : 1 < U) (hp : 0 < pay) (hw : 0 < width)
    (ha : 0 ≤ amplitude) (he : 0 ≤ e) :
    slotResponse U pay width amplitude ≤ e ↔ amplitude ≤ pay*U^(e*width) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [slotResponse,he,mul_nonneg hp.le (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _).le]
  · unfold slotResponse
    rw [div_le_iff₀ hw,Real.logb_le_iff_le_rpow hU (div_pos ha hp)]
    exact div_le_iff₀ hp |>.trans (by rw [mul_comm])

/-- The exact finite response cutoff is equivalent to the real normalized
slot inequalities. Zero-width bounds remain explicit and are supplied by
all-scale regular-row slot bounds. -/
theorem response_le_iff_amplitudes {Slot : Type*} [Fintype Slot]
    {U pay e : ℝ} (w amplitude : Slot → ℝ)
    (hU : 1 < U) (hp : 0 < pay) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ amplitude i) (hz : ∀ i, w i = 0 → amplitude i ≤ pay)
    (he : 0 ≤ e) :
    response U pay w amplitude ≤ e ↔ ∀ i, amplitude i ≤ pay*U^(e*w i) := by
  rw [response_le_iff]
  simp only [he,true_and]
  apply forall_congr'
  intro i
  rcases (hw i).eq_or_lt with h | h
  · have hwi : w i = 0 := h.symm
    simp [slotResponse,hwi,hz i hwi,he]
  · exact slotResponse_le_iff hU hp h (ha i) he

def originalResponse {Slot : Type*} [Fintype Slot]
    (η : Character) (m A : O) (t U pay : ℝ) (w : Slot → ℝ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ)
    (P : Slot → ℝ) (z : O) : ℝ :=
  response U pay w (fun i => ‖normalizedSlot η m A z (pool i) (coeff i) t (P i)‖^2)

/-- Genuine regular row-response classes, on the same mask and original data
as `LowRows`; no zero-maximum band is substituted for measured response. -/
theorem originalResponse_le_iff {Slot : Type*} [Fintype Slot]
    (η : Character) (m A : O) (t U pay e : ℝ) (w : Slot → ℝ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ)
    (P : Slot → ℝ) (z : O)
    (hU : 1 < U) (hp : 0 < pay) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, w i = 0 → ‖normalizedSlot η m A z (pool i) (coeff i) t (P i)‖^2 ≤ pay)
    (he : 0 ≤ e) :
    originalResponse η m A t U pay w pool coeff P z ≤ e ↔
      LowRows Finset.univ η m A t U e pay w pool coeff P z := by
  rw [originalResponse,response_le_iff_amplitudes w _ hU hp hw (fun _ => sq_nonneg _) hz he]
  simp [LowRows]

/-- A genuine supplied upper exponent bounds the measured response and
provides every zero-width bound at once. -/
theorem originalResponse_bounded {Slot : Type*} [Fintype Slot]
    (η : Character) (m A : O) (t U pay ν : ℝ) (w : Slot → ℝ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ)
    (P : Slot → ℝ) (z : O)
    (hU : 1 < U) (hp : 0 < pay) (hw : ∀ i, 0 ≤ w i) (hν : 0 ≤ ν)
    (hslot : ∀ i, ‖normalizedSlot η m A z (pool i) (coeff i) t (P i)‖^2 ≤ pay*U^(ν*w i)) :
    0 ≤ originalResponse η m A t U pay w pool coeff P z ∧
      originalResponse η m A t U pay w pool coeff P z ≤ ν := by
  refine ⟨response_nonneg _ _ _ _,?_⟩
  have hz : ∀ i, w i = 0 → ‖normalizedSlot η m A z (pool i) (coeff i) t (P i)‖^2 ≤ pay := by
    intro i hi
    simpa [hi] using hslot i
  exact (originalResponse_le_iff η m A t U pay ν w pool coeff P z hU hp hw hz hν).2
    (by simpa [LowRows] using hslot)

end
end QRH.Cycle092.LowActual
