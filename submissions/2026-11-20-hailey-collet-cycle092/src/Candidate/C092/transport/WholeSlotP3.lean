/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The exact P3 cancellation after genuine whole-slot retention. -/
import Candidate.C092.transport.WholeSlotUniform
import Candidate.C092.Source

set_option autoImplicit false
namespace QRH.Cycle092.WholeSlot
noncomputable section
open QRH.Cycle090 QRH.SourceCertificate

/-- The source application pays its real inward width decrement and the
single whole-slot rounding loss, with the exact checked P3 bracket. -/
theorem p3_capacity_difference (n y decrement mesh : ℝ) :
    sourceWidth n y-(u : ℝ)-(H : ℝ)*
      (sourceWidth (n/(H : ℝ)) (y/(H : ℝ))-decrement)+mesh =
      lowBracketAt y+(H : ℝ)*decrement+mesh := by
  have h := low_response_cancellation (n := n) (y := y) (u := (u : ℝ)) (H := (H : ℝ))
    (by norm_num [H,u]) H_real_bounds.1.ne'
  unfold lowBracketAt
  linarith

/-- Actual whole-slot rounding and the earlier strict-width decrement fit
inside half the positive source reserve, uniformly on the finite response band. -/
theorem p3_paid_with_rounding {n y e decrement mesh : ℝ}
    (he₀ : 0 ≤ e) (he₁ : e ≤ (responseUpper : ℝ))
    (hd : 0 ≤ decrement) (hm : 0 ≤ mesh)
    (hfee : 2*(responseUpper : ℝ)*((H : ℝ)*decrement+mesh) ≤ (rho : ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho : ℚ)) :
    e*max 0 (sourceWidth n y-(u : ℝ)-(H : ℝ)*
      (sourceWidth (n/(H : ℝ)) (y/(H : ℝ))-decrement)+mesh) <
      (u : ℝ)-(rho : ℝ)/2 := by
  rw [p3_capacity_difference]
  have hbuffer : 0 ≤ (H : ℝ)*decrement+mesh := add_nonneg (mul_nonneg H_real_bounds.1.le hd) hm
  have hmax : max 0 (lowBracketAt y+(H : ℝ)*decrement+mesh) ≤
      max 0 (lowBracketAt y)+(H : ℝ)*decrement+mesh := by
    apply max_le
    · linarith [le_max_left 0 (lowBracketAt y)]
    · linarith [le_max_right 0 (lowBracketAt y)]
  have hcost := mul_le_mul_of_nonneg_left hmax he₀
  have hresponse := mul_le_mul_of_nonneg_right he₁ hbuffer
  push_cast at hp
  nlinarith

/-- The width decrement and original slot mesh can be fixed positively before
all late row data, while staying strictly inside the earlier source width. -/
theorem p3_early_rounding {earlierWidth : ℝ} (hwidth : 0 < earlierWidth) :
    ∃ decrement mesh : ℝ, 0 < decrement ∧ decrement < earlierWidth ∧ 0 < mesh ∧
      2*(responseUpper : ℝ)*((H : ℝ)*decrement+mesh) ≤ (rho : ℝ) := by
  let fee : ℝ := (rho : ℝ)/(16*(responseUpper : ℝ))
  have hfee : 0 < fee := by norm_num [fee,rho,responseUpper]
  let decrement := min (earlierWidth/2) fee
  have hd : 0 < decrement := lt_min (by positivity) hfee
  have hdw : decrement < earlierWidth := (min_le_left _ _).trans_lt (by linarith)
  have hdf : decrement ≤ fee := min_le_right _ _
  have hHd : (H : ℝ)*decrement ≤ decrement := mul_le_of_le_one_left hd.le H_real_bounds.2.le
  refine ⟨decrement,fee,hd,hdw,hfee,?_⟩
  have hr : (0 : ℝ) < (responseUpper : ℝ) := by norm_num [responseUpper]
  have hbound := mul_le_mul_of_nonneg_left (show (H : ℝ)*decrement+fee ≤ 2*fee by linarith) (show 0 ≤ 2*(responseUpper : ℝ) by positivity)
  have hfeenum : 4*(responseUpper : ℝ)*fee ≤ (rho : ℝ) := by norm_num [fee,rho,responseUpper]
  nlinarith

/-- Keep the actual number of erased slots in the buffer charge. In the
exhaustion case it is zero, so both the constant and exponent charges vanish. -/
theorem payment_with_buffer {U : ℝ} (hU : 0 < U)
    (C buffer e erasedWidth V sourceError : ℝ) (erasedCount : ℕ) :
    ((C*U^buffer)^erasedCount*U^(e*erasedWidth))*U^(V*(1+sourceError)) =
      C^erasedCount*U^(V+V*sourceError+buffer*(erasedCount : ℝ)+e*erasedWidth) := by
  calc
    _ = C^erasedCount*(U^(buffer*(erasedCount : ℝ))*U^(e*erasedWidth)*U^(V*(1+sourceError))) := by
      rw [mul_pow,←Real.rpow_mul_natCast hU.le]
      ring
    _ = C^erasedCount*U^(buffer*(erasedCount : ℝ)+e*erasedWidth+V*(1+sourceError)) := by
      rw [←Real.rpow_add hU,←Real.rpow_add hU]
    _ = _ := by congr 2; ring

end
end QRH.Cycle092.WholeSlot
