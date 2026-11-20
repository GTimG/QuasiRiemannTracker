/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Quantitative absorption of the actual all-length contour floor at tiny radii. -/
import Candidate.C092.transport.TinyCoreFloor

set_option autoImplicit false
namespace QRH.Cycle092.TinyCore
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

/-- A coarse genuine upper bound on the original absolute marked width. -/
theorem original_width_cap {n y : ℝ} (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY)
    (hn : y ≤ n) : sourceWidth n y-(u : ℝ) ≤ 141/1000 := by
  have hg := sourceGain_le_cent hy0 hy1
  unfold sourceWidth
  norm_num [sourceY0,u] at hy0 ⊢
  linarith

/-- The pointwise contour floor is paid through V=.14 with a fixed modulus
allowance 5q=.0005 and the true finite-slot buffer charge<=.001. -/
theorem tiny_floor_paid {V e width buffer : ℝ} {K : ℕ}
    (hV0 : 0 ≤ V) (hV1 : V ≤ 7/50) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hw0 : 0 ≤ width) (hw1 : width ≤ 141/1000)
    (hbuffer : buffer*(K : ℝ) ≤ 1/1000) :
    5*V+5*(1/10000 : ℝ)+buffer*(K : ℝ)+e*width ≤
      V+(u : ℝ)-(rho : ℝ)/4+(5/6)*max 0 ((H : ℝ)-V) := by
  have hew := mul_le_mul_of_nonneg_right he1 hw0
  have hVH : 0 ≤ (H : ℝ)-V := by norm_num [H,u] at *; linarith only [hV1]
  rw [max_eq_right hVH]
  norm_num [H,u,rho] at *
  linarith

/-- No mesh premise is needed when every original slot is erased. Its
positive buffer is chosen after the finite slot count and before row data. -/
theorem tiny_slot_buffer (K : ℕ) :
    ∃ buffer : ℝ, 0 < buffer ∧ buffer*(K : ℝ) ≤ 1/1000 := by
  let b : ℝ := 1/(1000*(1+(K : ℝ)))
  have hb : 0 < b := by dsimp [b]; positivity
  have heq : b*(1000*(1+(K : ℝ))) = 1 := by dsimp [b]; field_simp
  exact ⟨b,hb,by nlinarith only [heq,hb]⟩

end
end QRH.Cycle092.TinyCore
