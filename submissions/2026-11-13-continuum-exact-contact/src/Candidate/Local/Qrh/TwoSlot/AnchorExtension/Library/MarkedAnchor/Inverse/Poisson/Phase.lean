/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Statement

/-!
# Inverse.Poisson.Phase — the phase identity

For the squarefree sextic row `χ_A = finiteSquarefreeRow P hg A` and the physical row
`y = f² g g' h` with `g = d g'` (`k₁ = g' h = (g/d) h`):
`χ_A(d) · conj χ_A(h) · χ_A(g)^4 · χ_A(f)^4 = conj χ_A(y)`, for EVERY column `A`
(no coprimality hypothesis: both sides vanish together off the coprime support).
The other orientation is the conjugate identity.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open OAI OAI.ActualEisensteinCubic

local notation "O" => ActualEisensteinCubic.O

section
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hgood : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (u : O) (n : ℕ) :
    finiteSquarefreeRow P hgood S (u ^ n) = finiteSquarefreeRow P hgood S u ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, finiteSquarefreeRow, map_one, Finset.prod_const_one]
  | succ n ih => rw [pow_succ, finiteSquarefreeRow_mul, ih, pow_succ]

theorem row_pow_ten (u : O) :
    finiteSquarefreeRow P hgood S u ^ 10 = finiteSquarefreeRow P hgood S u ^ 4 := by
  have h6 := finiteSquarefreeRow_sixth_power P hgood S u
  rw [row_pow] at h6
  by_cases hex : ∃ i ∈ S, u ∈ P i
  · rw [ite_eq_left hex] at h6
    have h0 : finiteSquarefreeRow P hgood S u = 0 := pow_eq_zero_iff (by norm_num) |>.mp h6
    rw [h0]; norm_num
  · rw [ite_eq_right hex] at h6
    calc finiteSquarefreeRow P hgood S u ^ 10
        = finiteSquarefreeRow P hgood S u ^ 6 * finiteSquarefreeRow P hgood S u ^ 4 := by ring
      _ = _ := by rw [h6, one_mul]

theorem row_star (u : O) :
    star (finiteSquarefreeRow P hgood S u) = finiteSquarefreeRow P hgood S u ^ 5 := by
  rw [finiteSquarefreeRow_conj_as_row_label]; ring

/-- The phase identity: `χ(d) conj χ(h) χ(g)^4 χ(f)^4 = conj χ(f² g g' h)` with `g = d g'`. -/
theorem phase_identity (f d g' h : O) :
    finiteSquarefreeRow P hgood S d * star (finiteSquarefreeRow P hgood S h) *
        finiteSquarefreeRow P hgood S (d * g') ^ 4 * finiteSquarefreeRow P hgood S f ^ 4 =
      star (finiteSquarefreeRow P hgood S (f ^ 2 * (d * g') * g' * h)) := by
  rw [row_star, row_star]
  simp only [finiteSquarefreeRow_mul, row_pow]
  have hf := row_pow_ten P hgood S f
  have hg := row_pow_ten P hgood S g'
  calc _ = finiteSquarefreeRow P hgood S d ^ 5 * finiteSquarefreeRow P hgood S h ^ 5 *
          finiteSquarefreeRow P hgood S g' ^ 4 * finiteSquarefreeRow P hgood S f ^ 4 := by ring
    _ = finiteSquarefreeRow P hgood S d ^ 5 * finiteSquarefreeRow P hgood S h ^ 5 *
          finiteSquarefreeRow P hgood S g' ^ 10 * finiteSquarefreeRow P hgood S f ^ 10 := by
        rw [hf, hg]
    _ = _ := by ring

/-- The conjugate orientation of the phase identity. -/
theorem phase_identity_conj (f d g' h : O) :
    star (finiteSquarefreeRow P hgood S d) * finiteSquarefreeRow P hgood S h *
        star (finiteSquarefreeRow P hgood S (d * g')) ^ 4 *
        star (finiteSquarefreeRow P hgood S f) ^ 4 =
      finiteSquarefreeRow P hgood S (f ^ 2 * (d * g') * g' * h) := by
  have h := congrArg star (phase_identity P hgood S f d g' h)
  simpa only [star_mul, star_pow, star_star, mul_comm, mul_left_comm, mul_assoc] using h

end

end
end Qrh.MarkedAnchor.Inverse.Poisson
