/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowReflected.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent

namespace OAI

namespace SevenEighths.ProbeLowReflected

open InverseTerminalWidths

theorem bound_perturbed_reflected_exponent
    (t d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (_ht : 0 ≤ t) (hd : 0 ≤ d) (_hdmax : d ≤ 1 / 6 + t)
    (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀)
    (hH : H ≤ (5 / 6 - t - 2 * d) - O₀ + ε)
    (hA : 2 * A₀ ≤ O₀ + ε)
    (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hell : ell₀ ≤ 1 / 6 + t - d + ε)
    (hz : za ≤ ell₀ + ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el)
    (hθ : |θ| ≤ ε)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀ + ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
        (2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀) ≤
      5 / 6 - t - 2 * d + max 0 ((d - 1 / 6 + 5 * t) / 4) + 40 * ε := by
  let dualWidth := 2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀
  have hθLower : -ε ≤ θ := (abs_le.mp hθ).1
  have hθUpper : θ ≤ ε := (abs_le.mp hθ).2
  have hdualWidth : dualWidth ≤ H - 3 * d + 6 * ε := by
    dsimp [dualWidth]
    linarith
  have hcolumn : v + ell ≤ H + 10 * ε := by
    dsimp [dualWidth] at hdualWidth
    linarith
  have hmax : max H (v + ell) ≤ H + 10 * ε :=
    max_le (by linarith) hcolumn
  have hpositivePart :
      0 ≤ max 0 ((d - 1 / 6 + 5 * t) / 4) := le_max_left _ _
  have hpositivePartUpper :
      (d - 1 / 6 + 5 * t) / 4 ≤
        max 0 ((d - 1 / 6 + 5 * t) / 4) := le_max_right _ _
  by_cases hmode : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hmode]
    change O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - za - ell -
      2 * el / 3 - max 0 (dualWidth - v - 3 * ell - el) / 2 ≤ _
    have hkernel : 0 ≤ max 0 (dualWidth - v - 3 * ell - el) :=
      le_max_left _ _
    linarith
  · have hhalf := hybrid_half_with_error hv hε hmode
    have hquarter := retained_kernel_quarter dualWidth (v + 3 * ell + el)
    have hcharge : dualWidth / 4 - 17 * ε / 12 ≤
        hybridSaving v za + ell + 2 * el / 3 +
          max 0 (dualWidth - v - 3 * ell - el) / 2 := by
      have heq : dualWidth - (v + 3 * ell + el) =
          dualWidth - v - 3 * ell - el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el dualWidth ≤
        O₀ / 2 + H - S₀ - B₀ + za - dualWidth / 4 +
          (10 + 17 / 12) * ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el dualWidth ≤ _
    apply hbound.trans
    dsimp [dualWidth]
    linarith

end SevenEighths.ProbeLowReflected

end OAI
