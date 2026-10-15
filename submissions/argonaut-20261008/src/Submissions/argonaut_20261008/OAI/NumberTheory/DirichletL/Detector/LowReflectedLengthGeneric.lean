import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent

/- The proof body below is adapted from the frozen public web return.
   Definitions and helper lemmas are imported from the genuine official
   LowReflectedExponent module. No definition or ideal is introduced here.
   The E<=1/5 restriction matches the previously frozen transport contract;
   the original web lemma does not need that restriction. -/

namespace OAI.SevenEighths.ProbeLowReflected
open InverseTerminalWidths

theorem compensated_reflected_exponent_with_total_length
    (E d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hE : 0≤E) (hE1 : E≤1/5) (hd : 0≤d) (_hdE : d≤E) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(1-E-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hell : ell₀≤E-d+ε) (hz : za≤ell₀+ε)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤
        (1-E-2*d)+max 0 (5*E-1+d)/4+40*ε := by
  let Td : ℝ :=
    2*H + 2*A₀ + 2*za - 1 - ell₀ -
      θ - N₀ - 3*B₀

  have hθlo : -ε ≤ θ := (abs_le.mp hθ).1
  have hθhi : θ ≤ ε := (abs_le.mp hθ).2
  have hA0 : 0 ≤ A₀ := hN.trans hNA

  /-
  This is the same terminal-width estimate as in the fixed-length proof.
  All dependence on `E` cancels through `M + E = 1`.
  -/
  have hTd : Td ≤ H - 3*d + 6*ε := by
    dsimp [Td]
    linarith

  have hret' :
      v + 3*ell + el ≤ Td + ε := by
    simpa [Td] using hret

  have hcol :
      v + ell ≤ H + 10*ε := by
    linarith

  have hmax :
      max H (v + ell) ≤ H + 10*ε :=
    max_le (by linarith) hcol

  have hk :
      0 ≤ max 0 (Td - v - 3*ell - el) :=
    le_max_left 0 (Td - v - 3*ell - el)

  have hq0 :
      0 ≤ max 0 (5*E - 1 + d) :=
    le_max_left 0 (5*E - 1 + d)

  have hqright :
      5*E - 1 + d ≤ max 0 (5*E - 1 + d) :=
    le_max_right 0 (5*E - 1 + d)

  change
    reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
      (1 - E) - 2*d +
        max 0 (5*E - 1 + d) / 4 +
        40*ε

  by_cases hu : hybridSaving v za = za

  · /-
    `za`-saving branch.

    The `za` terms cancel. The remaining losses are bounded using
    `hmax`, `hO`, the lower bounds on `ell` and `el`, and the
    nonnegativity of the retained kernel.
    -/
    unfold reflectedExponent
    rw [hu]
    change
      O₀/2 + max H (v + ell) - S₀ - B₀ +
          za - za - ell - 2*el/3 -
          max 0 (Td - v - 3*ell - el)/2 ≤
        (1 - E) - 2*d +
          max 0 (5*E - 1 + d)/4 +
          40*ε
    linarith

  · /-
    Non-`za` branch.

    The hybrid term plus the retained kernel controls `Td / 4`,
    with total local loss `17 ε / 12`.
    -/
    have hhalf :=
      hybrid_half_with_error hv hε hu

    have hquarter :=
      retained_kernel_quarter Td (v + 3*ell + el)

    have hcharge :
        Td/4 - 17*ε/12 ≤
          hybridSaving v za +
            ell +
            2*el/3 +
            max 0 (Td - v - 3*ell - el)/2 := by
      have heq :
          Td - (v + 3*ell + el) =
            Td - v - 3*ell - el := by
        ring
      rw [heq] at hquarter
      linarith

    have hbound :
        reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
          O₀/2 + H - S₀ - B₀ + za - Td/4 +
            (10 + 17/12)*ε := by
      unfold reflectedExponent
      linarith

    /-
    After expanding `Td`, the non-error part is bounded by

      3/4 + E/4 - 7*d/4.

    Relative to `(1-E)-2*d`, the exact excess is

      (5*E - 1 + d)/4,

    which is bounded by the requested max correction.
    -/
    have hcore :
        O₀/2 + H - S₀ - B₀ + za - Td/4 ≤
          (1 - E) - 2*d +
            max 0 (5*E - 1 + d)/4 +
            2*ε := by
      dsimp [Td]
      linarith

    calc
      reflectedExponent O₀ H S₀ B₀ za v ell el Td
          ≤ O₀/2 + H - S₀ - B₀ + za - Td/4 +
              (10 + 17/12)*ε :=
        hbound
      _ ≤
          (1 - E) - 2*d +
            max 0 (5*E - 1 + d)/4 +
            40*ε := by
        linarith

theorem compensated_reflected_exponent_with_length_generic
    (E d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hE : 0≤E) (hE1 : E≤1/5) (hd : 0≤d) (_hdE : d≤E) (hε : 0≤ε)
    (hO : -ε≤O₀) (hH : H≤(1-E-2*d)-O₀+ε)
    (hA : 2*A₀≤O₀+ε) (hN : 0≤N₀) (hNA : N₀≤A₀)
    (hS : 0≤S₀) (hB : 0≤B₀) (hell : ell₀≤E-d+ε) (hz : za≤ell₀+ε)
    (hv : -ε≤v) (hl : -ε≤ell) (he : -ε≤el) (hθ : |θ|≤ε)
    (hret : v+3*ell+el≤2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀)≤
        (1-E-2*d)+max 0 (5*E-1+d)/4+40*ε := by
  exact compensated_reflected_exponent_with_total_length E d ell₀ O₀ H A₀ N₀ S₀ B₀
    za v ell el θ ε hE hE1 hd _hdE hε hO hH hA hN hNA hS hB hell hz hv hl he hθ hret

end OAI.SevenEighths.ProbeLowReflected
