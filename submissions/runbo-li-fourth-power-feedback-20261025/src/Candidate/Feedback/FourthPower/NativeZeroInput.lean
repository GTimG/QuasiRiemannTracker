/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Reuse the completed OpenAI zero-slot induction, not a crude floor estimate.
The dummy zero slot only instantiates the existing certificate interface.
The extraction pattern is also used by PR69 LocalMoment/PlainUnmarkedAdapter;
here the full moving-support, length and profile parameters are retained.
The beta >= 0.51 premise is the nontrivial branch of the final contradiction,
not an assumed moment or an assumed bound on beta.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.NativeZeroInput
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentEnergyCappedWidthInduction
open CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

/-- One scale threshold works for every moving natural state, every profile
and every positive pair of lengths within the stated polynomial enclosure. -/
theorem zero_input (a b radial Bmask L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Ideal O) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ×ℕ), ∀ η₀ : Character, Q ≤ η₀.modulus →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt Q a b radial Bmask L Mcap ε Z degree control C := by
  let κ : ℝ := max (3/4) (2*HeckeZeroSupremum.beta-1)
  have hκ : (3/4 : ℝ) ≤ κ := le_max_left _ _
  have hκβ : 2*HeckeZeroSupremum.beta-1 ≤ κ := le_max_right _ _
  have hc := CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Unit) Q ⊤ le_top (fun _ : ℝ => (0 : ℂ))
    1 2 a b radial Bmask L 0 0 Mcap κ ε
    (by norm_num) (by simp) (by fun_prop) (by norm_num)
    ha haUpper hb hrad hmask hMcap hκ hε hβ hκβ
  obtain ⟨degree,control,hbound⟩ := certified_terminal (α := Unit) Q ⊤ le_top
    (fun _ : ℝ => (0 : ℂ)) 2 a b radial Bmask L 0 0 Mcap κ ε
    hmask hMcap.le (by linarith) hε hc
  refine ⟨degree,control,?_⟩
  intro η₀ hQη
  have hi : internalQ Q η₀=Q := inf_eq_left.mpr hQη
  obtain ⟨C,Cp,hC,hCp,h⟩ := hbound η₀ Q le_rfl
    (by simpa only [hi] using NeZero.ne Q)
    (by simpa only [hi] using hQt) (by simpa only [hi] using hQ72)
  refine ⟨C,hC,h.mono ?_⟩
  intro Z hZ
  exact ⟨hZ.1,by simpa only [hi] using hZ.2.1⟩

end
end Candidate.Feedback.FourthPower.NativeZeroInput
