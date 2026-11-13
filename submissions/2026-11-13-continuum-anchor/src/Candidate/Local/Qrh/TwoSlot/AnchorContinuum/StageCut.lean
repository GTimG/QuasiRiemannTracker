/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Legal cuts and actual finite-stage output domination for strict source curves.
This does not yet discharge the padded physical HIGH gates. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.GainBounds
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.ChainData

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qrh.TwoSlot.AnchorContinuum.Curve
open Set Qrh.TwoSlot.AnchorExtension.ChainData

def cut (lam T gamma R : ℝ) : ℝ :=
  1/(2+6*(W lam T R-R*D lam T R+R*gamma))

/-- The differential reserve can also be bounded by a fixed harmless ceiling. -/
theorem uniform_reserve_small {lam T : ℝ} (hlam : lam < 1)
    (hT : 3/4 ≤ T) (hT1 : T < 7/9) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1/100 ∧ ∀ R ∈ Icc (3/4:ℝ) T,
      3*gamma ≤ D lam T R-flow R (W lam T R) := by
  obtain ⟨g,hg,hall⟩ := uniform_reserve hlam hT hT1
  refine ⟨min g (1/100),lt_min hg (by norm_num),min_le_right _ _,?_⟩
  intro R hR
  have h := hall R hR
  have hm := min_le_left g (1/100)
  linarith

/-- The chosen cut is in the actual physical stage's admitted cut interval. -/
theorem cut_bounds {lam T gamma R : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9) (hR : R ∈ Icc (3/4:ℝ) T)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1/100) :
    45457/125000 ≤ cut lam T gamma R ∧ cut lam T gamma R < 1/2 := by
  obtain ⟨hz,hz1⟩ := W_bounds hlam hlam1 hT hT1 hR
  obtain ⟨hd,hd1⟩ := D_bounds hlam hlam1 hT hT1 hR
  have hR0 : 0 ≤ R := by linarith [hR.1]
  have hR1 : R ≤ 7/9 := hR.2.trans hT1
  have hRD := mul_nonpos_of_nonneg_of_nonpos hR0 hd1
  have hRg := mul_pos (show 0 < R by linarith [hR.1]) hg
  have hden : 0 < 2+6*(W lam T R-R*D lam T R+R*gamma) := by linarith
  have hden2 : 2 < 2+6*(W lam T R-R*D lam T R+R*gamma) := by linarith
  have hDmax : -D lam T R ≤ 4/45 := by linarith
  have hpD := mul_le_mul_of_nonneg_left hDmax hR0
  have hpR := mul_le_mul_of_nonneg_right hR1 (show 0 ≤ (4/45:ℝ) by norm_num)
  have hpG := mul_le_mul hR1 hg1 hg.le (show 0 ≤ (7/9:ℝ) by norm_num)
  unfold cut
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith only [hz1,hpD,hpR,hpG]
  · rw [div_lt_iff₀ hden]
    linarith

/-- The actual stage output is the strict tangent chosen from the derivative. -/
theorem output_eq {lam T gamma R : ℝ} (hR : R ≠ 0) (r : ℝ) :
    fY R (W lam T R) (cut lam T gamma R) r =
      W lam T R+(D lam T R-gamma)*(r-R) := by
  unfold fY fu cut
  rw [one_div_one_div]
  field_simp [hR]
  <;> ring

/-- One common finite-step radius makes every actual source output dominate the
curve on its entire interval. The physical stage gates are a separate input. -/
theorem uniform_output_dominates (lam T : ℝ) (hT : 3/4 ≤ T) {gamma : ℝ} (hg : 0 < gamma) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ r R : ℝ, 3/4 ≤ r → r ≤ R → R ≤ T → R-r ≤ eta →
      ∀ x ∈ Icc r R, W lam T x ≤ fY R (W lam T R) (cut lam T gamma R) x := by
  obtain ⟨eta,heta,hall⟩ := uniform_finite_steps lam T hT hg
  refine ⟨eta,heta,?_⟩
  intro r R hr hrR hRT hlength x hx
  rw [output_eq (show R ≠ 0 by linarith)]
  exact hall r R hr hrR hRT hlength x hx

end Qrh.TwoSlot.AnchorContinuum.Curve
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.cut_bounds
#print axioms Qrh.TwoSlot.AnchorContinuum.Curve.uniform_output_dominates
