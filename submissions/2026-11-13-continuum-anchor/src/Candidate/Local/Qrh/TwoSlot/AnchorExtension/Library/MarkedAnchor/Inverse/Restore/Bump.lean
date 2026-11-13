/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Basic

/-!
# Inverse.Restore.Bump — smooth bumps times powers

The restored child slot bump is `W' x = -conj(W x) · x^{-1/2}` and the restored child column
profile is `Φ₂ x = Φ x · x^{-1/2}`. Both are smooth with the same support as the original
(compactly supported in `(0, ∞)`):

* `contDiff_mul_cpow`: `W` smooth with support in `[a, b]`, `0 < a` ⇒ `x ↦ W x · (x:ℂ)^s` smooth;
* `childBump W := fun x => -(star (W x)) * (x:ℂ)^(-(1/2))`, `childBump_contDiff`,
  `childBump_support`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped ContDiff
open Set Filter Topology

theorem contDiffAt_ofReal_cpow (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun y : ℝ => ((y : ℂ) ^ s)) x := by
  have hev : (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * s)) =ᶠ[𝓝 x]
      (fun y : ℝ => ((y : ℂ) ^ s)) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      ← Complex.ofReal_log hy.le]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev.symm
  have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log y) x := Real.contDiffAt_log.mpr hx.ne'
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ => ((Real.log y : ℂ) * s)) x :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp x hlog).mul contDiffAt_const
  exact Complex.contDiff_exp.contDiffAt.comp x h1

/-- A smooth function supported in `[a, b]` (`0 < a`) times `x^s` is smooth. -/
theorem contDiff_mul_cpow (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : ℝ => W x * ((x : ℂ) ^ s)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : 0 < x
  · exact hW.contDiffAt.mul (contDiffAt_ofReal_cpow s hx)
  · have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 x] (fun y : ℝ => W y * ((y : ℂ) ^ s)) := by
      filter_upwards [gt_mem_nhds (lt_of_le_of_lt (not_lt.mp hx) ha)] with y hy
      have hW0 : W y = 0 := by
        by_contra h
        exact absurd (hs h).1 (not_le.mpr hy)
      rw [hW0, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev.symm

/-- The restored child slot bump `W' x = -conj(W x) · x^{-1/2}`. -/
def childBump (W : ℝ → ℂ) : ℝ → ℂ := fun x => -(star (W x)) * ((x : ℂ) ^ (-(1/2 : ℂ)))

theorem childBump_contDiff (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) : ContDiff ℝ ∞ (childBump W) := by
  have hc : ContDiff ℝ ∞ (fun x => -(star (W x))) :=
    (Complex.conjCLE.toContinuousLinearMap.contDiff.comp hW).neg
  have hcs : Function.support (fun x => -(star (W x))) ⊆ Icc a b := by
    intro x hx
    apply hs
    intro h0
    apply hx
    simp [h0]
  exact contDiff_mul_cpow _ hc a b ha hcs _

theorem childBump_support (W : ℝ → ℂ) (a b : ℝ) (hs : Function.support W ⊆ Icc a b) :
    Function.support (childBump W) ⊆ Icc a b := by
  intro x hx
  apply hs
  intro h0
  apply hx
  simp [childBump, h0]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.childBump_contDiff
#print axioms Qrh.MarkedAnchor.Inverse.Restore.contDiff_mul_cpow
