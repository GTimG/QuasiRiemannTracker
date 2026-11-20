/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Supremum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The analytic closing argument in Appendix Q.4

The analytic identity theorem turns an independently constructed analytic
continuation of a reciprocal signal into nonvanishing of its denominator.
The manuscript-specific Mellin continuation and its initial identity remain
explicit hypotheses.  In particular, this module does not assert the new
Dirichlet L-function zero-free region.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology
open MeasureTheory Asymptotics

namespace QRH.Cycle090

/-- The open complex half-plane used by the Mellin continuation in Q.4. -/
def rightHalfPlane (a : ℝ) : Set ℂ := {z | a < z.re}

/-- Complex right half-planes are preconnected, by real convexity. -/
theorem rightHalfPlane_isPreconnected (a : ℝ) :
    IsPreconnected (rightHalfPlane a) := by
  exact (convex_halfSpace_gt Complex.reLm.isLinear a).isPreconnected

/-- The continuation domain is open. -/
theorem rightHalfPlane_isOpen (a : ℝ) : IsOpen (rightHalfPlane a) := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Continue the cross-multiplied reciprocal identity from one neighborhood.
The input functions are analytic on the connected domain.  This avoids
presupposing that the denominator is nonzero on the continuation domain. -/
theorem continue_reciprocal_identity
    {U : Set ℂ} {F H L : ℂ → ℂ} {z₀ : ℂ}
    (hU : IsPreconnected U) (hz₀ : z₀ ∈ U)
    (hF : AnalyticOnNhd ℂ F U)
    (hH : AnalyticOnNhd ℂ H U)
    (hL : AnalyticOnNhd ℂ L U)
    (hidentity : H =ᶠ[𝓝 z₀] fun z => L z * F z) :
    EqOn H (fun z => L z * F z) U := by
  exact hH.eqOn_of_preconnected_of_eventuallyEq (hL.mul hF) hU hz₀ hidentity

/-- The continuation identity excludes denominator zeros where the numerator
does not vanish.  The analytic continuation is an explicit input. -/
theorem denominator_nonzero_of_continuation
    {U : Set ℂ} {F H L : ℂ → ℂ} {z₀ z : ℂ}
    (hU : IsPreconnected U) (hz₀ : z₀ ∈ U) (hz : z ∈ U)
    (hF : AnalyticOnNhd ℂ F U)
    (hH : AnalyticOnNhd ℂ H U)
    (hL : AnalyticOnNhd ℂ L U)
    (hidentity : H =ᶠ[𝓝 z₀] fun w => L w * F w)
    (hHnonzero : H z ≠ 0) : L z ≠ 0 := by
  have hid := continue_reciprocal_identity hU hz₀ hF hH hL hidentity hz
  intro hzero
  apply hHnonzero
  simpa only [hzero, zero_mul] using hid

/-- The `|H - 1| ≤ 1/2` estimate in Q.4 excludes zeros of `H`. -/
theorem numerator_nonzero_of_half_bound {w : ℂ}
    (hw : ‖w - 1‖ ≤ (1 / 2 : ℝ)) : w ≠ 0 := by
  intro hzero
  subst w
  norm_num at hw

/-- Combine the two estimates on the same physical probe in Q.4.
All functions have scalar real input and complex scalar output; the constants
and exponents are real.  This is a pointwise bound for `Z ≥ 1`. -/
theorem combine_probe_bounds
    (J f : ℝ → ℂ) {Z CJ CE t β k ω σ m : ℝ}
    (hZ : 1 ≤ Z) (hCJ : 0 ≤ CJ) (hCE : 0 ≤ CE)
    (hJ : ‖J Z‖ ≤ CJ * Z ^ (t - k + ω))
    (hE : ‖J Z - f Z‖ ≤ CE * Z ^ (β - k - σ))
    (hmain : t + ω ≤ β - m) (herror : m ≤ σ) :
    ‖f Z‖ ≤ (CJ + CE) * Z ^ (β - k - m) := by
  have hp₁ : Z ^ (t - k + ω) ≤ Z ^ (β - k - m) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hp₂ : Z ^ (β - k - σ) ≤ Z ^ (β - k - m) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have htri : ‖f Z‖ ≤ ‖J Z‖ + ‖J Z - f Z‖ := by
    calc
      ‖f Z‖ = ‖J Z - (J Z - f Z)‖ := by congr 1; ring
      _ ≤ ‖J Z‖ + ‖J Z - f Z‖ := norm_sub_le _ _
  calc
    ‖f Z‖ ≤ CJ * Z ^ (t - k + ω) + CE * Z ^ (β - k - σ) :=
      htri.trans (add_le_add hJ hE)
    _ ≤ CJ * Z ^ (β - k - m) + CE * Z ^ (β - k - m) :=
      add_le_add (mul_le_mul_of_nonneg_left hp₁ hCJ)
        (mul_le_mul_of_nonneg_left hp₂ hCE)
    _ = (CJ + CE) * Z ^ (β - k - m) := by ring

/-- The pointwise combination of Q.4 also gives the precise asymptotic input
needed by the Mellin theorem, with independent constants for the two bounds. -/
theorem combine_probe_isBigO
    (J f : ℝ → ℂ) {t β k ω σ m : ℝ}
    (hJ : J =O[atTop] (fun Z : ℝ => Z ^ (t - k + ω)))
    (hE : (fun Z => J Z - f Z) =O[atTop]
      (fun Z : ℝ => Z ^ (β - k - σ)))
    (hmain : t + ω ≤ β - m) (herror : m ≤ σ) :
    f =O[atTop] (fun Z : ℝ => Z ^ (β - k - m)) := by
  obtain ⟨CJ, hCJ, hJbound⟩ := isBigO_iff'.mp hJ
  obtain ⟨CE, hCE, hEbound⟩ := isBigO_iff'.mp hE
  apply IsBigO.of_bound (CJ + CE)
  filter_upwards [hJbound, hEbound, eventually_ge_atTop (1 : ℝ)] with Z hj he hZ
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hj' : ‖J Z‖ ≤ CJ * Z ^ (t - k + ω) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZ0 (t - k + ω))] using hj
  have he' : ‖J Z - f Z‖ ≤ CE * Z ^ (β - k - σ) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZ0 (β - k - σ))] using he
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ0 (β - k - m))] using
    combine_probe_bounds J f hZ hCJ.le hCE.le hj' he' hmain herror

/-- Q.4's signal Mellin integral converges absolutely in the improved
half-plane.  The locally integrable signal has the proved power bound at
infinity and arbitrary power decay at zero; these remain explicit inputs. -/
theorem mellin_signal_convergent
    (f : ℝ → ℂ) {β k m : ℝ}
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (fun Z : ℝ => Z ^ (β - k - m)))
    (hzero : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b)))
    {s : ℂ} (hs : s ∈ rightHalfPlane (β - m)) :
    MellinConvergent f ((k : ℂ) - s) := by
  have he : -(k + m - β) = β - k - m := by ring
  have htop' : f =O[atTop] (fun Z : ℝ => Z ^ (-(k + m - β))) := by
    simpa only [he] using htop
  apply mellinConvergent_of_isBigO_rpow hlocal htop'
    (b := k - s.re - 1)
  · change k - s.re < k + m - β
    change β - m < s.re at hs
    linarith
  · exact hzero (k - s.re - 1)
  · change k - s.re - 1 < k - s.re
    linarith

/-- Q.4's growth and decay hypotheses yield an analytic Mellin continuation.
Mathlib's `mellin f w` integrates `f(Z) Z^(w-1) dZ`, so the manuscript's
`∫ f(Z) Z^(k-s) dZ/Z` is `mellin f (k-s)`. -/
theorem mellin_signal_analytic
    (f : ℝ → ℂ) {β k m : ℝ}
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (fun Z : ℝ => Z ^ (β - k - m)))
    (hzero : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b))) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin f ((k : ℂ) - s))
      (rightHalfPlane (β - m)) := by
  apply DifferentiableOn.analyticOnNhd _ (rightHalfPlane_isOpen (β - m))
  intro s hs
  have he : -(k + m - β) = β - k - m := by ring
  have htop' : f =O[atTop] (fun Z : ℝ => Z ^ (-(k + m - β))) := by
    simpa only [he] using htop
  have hM : DifferentiableAt ℂ (mellin f) ((k : ℂ) - s) := by
    apply mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (b := k - s.re - 1)
    · change k - s.re < k + m - β
      change β - m < s.re at hs
      linarith
    · exact hzero (k - s.re - 1)
    · change k - s.re - 1 < k - s.re
      linarith
  have haff : DifferentiableAt ℂ (fun w : ℂ => (k : ℂ) - w) s := by fun_prop
  exact (hM.comp s haff).differentiableWithinAt

/-- Q.4's contradiction using an actual zero near the supremum, an analytic
continuation of the signal, and its initial reciprocal identity.  The
continuation hypotheses include the manuscript's substantial analytic work;
they are not derived from the finite arithmetic in this development. -/
theorem supremum_contradiction_from_continuation
    (L H F : ℂ → ℂ) (allowed : ℂ → Prop)
    (hne : (zeroRealParts L allowed).Nonempty)
    (hbdd : BddAbove (zeroRealParts L allowed))
    {β m a : ℝ} (hβ : β = sSup (zeroRealParts L allowed))
    (hm : 0 < m) (hma : m < β - a)
    (hF : AnalyticOnNhd ℂ F (rightHalfPlane (β - m)))
    (hH : AnalyticOnNhd ℂ H (rightHalfPlane (β - m)))
    (hL : AnalyticOnNhd ℂ L (rightHalfPlane (β - m)))
    (hnum : ∀ z : ℂ, a < z.re → H z ≠ 0)
    (hidentity : ∃ z₀ ∈ rightHalfPlane (β - m),
      H =ᶠ[𝓝 z₀] fun z => L z * F z) : False := by
  obtain ⟨z, _hzallowed, hz, hznear, _hzupper⟩ :=
    actual_zero_near_supremum L allowed hne hbdd hm
  rw [← hβ] at hznear
  obtain ⟨hzhalf, hznum⟩ := near_supremum_in_continuation hm hma hznear
  obtain ⟨z₀, hz₀, hid⟩ := hidentity
  have hnonzero : L z ≠ 0 :=
    denominator_nonzero_of_continuation (rightHalfPlane_isPreconnected (β - m))
      hz₀ hzhalf hF hH hL hid (hnum z hznum)
  exact hnonzero hz

/-- The final Q.4 contradiction with analyticity of the Mellin transform
derived from its two growth hypotheses, rather than assumed.  The identity
with the original L-function numerator is still an explicit hypothesis. -/
theorem supremum_contradiction_from_mellin
    (L H : ℂ → ℂ) (f : ℝ → ℂ) (allowed : ℂ → Prop)
    (hne : (zeroRealParts L allowed).Nonempty)
    (hbdd : BddAbove (zeroRealParts L allowed))
    {β k m a : ℝ} (hβ : β = sSup (zeroRealParts L allowed))
    (hm : 0 < m) (hma : m < β - a)
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (fun Z : ℝ => Z ^ (β - k - m)))
    (hzero : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b)))
    (hH : AnalyticOnNhd ℂ H (rightHalfPlane (β - m)))
    (hL : AnalyticOnNhd ℂ L (rightHalfPlane (β - m)))
    (hnum : ∀ z : ℂ, a < z.re → H z ≠ 0)
    (hidentity : ∃ z₀ ∈ rightHalfPlane (β - m),
      H =ᶠ[𝓝 z₀] fun z => L z * mellin f ((k : ℂ) - z)) : False := by
  exact supremum_contradiction_from_continuation L H
    (fun s : ℂ => mellin f ((k : ℂ) - s)) allowed hne hbdd hβ hm hma
    (mellin_signal_analytic f hlocal htop hzero) hH hL hnum hidentity

/-- A closing theorem for Q.4 whose analytic inputs are the two independent
physical-probe bounds, local integrability, zero-end decay, and the original
reciprocal identity.  Establishing these inputs for the manuscript's actual
probe and L-functions remains outside this partial formalization. -/
theorem supremum_contradiction_from_probe_bounds
    (L H : ℂ → ℂ) (J f : ℝ → ℂ) (allowed : ℂ → Prop)
    (hne : (zeroRealParts L allowed).Nonempty)
    (hbdd : BddAbove (zeroRealParts L allowed))
    {β k m a t ω σ : ℝ} (hβ : β = sSup (zeroRealParts L allowed))
    (hm : 0 < m) (hma : m < β - a)
    (hmain : t + ω ≤ β - m) (herror : m ≤ σ)
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (hJ : J =O[atTop] (fun Z : ℝ => Z ^ (t - k + ω)))
    (hE : (fun Z => J Z - f Z) =O[atTop]
      (fun Z : ℝ => Z ^ (β - k - σ)))
    (hzero : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b)))
    (hH : AnalyticOnNhd ℂ H (rightHalfPlane (β - m)))
    (hL : AnalyticOnNhd ℂ L (rightHalfPlane (β - m)))
    (hnum : ∀ z : ℂ, a < z.re → H z ≠ 0)
    (hidentity : ∃ z₀ ∈ rightHalfPlane (β - m),
      H =ᶠ[𝓝 z₀] fun z => L z * mellin f ((k : ℂ) - z)) : False := by
  exact supremum_contradiction_from_mellin L H f allowed hne hbdd hβ hm hma
    hlocal (combine_probe_isBigO J f hJ hE hmain herror) hzero hH hL hnum hidentity

/-- A domain-restricted form of the Q.4 closure.  It permits a connected
domain with the principal pole removed: only `L` and `H` on `U` must be
analytic.  Membership of the selected actual zeros in that domain, its
connectedness, and its initial identity are explicit obligations. -/
theorem supremum_contradiction_from_mellin_on_domain
    (L H : ℂ → ℂ) (f : ℝ → ℂ) (allowed : ℂ → Prop)
    (hne : (zeroRealParts L allowed).Nonempty)
    (hbdd : BddAbove (zeroRealParts L allowed))
    {β k m a : ℝ} (hβ : β = sSup (zeroRealParts L allowed))
    (hm : 0 < m) (hma : m < β - a)
    (hlocal : LocallyIntegrableOn f (Ioi 0))
    (htop : f =O[atTop] (fun Z : ℝ => Z ^ (β - k - m)))
    (hzero : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b)))
    {U : Set ℂ} (hU : IsPreconnected U)
    (hUsubset : U ⊆ rightHalfPlane (β - m))
    (hH : AnalyticOnNhd ℂ H U) (hL : AnalyticOnNhd ℂ L U)
    (hzeros : ∀ z : ℂ, allowed z → L z = 0 →
      β - m / 2 < z.re → z.re ≤ β → z ∈ U)
    (hnum : ∀ z ∈ U, allowed z → a < z.re → H z ≠ 0)
    (hidentity : ∃ z₀ ∈ U,
      H =ᶠ[𝓝 z₀] fun z => L z * mellin f ((k : ℂ) - z)) : False := by
  obtain ⟨z, hzallowed, hz, hznear, hzupper⟩ :=
    actual_zero_near_supremum L allowed hne hbdd hm
  rw [← hβ] at hznear hzupper
  have hzU := hzeros z hzallowed hz hznear hzupper
  have hznum := (near_supremum_in_continuation hm hma hznear).2
  obtain ⟨z₀, hz₀, hid⟩ := hidentity
  have hF : AnalyticOnNhd ℂ (fun s : ℂ => mellin f ((k : ℂ) - s)) U :=
    (mellin_signal_analytic f hlocal htop hzero).mono hUsubset
  exact denominator_nonzero_of_continuation hU hz₀ hzU hF hH hL hid
    (hnum z hzU hzallowed hznum) hz

end QRH.Cycle090
