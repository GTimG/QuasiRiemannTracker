/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.SideRow
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.ProfileSep

/-!
# Inverse.Poisson.ChildRow — child rows: profile form, continuity, trivial bound, `g`-zero

* `mobiusRowF_childLogTest`: the general-profile row at `childLogTest Φ s (·/Xc)` is the
  interface child `mobiusChildRowInj … true`.
* `childRow_continuous`, `childRow_norm_le`: continuity in the height, height-free bound
  (`childTriv`).
* `childRow_pool_extend`: the `g`-zero (supplied by `g | y`): if every prime of
  `g` divides the row, the residual pool `pool \ g \ t` may be replaced by `pool \ t`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open MeasureTheory OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open FirstCauchyArithmetic (supportMobius)
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem mobiusRowF_childLogTest (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (z : O) :
    mobiusRowF p hg pool ψ m slots lists a (fun n => Φ (n / Xc)) z =
      mobiusChildRowInj p hg pool ψ m slots lists a Φ Xc true z := by
  unfold mobiusRowF mobiusChildRowInj
  simp only [if_true]

theorem logPhase_norm (t x : ℝ) : ‖FourierBridge.logPhase t x‖ = 1 := by
  unfold FourierBridge.logPhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem logPhase_continuous_freq (c x : ℝ) :
    Continuous (fun t : ℝ => FourierBridge.logPhase (t + c) x) := by
  unfold FourierBridge.logPhase
  fun_prop

theorem childRow_continuous (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (c Xc : ℝ) (neg : Bool) (z : O) :
    Continuous (fun t : ℝ =>
      mobiusChildRowInj p hg pool ψ m slots lists a (childLogTest Φ (t + c)) Xc neg z) := by
  unfold mobiusChildRowInj childLogTest
  apply continuous_finset_sum
  intro A _
  have h := logPhase_continuous_freq (c := c) (x := Real.log (primeProductNorm p A / Xc))
  fun_prop

/-- Height-free bound of a child row. -/
def childTriv (pool : Finset ι) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (Φ : ℝ → ℂ) (Xc : ℝ) : ℝ :=
  ∑ A ∈ pool.powerset, ‖primeMarkInj slots lists a A‖ * ‖Φ (primeProductNorm p A / Xc)‖ *
    (Real.sqrt (primeProductNorm p A))⁻¹

theorem supportMobius_norm (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (A : Finset ι) : ‖supportMobius (fun i => Ideal.span {p i}) A‖ = 1 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj, norm_pow, norm_neg, norm_one,
    one_pow]

theorem rowCoprimeMask_norm_le (S : Finset ι) (u : O) :
    ‖rowCoprimeMask (fun i => Ideal.span {p i}) S u‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem childLogTest_norm (Φ : ℝ → ℂ) (s x : ℝ) : ‖childLogTest Φ s x‖ = ‖Φ x‖ := by
  rw [childLogTest, norm_mul, logPhase_norm, mul_one]

theorem childRow_norm_le (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (ψ : O →* ℂ) (hψ : ∀ u, ‖ψ u‖ ≤ 1) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (s Xc : ℝ)
    (neg : Bool) (z : O) :
    ‖mobiusChildRowInj p hg pool ψ m slots lists a (childLogTest Φ s) Xc neg z‖ ≤
      childTriv p pool slots lists a Φ Xc := by
  unfold mobiusChildRowInj childTriv
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro A _
  have hχ : ‖(if neg then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z)
      else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z)‖ ≤ 1 := by
    split_ifs
    · rw [norm_star]; exact finiteSquarefreeRow_norm_le_one _ hg A z
    · exact finiteSquarefreeRow_norm_le_one _ hg A z
  have hm := rowCoprimeMask_norm_le p A m
  have hψA := hψ (∏ i ∈ A, p i)
  have hs : 0 ≤ (Real.sqrt (primeProductNorm p A))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  simp only [norm_mul, supportMobius_norm p hinj, childLogTest_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs, one_mul]
  have h1 := norm_nonneg (primeMarkInj slots lists a A)
  have h2 := norm_nonneg (Φ (primeProductNorm p A / Xc))
  calc ‖ψ (∏ i ∈ A, p i)‖ * ‖rowCoprimeMask (fun i => Ideal.span {p i}) A m‖ *
        ‖(if neg then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z)
          else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A z)‖ *
        ‖primeMarkInj slots lists a A‖ * ‖Φ (primeProductNorm p A / Xc)‖ *
        (Real.sqrt (primeProductNorm p A))⁻¹
      ≤ 1 * 1 * 1 * ‖primeMarkInj slots lists a A‖ * ‖Φ (primeProductNorm p A / Xc)‖ *
        (Real.sqrt (primeProductNorm p A))⁻¹ := by gcongr
    _ = _ := by ring

/-- The `g`-zero: if every prime of `G` divides the row, the columns meeting `G` vanish. -/
theorem childRow_pool_extend (pool G : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (neg : Bool) (z : O)
    (hz : ∀ i ∈ G, z ∈ Ideal.span {p i}) :
    mobiusChildRowInj p hg (pool \ G) ψ m slots lists a Φ Xc neg z =
      mobiusChildRowInj p hg pool ψ m slots lists a Φ Xc neg z := by
  unfold mobiusChildRowInj
  apply Finset.sum_subset
  · intro A hA
    exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hA).trans Finset.sdiff_subset)
  · intro A hA hA'
    have hmeet : ∃ i ∈ A, z ∈ Ideal.span {p i} := by
      by_contra hno
      push_neg at hno
      apply hA'
      apply Finset.mem_powerset.mpr
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_powerset.mp hA hi, fun hiG => hno i hi (hz i hiG)⟩
    have hmask : rowCoprimeMask (fun i => Ideal.span {p i}) A z = 0 := by
      unfold rowCoprimeMask
      rw [if_pos hmeet]
    have hrow := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg A z hmask
    simp [hrow]

end
end Qrh.MarkedAnchor.Inverse.Poisson
