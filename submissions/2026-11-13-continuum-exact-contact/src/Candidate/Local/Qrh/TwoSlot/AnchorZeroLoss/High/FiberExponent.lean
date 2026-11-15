/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The branch structure follows Hailey Collet's `Record1252270103Source/High/FiberExponent.lean`
(`fiber_exponent`, Apache-2.0): same-zero witnesses split into long inverse, short inverse and
squared ordinary; here the short witnesses are paid at the selected width `σ(w')`. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Price
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.FiberCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness

/-!
# High.FiberExponent

The count of one detector fiber of a HIGH class.

Detector cutoff `t = 3w/2 + 10^-12` with `w ∈ [2/3, 79/100]`. A supported same-zero witness of a
fiber has inverse width `r ≤ t + ε` and ordinary width `m ≥ t - r - ε`, `m ≤ 1/2 + 75ε`. Then
* `r ≥ 1`: the native unmarked inverse gives `1/6 + (5/6-ν) r ≤` the long rate;
* `w ≤ r < 1`: the marked inverse at selected width `z(r) = min (σ(r)) S` (`S` the slot supply)
  gives `1 - ν r - e z(r) ≤ 1 - ν w - e z(w)`;
* `r < w`: then `2m ≥ w`; for `2m < 1` the squared ordinary at selected width `z(2m)`, for
  `2m ≥ 1` the unmarked ordinary, `2m(1-ν) ≤` the long rate up to `150 ε`.

`fiber_rate_cases` is the scalar case split, `fiber_rate` its exponent form, and
`high_fiber_count` the analytic count of one fiber: with the (anchor or native) marked moments at
selected width `z(·)` and the native unmarked counts,
`#rows ≤ K' U^(fiberTarget a0 a1 ν e w S + 150ε + loss)`,
`fiberTarget = max (1 - ν w - e z(w)) (1/6 + (5/6-ν) t)`, `ν = 2a-1`, `e = 2·(fiber slot mean)` (`≤ ν`).
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section

/-! ### Scalar layer -/

/-- `σ` is antitone with slope at most `1/2 + a1`. -/
theorem sig_sub_le {a0 a1 w x : ℝ} (ha1 : 0 ≤ a1) (hwx : w ≤ x) :
    0 ≤ sig a0 a1 w - sig a0 a1 x ∧ sig a0 a1 w - sig a0 a1 x ≤ (1 / 2 + a1) * (x - w) := by
  unfold sig
  have hX : (1 - x) / 2 + (a0 - a1 * x) - 1 / 10000000000000 ≤ (1 - w) / 2 + (a0 - a1 * w) - 1 / 10000000000000 := by
    nlinarith
  have hd : ((1 - w) / 2 + (a0 - a1 * w) - 1 / 10000000000000) - ((1 - x) / 2 + (a0 - a1 * x) - 1 / 10000000000000)
      = (1 / 2 + a1) * (x - w) := by ring
  constructor
  · have := max_le_max (le_refl (0 : ℝ)) hX; linarith
  · rcases le_total 0 ((1 - x) / 2 + (a0 - a1 * x) - 1 / 10000000000000) with h | h
    · rw [max_eq_right h, max_eq_right (h.trans hX)]; linarith
    · rw [max_eq_left h]
      rcases le_total 0 ((1 - w) / 2 + (a0 - a1 * w) - 1 / 10000000000000) with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; nlinarith

/-- The selected width at witness width `x` with total slot supply `S`: `min (σ(x)) S`. -/
def selW (a0 a1 S x : ℝ) : ℝ := min (sig a0 a1 x) S

theorem selW_nonneg {a0 a1 S : ℝ} (hS : 0 ≤ S) (x : ℝ) : 0 ≤ selW a0 a1 S x :=
  le_min (sig_nonneg a0 a1 x) hS

theorem selW_le_supply (a0 a1 S x : ℝ) : selW a0 a1 S x ≤ S := min_le_right _ _

theorem selW_le_sig (a0 a1 S x : ℝ) : selW a0 a1 S x ≤ sig a0 a1 x := min_le_left _ _

/-- The capped selection is antitone with slope at most `1/2 + a1`. -/
theorem selW_sub_le {a0 a1 S w x : ℝ} (ha1 : 0 ≤ a1) (hwx : w ≤ x) :
    0 ≤ selW a0 a1 S w - selW a0 a1 S x ∧
      selW a0 a1 S w - selW a0 a1 S x ≤ (1 / 2 + a1) * (x - w) := by
  obtain ⟨h1, h2⟩ := sig_sub_le (a0 := a0) ha1 hwx
  unfold selW
  constructor
  · have := min_le_min (show sig a0 a1 x ≤ sig a0 a1 w by linarith) (le_refl S); linarith
  · rcases le_total (sig a0 a1 x) S with h | h
    · rw [min_eq_left h]
      have := min_le_left (sig a0 a1 w) S; linarith
    · rw [min_eq_right h, min_eq_right (h.trans (by linarith))]; nlinarith

/-- Monotonicity of the short rate in the witness width, for any selection `z` whose
decrease is at most `(1/2 + a1)` per unit width. -/
theorem short_rate_mono {a1 ν e w x zw zx : ℝ} (ha1' : a1 ≤ 1 / 2) (he0 : 0 ≤ e)
    (he : e ≤ ν) (hwx : w ≤ x) (hz : zw - zx ≤ (1 / 2 + a1) * (x - w)) (ha1 : 0 ≤ a1) :
    1 - ν * x - e * zx ≤ 1 - ν * w - e * zw := by
  have h3 : e * (zw - zx) ≤ e * ((1 / 2 + a1) * (x - w)) := mul_le_mul_of_nonneg_left hz he0
  have h4 : e * ((1 / 2 + a1) * (x - w)) ≤ ν * (x - w) := by
    have : e * (1 / 2 + a1) ≤ ν := by nlinarith
    nlinarith
  nlinarith

/-- The short and long target rate of a HIGH fiber with cutoff width `w` and slot supply `S`. -/
def fiberTarget (a0 a1 ν e w S : ℝ) (shift : ℝ := 1/1000000000000) : ℝ :=
  max (1 - ν * w - e * selW a0 a1 S w) (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + shift))

/-- **Case split of a supported witness.** Selections are capped by the slot supply `S`. -/
theorem fiber_rate_cases_with_shift {shift a0 a1 ν e w S ε r m : ℝ} (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1 / 2)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he : e ≤ ν) (hw : w ∈ cutoffs)
    (hε0 : 0 ≤ ε) (hε : ε ≤ shift)
    (hlen : (3 * w / 2 + shift) - r - ε ≤ m) (hr : r ≤ (3 * w / 2 + shift) + ε)
    (hm : m ≤ 1 / 2 + 75 * ε) :
    (1 ≤ r ∧ max 1 ((1 + 5 * r) / 6) - ν * r ≤ fiberTarget a0 a1 ν e w S shift + 150 * ε) ∨
    (w ≤ r ∧ r < 1 ∧ 1 - ν * r - e * selW a0 a1 S r ≤ fiberTarget a0 a1 ν e w S shift + 150 * ε) ∨
    (w ≤ 2 * m ∧ 2 * m < 1 ∧
      1 - 2 * ν * m - e * selW a0 a1 S (2 * m) ≤ fiberTarget a0 a1 ν e w S shift + 150 * ε) ∨
    (max 1 (2 * m) - 2 * ν * m ≤ fiberTarget a0 a1 ν e w S shift + 150 * ε) := by
  obtain ⟨hw1, hw2⟩ := hw
  unfold cutLo at hw1; unfold cutHi at hw2
  have hS := le_max_left (1 - ν * w - e * selW a0 a1 S w)
    (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + shift))
  have hL := le_max_right (1 - ν * w - e * selW a0 a1 S w)
    (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + shift))
  unfold fiberTarget
  by_cases hr1 : 1 ≤ r
  · left
    refine ⟨hr1, ?_⟩
    rw [max_eq_right (by linarith : (1 : ℝ) ≤ (1 + 5 * r) / 6)]
    have : (5 / 6 - ν) * r ≤ (5 / 6 - ν) * ((3 * w / 2 + shift) + ε) :=
      mul_le_mul_of_nonneg_left hr (by linarith)
    nlinarith
  · push_neg at hr1
    by_cases hwr : w ≤ r
    · right; left
      exact ⟨hwr, hr1, (short_rate_mono ha1' he0 he hwr
        (selW_sub_le (a0 := a0) (S := S) ha1 hwr).2 ha1).trans (by nlinarith)⟩
    · push_neg at hwr
      have h2m : w ≤ 2 * m := by linarith
      by_cases hm1 : 2 * m < 1
      · right; right; left
        refine ⟨h2m, hm1, ?_⟩
        have := short_rate_mono (ν := ν) ha1' he0 he h2m
          (selW_sub_le (a0 := a0) (S := S) ha1 h2m).2 ha1
        have e1 : 1 - 2 * ν * m - e * selW a0 a1 S (2 * m) =
            1 - ν * (2 * m) - e * selW a0 a1 S (2 * m) := by ring
        rw [e1]; nlinarith
      · right; right; right
        push_neg at hm1
        rw [max_eq_right hm1]
        have hlong : 1 - ν ≤ 1 / 6 + (5 / 6 - ν) * (3 * w / 2 + shift) := by nlinarith
        have : 2 * m - 2 * ν * m ≤ (1 + 150 * ε) * (1 - ν) := by nlinarith
        nlinarith


/-- Specialization to the frozen finite witness shift. -/
theorem fiber_rate_cases {a0 a1 ν e w S ε r m : ℝ} (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1 / 2)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he : e ≤ ν) (hw : w ∈ cutoffs)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000000000000)
    (hlen : (3 * w / 2 + 1 / 1000000000000) - r - ε ≤ m) (hr : r ≤ (3 * w / 2 + 1 / 1000000000000) + ε)
    (hm : m ≤ 1 / 2 + 75 * ε) :
    (1 ≤ r ∧ max 1 ((1 + 5 * r) / 6) - ν * r ≤ fiberTarget a0 a1 ν e w S + 150 * ε) ∨
    (w ≤ r ∧ r < 1 ∧ 1 - ν * r - e * selW a0 a1 S r ≤ fiberTarget a0 a1 ν e w S + 150 * ε) ∨
    (w ≤ 2 * m ∧ 2 * m < 1 ∧
      1 - 2 * ν * m - e * selW a0 a1 S (2 * m) ≤ fiberTarget a0 a1 ν e w S + 150 * ε) ∨
    (max 1 (2 * m) - 2 * ν * m ≤ fiberTarget a0 a1 ν e w S + 150 * ε) :=
  fiber_rate_cases_with_shift ha1 ha1' hν0 hν he0 he hw hε0 hε hlen hr hm

/-- Exponent form (as Hailey Collet's `fiber_exponent`): four branch bounds give the HIGH rate. -/
theorem fiber_rate_with_shift {shift a0 a1 ν e w S ε r m E loss : ℝ} (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1 / 2)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he : e ≤ ν) (hw : w ∈ cutoffs)
    (hε0 : 0 ≤ ε) (hε : ε ≤ shift)
    (hlen : (3 * w / 2 + shift) - r - ε ≤ m) (hr : r ≤ (3 * w / 2 + shift) + ε)
    (hm : m ≤ 1 / 2 + 75 * ε)
    (hI0 : E ≤ max 1 ((1 + 5 * r) / 6) - ν * r + loss)
    (hP0 : E ≤ max 1 (2 * m) - 2 * ν * m + loss)
    (hIM : w ≤ r → r < 1 → E ≤ 1 - ν * r - e * selW a0 a1 S r + loss)
    (hPM : w ≤ 2 * m → 2 * m < 1 → E ≤ 1 - 2 * ν * m - e * selW a0 a1 S (2 * m) + loss) :
    E ≤ fiberTarget a0 a1 ν e w S shift + 150 * ε + loss := by
  rcases fiber_rate_cases_with_shift (a0 := a0) (S := S) ha1 ha1' hν0 hν he0 he hw hε0 hε hlen hr hm with
    ⟨_, h⟩ | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩ | h
  · linarith
  · linarith [hIM h1 h2]
  · linarith [hPM h1 h2]
  · linarith


/-- Specialization to the frozen finite witness shift. -/
theorem fiber_rate {a0 a1 ν e w S ε r m E loss : ℝ} (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1 / 2)
    (hν0 : 0 ≤ ν) (hν : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he : e ≤ ν) (hw : w ∈ cutoffs)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000000000000)
    (hlen : (3 * w / 2 + 1 / 1000000000000) - r - ε ≤ m) (hr : r ≤ (3 * w / 2 + 1 / 1000000000000) + ε)
    (hm : m ≤ 1 / 2 + 75 * ε)
    (hI0 : E ≤ max 1 ((1 + 5 * r) / 6) - ν * r + loss)
    (hP0 : E ≤ max 1 (2 * m) - 2 * ν * m + loss)
    (hIM : w ≤ r → r < 1 → E ≤ 1 - ν * r - e * selW a0 a1 S r + loss)
    (hPM : w ≤ 2 * m → 2 * m < 1 → E ≤ 1 - 2 * ν * m - e * selW a0 a1 S (2 * m) + loss) :
    E ≤ fiberTarget a0 a1 ν e w S + 150 * ε + loss :=
  fiber_rate_with_shift ha1 ha1' hν0 hν he0 he hw hε0 hε hlen hr hm hI0 hP0 hIM hPM

/-- Promotion of a count bound to a larger constant and exponent (`U ≥ 1`). -/
theorem count_promote {N C C' U x y : ℝ} (hU : 1 ≤ U) (hC : C ≤ C') (hC' : 0 ≤ C')
    (hN : N ≤ C * U ^ x) (hxy : x ≤ y) : N ≤ C' * U ^ y := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  calc N ≤ C * U ^ x := hN
    _ ≤ C' * U ^ x := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hU0.le _)
    _ ≤ C' * U ^ y := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hxy) hC'

/-! ### The analytic count of one HIGH fiber -/

section Analytic
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open HeckeDetectorSupportedWitness
local notation "O" => HeckeFamily.O


/-- **Count of one HIGH detector fiber.** Rows with fixed label, fixed dyadic witness widths
`r = log_U 2^J`, `m = log_U 2^K` and fixed slot bins, cutoff `tstar = 3w/2 + 10^-12`; `S` is the total
slot width of the fiber (relative to `U`). Inputs:
* `hI0`, `hP0`: the native unmarked inverse and ordinary counts of the fiber;
* `hinv`: for `w ≤ r < 1` the marked inverse moment for every whole-slot selection of width
  `≤ min (σ(r)) S` (from the anchor of an earlier stage containing `r`, or the native source above
  `TOP`: `High.Sources.high_child_sources`);
* `hpl`: for `w ≤ 2m < 1` the squared ordinary moment for every selection of width `≤ min (σ(2m)) S`.
Output: `#rows ≤ K' U^(fiberTarget a0 a1 ν e w S + 150 ε + loss')` with `ν = 2a - 1`,
`e = 2 · weightedMean slots widths g ∈ [0, ν]`. -/
theorem high_fiber_count_with_shift {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1 ≤ 3/4)
    (witness : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (shift a0 a1 w K₀ loss : ℝ) (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (hwc : w ∈ cutoffs)
    (ht : tstar = 3*w/2 + shift) (hε0 : 0 ≤ ε) (hε : ε ≤ shift) (hK₀ : 0 ≤ K₀)
    (hI0 : (rows.card : ℝ) ≤ K₀ * U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J.val))/6)
      - (2*a-1)*Real.logb U ((2 : ℝ)^J.val) + loss))
    (hP0 : (rows.card : ℝ) ≤ K₀ * U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))
      - 2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val) + loss))
    (hinv : w ≤ Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val) < 1 →
      ∀ selected : Finset Slot, selected⊆slots →
        (∑ s∈selected,widths s) ≤
          selW a0 a1 (∑ s∈slots,widths s) (Real.logb U ((2 : ℝ)^J.val)) →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm))
    (hpl : w ≤ 2*Real.logb U ((2 : ℝ)^K.val) → 2*Real.logb U ((2 : ℝ)^K.val) < 1 →
      ∀ selected : Finset Slot, selected⊆slots →
        (∑ s∈selected,widths s) ≤
          selW a0 a1 (∑ s∈slots,widths s) (2*Real.logb U ((2 : ℝ)^K.val)) →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ) ≤ max K₀ (192*(1+height)*C) *
      U^(fiberTarget a0 a1 (2*a-1) (2*weightedMean slots widths g) w (∑ s∈slots,widths s) shift +
        150*ε + max loss (4*ε+(2*a-1)*mesh+εm)) := by
  set r := Real.logb U ((2 : ℝ)^J.val) with hrdef
  set m := Real.logb U ((2 : ℝ)^K.val) with hmdef
  set ν := 2*a-1 with hνdef
  set e := 2*weightedMean slots widths g with hedef
  set S := ∑ s∈slots,widths s with hSdef
  have hν0 : 0 ≤ ν := by rw [hνdef]; linarith
  have hU1 : 1 ≤ U := hU.le
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤g s ∧ g s≤ν/2 := by
    rw [←hbins u0 hu0 s hs]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hqν⟩ : 0 ≤ weightedMean slots widths g ∧ weightedMean slots widths g ≤ ν/2 := by
    rcases lt_or_eq_of_le hL with hpos | hzero
    · exact weightedMean_bounds slots widths g ν (fun s hs => (hw s hs).le) hpos hg
    · have : weightedMean slots widths g = 0 := by
        unfold weightedMean
        rw [show (∑ s∈slots,widths s) = 0 from hzero.symm, div_zero]
      rw [this]; constructor <;> linarith
  have he0 : 0 ≤ e := by rw [hedef]; linarith
  have he : e ≤ ν := by rw [hedef]; linarith
  obtain ⟨hlen,hr,hm,-,-⟩ := fiber_lengths rows ⟨u0,hu0⟩ χ U a ε tstar T allowance i hU witness
    J K hJ hK
  rw [ht] at hlen hr
  have hKC : 0 ≤ max K₀ (192*(1+height)*C) := le_max_of_le_left hK₀
  have hloss : loss ≤ max loss (4*ε+ν*mesh+εm) := le_max_left _ _
  have hloss' : 4*ε+ν*mesh+εm ≤ max loss (4*ε+ν*mesh+εm) := le_max_right _ _
  have hνmesh : 0 ≤ ν*mesh := mul_nonneg hν0 hmesh
  have h12 : 12*(1+height)*C ≤ max K₀ (192*(1+height)*C) :=
    (by nlinarith : 12*(1+height)*C ≤ 192*(1+height)*C).trans (le_max_right _ _)
  rcases fiber_rate_cases_with_shift (a0 := a0) (S := S) ha1 ha1' hν0 hν he0 he hwc hε0 hε hlen hr hm with
    ⟨_, hb⟩ | ⟨h1, h2, hb⟩ | ⟨h1, h2, hb⟩ | hb
  · exact count_promote hU1 (le_max_left _ _) hKC hI0 (by linarith)
  · have hz0 := selW_nonneg (a0 := a0) (a1 := a1) hL r
    have hc := gated_inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε tstar T allowance i hU ha
      (fun u => (witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth (selW a0 a1 S r) εm C height hmesh hbin hw hwm hL hz0
      (selW_le_supply a0 a1 S r) hbins hC hheight hfreq (hinv h1 h2)
    refine count_promote hU1 h12 hKC hc ?_
    have : 2*weightedMean slots widths g*selW a0 a1 S r = e*selW a0 a1 S r := by rw [hedef]
    rw [this]; linarith
  · have hz0 := selW_nonneg (a0 := a0) (a1 := a1) hL (2*m)
    have hc := gated_plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε tstar T allowance i hU ha
      (fun u => (witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth (selW a0 a1 S (2*m)) εm C height hmesh hbin hw hwm hL hz0
      (selW_le_supply a0 a1 S (2*m)) hbins hC hheight hfreq (hpl h1 h2)
    refine count_promote hU1 (le_max_right _ _) hKC hc ?_
    have : 2*weightedMean slots widths g*selW a0 a1 S (2*m) = e*selW a0 a1 S (2*m) := by
      rw [hedef]
    rw [this]; linarith
  · exact count_promote hU1 (le_max_left _ _) hKC hP0 (by linarith)

/-- Specialization to the frozen finite witness shift. -/
theorem high_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1 ≤ 3/4)
    (witness : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth εm C height : ℝ) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (a0 a1 w K₀ loss : ℝ) (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2) (hwc : w ∈ cutoffs)
    (ht : tstar = 3*w/2 + 1/1000000000000) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/1000000000000) (hK₀ : 0 ≤ K₀)
    (hI0 : (rows.card : ℝ) ≤ K₀ * U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J.val))/6)
      - (2*a-1)*Real.logb U ((2 : ℝ)^J.val) + loss))
    (hP0 : (rows.card : ℝ) ≤ K₀ * U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))
      - 2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val) + loss))
    (hinv : w ≤ Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val) < 1 →
      ∀ selected : Finset Slot, selected⊆slots →
        (∑ s∈selected,widths s) ≤
          selW a0 a1 (∑ s∈slots,widths s) (Real.logb U ((2 : ℝ)^J.val)) →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm))
    (hpl : w ≤ 2*Real.logb U ((2 : ℝ)^K.val) → 2*Real.logb U ((2 : ℝ)^K.val) < 1 →
      ∀ selected : Finset Slot, selected⊆slots →
        (∑ s∈selected,widths s) ≤
          selW a0 a1 (∑ s∈slots,widths s) (2*Real.logb U ((2 : ℝ)^K.val)) →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ) ≤ max K₀ (192*(1+height)*C) *
      U^(fiberTarget a0 a1 (2*a-1) (2*weightedMean slots widths g) w (∑ s∈slots,widths s) +
        150*ε + max loss (4*ε+(2*a-1)*mesh+εm)) :=
  high_fiber_count_with_shift rows hne χ U a ε tstar T allowance i hU ha hν witness
    label J K hlabel hJ hK slots Q widths g mesh binWidth εm C height hmesh hbin hw hwm
    hL hbins hC hheight hfreq (1/1000000000000) a0 a1 w K₀ loss ha1 ha1' hwc
    ht hε0 hε hK₀ hI0 hP0 hinv hpl


end Analytic

end
end Qrh.TwoSlot.AnchorZeroLoss.High
