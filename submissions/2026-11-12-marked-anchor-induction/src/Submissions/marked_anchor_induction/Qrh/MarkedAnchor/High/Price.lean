/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.sil_density_split_20261026.CubeFree.Price
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# High.Price

The HIGH price of the anchor induction, as an exponential leaf price in the sense of
sil-density-split `CubeFree.Price`.

All widths are absolute exponents of one child row ball: `P` the free width (inverse: `r`;
ordinary: `ℓ₁+ℓ₂`), `s` the total slot width, `M` the row radius. A HIGH class is a pair
`(ν, e)` with `k ≤ ν ≤ 3/4` (buffered zero exponent) and `0 ≤ e ≤ ν` (lower slot mean amplitude).
The stage line is `l(w) = a0 - a1 w`.

* `sig a0 a1 w = max 0 ((1-w)/2 + l(w) - 10^-7)`: the selected slot width (relative) at witness
  width `w`;
* `shortCnt`: the short count exponent `M - ν M w - e min(s, M σ(w))` (selection capped by the
  supply `s`);
* `longCnt`: the long inverse count exponent `M (1/6 + (5/6-ν) t)`, `t = 3w/2 + 10^-6`;
* `detEx`: excess over `M` after the pointwise payment `ν P + e s`;
* `tinyEx`: the tiny-core term (cores of norm `≤ Z^(2/25)`);
* `detPrice = sup_{(ν,e)} inf_{w ∈ [2/3, 79/100]} detEx` and
  `highPriceF = max 0 (max tinyEx detPrice)`.

`highPrice a0 a1 k` packages `highPriceF` as a `Price` (nonnegative, monotone in `P, s`,
Lipschitz in `P, s, M` with constant `2 + |a0| + |a1|`). Further: `highPriceF_antitoneM`
(larger radius, ordinary children), `exists_cutoff` (the cutoff used by the leaf for one class),
`highPriceF_le_of` (how the stage ledger bounds the price).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section

/-! ### Definitions -/

/-- Selected slot width (relative to the row radius) at witness width `w`: `((1-w)/2 + l(w) - pad)₊`. -/
def sig (a0 a1 w : ℝ) : ℝ := max 0 ((1 - w) / 2 + (a0 - a1 * w) - 1 / 10000000)

/-- Short count exponent: `M - ν M w - e min(s, M σ(w))`. -/
def shortCnt (a0 a1 ν e w s M : ℝ) : ℝ := M - ν * M * w - e * min s (M * sig a0 a1 w)

/-- Long count exponent `M (1/6 + (5/6-ν) t)` with cutoff `t = 3w/2 + 10^-6`. -/
def longCnt (ν w M : ℝ) : ℝ := M / 6 + (5 / 6 - ν) * M * (3 * w / 2 + 1 / 1000000)

/-- Excess over the radius `M` of the detector-paid energy of the class `(ν,e)` at cutoff `w`. -/
def detEx (a0 a1 ν e w P s M : ℝ) : ℝ :=
  ν * P + e * s + max (shortCnt a0 a1 ν e w s M) (longCnt ν w M) - M

/-- Excess of the tiny-core rows: count `M/6 + 5(2/25)/6`, pointwise `(3/4) P + s`. -/
def tinyEx (P s M : ℝ) : ℝ := M / 6 + 1 / 15 + 3 / 4 * P + s - M

/-- Lower end of the cutoff widths (`t > 1`). -/
def cutLo : ℝ := 2 / 3
/-- Upper end of the cutoff widths (`t < 3/2`). -/
def cutHi : ℝ := 79 / 100

/-- The admissible cutoff widths. -/
def cutoffs : Set ℝ := Set.Icc cutLo cutHi

/-- The HIGH classes `(ν, e)`: `k ≤ ν ≤ 3/4`, `0 ≤ e ≤ ν`. -/
def classes (k : ℝ) : Set (ℝ × ℝ) := {p | k ≤ p.1 ∧ p.1 ≤ 3 / 4 ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1}

/-- Infimum over the cutoff widths. -/
def infW (f : ℝ → ℝ) : ℝ := ⨅ w : cutoffs, f w

/-- Supremum over the HIGH classes. -/
def supC (k : ℝ) (F : ℝ × ℝ → ℝ) : ℝ := ⨆ p : classes k, F p

/-- The detector price `sup_{(ν,e)} inf_w detEx`. -/
def detPrice (a0 a1 k P s M : ℝ) : ℝ :=
  supC k fun p => infW fun w => detEx a0 a1 p.1 p.2 w P s M

/-- The HIGH price. -/
def highPriceF (a0 a1 k P s M : ℝ) : ℝ := max 0 (max (tinyEx P s M) (detPrice a0 a1 k P s M))

/-- The Lipschitz constant. -/
def lipH (a0 a1 : ℝ) : ℝ := 2 + |a0| + |a1|

theorem lipH_ge_one (a0 a1 : ℝ) : 1 ≤ lipH a0 a1 := by
  unfold lipH; have := abs_nonneg a0; have := abs_nonneg a1; linarith

theorem cutLo_mem : cutLo ∈ cutoffs := ⟨le_rfl, by norm_num [cutLo, cutHi]⟩

instance cutoffs_nonempty : Nonempty cutoffs := ⟨⟨cutLo, cutLo_mem⟩⟩

/-! ### inf / sup helpers -/

theorem infW_le {f : ℝ → ℝ} {B : ℝ} (hB : ∀ w ∈ cutoffs, -B ≤ f w) {w : ℝ}
    (hw : w ∈ cutoffs) : infW f ≤ f w :=
  ciInf_le (f := fun w : cutoffs => f w) ⟨-B, by rintro _ ⟨x, rfl⟩; exact hB x x.2⟩ ⟨w, hw⟩

theorem le_infW {f : ℝ → ℝ} {a : ℝ} (h : ∀ w ∈ cutoffs, a ≤ f w) : a ≤ infW f :=
  le_ciInf fun w => h w w.2

theorem infW_le_add {f g : ℝ → ℝ} {c B : ℝ} (hB : ∀ w ∈ cutoffs, -B ≤ g w)
    (h : ∀ w ∈ cutoffs, g w ≤ f w + c) : infW g ≤ infW f + c := by
  have : infW g - c ≤ infW f := le_infW fun w hw => by
    have := infW_le hB hw; linarith [h w hw]
  linarith

theorem exists_lt_infW {f : ℝ → ℝ} {a : ℝ} (h : infW f < a) : ∃ w ∈ cutoffs, f w < a := by
  obtain ⟨w, hw⟩ := exists_lt_of_ciInf_lt h
  exact ⟨w, w.2, hw⟩

theorem classes_nonempty {k : ℝ} (hk : k ≤ 3 / 4) : Nonempty (classes k) :=
  ⟨⟨(3 / 4, 0), hk, le_rfl, le_rfl, by norm_num⟩⟩

theorem le_supC {k : ℝ} {F : ℝ × ℝ → ℝ} {B : ℝ} (hB : ∀ p ∈ classes k, F p ≤ B) {p : ℝ × ℝ}
    (hp : p ∈ classes k) : F p ≤ supC k F :=
  le_ciSup (f := fun p : classes k => F p) ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x x.2⟩ ⟨p, hp⟩

theorem supC_le {k : ℝ} (hk : k ≤ 3 / 4) {F : ℝ × ℝ → ℝ} {a : ℝ}
    (h : ∀ p ∈ classes k, F p ≤ a) : supC k F ≤ a := by
  haveI := classes_nonempty hk
  exact ciSup_le fun p => h p p.2

/-! ### Pointwise facts on `detEx` -/

section Pointwise
variable {a0 a1 ν e w : ℝ}

theorem sig_nonneg (a0 a1 w : ℝ) : 0 ≤ sig a0 a1 w := le_max_left _ _

theorem sig_le (hw : w ∈ cutoffs) : sig a0 a1 w ≤ 1 + |a0| + |a1| := by
  obtain ⟨h1, h2⟩ := hw
  unfold cutLo at h1; unfold cutHi at h2
  unfold sig
  refine max_le (by positivity) ?_
  have ha0 := le_abs_self a0
  have ha1 : -(a1 * w) ≤ |a1| := by
    have : |a1 * w| ≤ |a1| := by
      rw [abs_mul]
      have : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      nlinarith [abs_nonneg a1]
    linarith [neg_abs_le (a1 * w)]
  linarith

theorem detEx_P (a0 a1 ν e w P s M δ : ℝ) :
    detEx a0 a1 ν e w (P + δ) s M = detEx a0 a1 ν e w P s M + ν * δ := by
  unfold detEx; ring

theorem max_le_max_sub {a b a' b' c : ℝ} (ha : a - c ≤ a') (hb : b - c ≤ b') :
    max a b - c ≤ max a' b' := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact (by linarith : b - c ≤ b').trans (le_max_right _ _)
  · rw [max_eq_left h]; exact (by linarith : a - c ≤ a').trans (le_max_left _ _)

theorem detEx_s (he : 0 ≤ e) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    detEx a0 a1 ν e w P s M ≤ detEx a0 a1 ν e w P (s + δ) M ∧
      detEx a0 a1 ν e w P (s + δ) M ≤ detEx a0 a1 ν e w P s M + e * δ := by
  unfold detEx shortCnt
  generalize M * sig a0 a1 w = X
  generalize longCnt ν w M = Lc
  have m1 : min s X ≤ min (s + δ) X := min_le_min (by linarith) le_rfl
  have m2 : min (s + δ) X ≤ min s X + δ := by
    rcases le_total s X with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _)
    · rw [min_eq_right h]; linarith [min_le_right (s + δ) X]
  have e1 := mul_le_mul_of_nonneg_left m1 he
  have e2 := mul_le_mul_of_nonneg_left m2 he
  constructor
  · have : max (M - ν * M * w - e * min s X) Lc - e * δ ≤
        max (M - ν * M * w - e * min (s + δ) X) Lc :=
      max_le_max_sub (by nlinarith) (by nlinarith)
    linarith
  · have : max (M - ν * M * w - e * min (s + δ) X) Lc ≤
        max (M - ν * M * w - e * min s X) Lc :=
      max_le_max (by linarith) le_rfl
    linarith

/-- `detEx` with the radius pulled into the two branches. -/
theorem detEx_eq (a0 a1 ν e w P s x : ℝ) : detEx a0 a1 ν e w P s x = ν * P + e * s +
    max (-(ν * x * w) - e * min s (x * sig a0 a1 w))
      (x * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1)) := by
  unfold detEx shortCnt longCnt
  have h := max_sub_sub_right (x - ν * x * w - e * min s (x * sig a0 a1 w))
    (x / 6 + (5 / 6 - ν) * x * (3 * w / 2 + 1 / 1000000)) x
  have e1 : x - ν * x * w - e * min s (x * sig a0 a1 w) - x =
      -(ν * x * w) - e * min s (x * sig a0 a1 w) := by ring
  have e2 : x / 6 + (5 / 6 - ν) * x * (3 * w / 2 + 1 / 1000000) - x =
      x * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1) := by ring
  rw [e1, e2] at h
  linarith

theorem detEx_M (hν0 : 0 ≤ ν) (hν1 : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he1 : e ≤ 3 / 4)
    (hw : w ∈ cutoffs) (P s M δ : ℝ) :
    |detEx a0 a1 ν e w P s (M + δ) - detEx a0 a1 ν e w P s M| ≤ lipH a0 a1 * |δ| := by
  have hσ0 := sig_nonneg a0 a1 w
  have hσ := sig_le (a0 := a0) (a1 := a1) hw
  obtain ⟨hw1, hw2⟩ := hw
  unfold cutLo at hw1; unfold cutHi at hw2
  rw [detEx_eq, detEx_eq]
  generalize sig a0 a1 w = σ at hσ0 hσ ⊢
  have hm := abs_max_sub_max_le_max (-(ν * (M + δ) * w) - e * min s ((M + δ) * σ))
    ((M + δ) * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1))
    (-(ν * M * w) - e * min s (M * σ))
    (M * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1))
  have hmin := abs_min_sub_min_le_max s ((M + δ) * σ) s (M * σ)
  rw [sub_self, abs_zero, show (M + δ) * σ - M * σ = δ * σ by ring, abs_mul, abs_of_nonneg hσ0,
    max_eq_right (by positivity)] at hmin
  have hA : |(-(ν * (M + δ) * w) - e * min s ((M + δ) * σ)) -
      (-(ν * M * w) - e * min s (M * σ))| ≤ lipH a0 a1 * |δ| := by
    have e1 : (-(ν * (M + δ) * w) - e * min s ((M + δ) * σ)) -
        (-(ν * M * w) - e * min s (M * σ)) =
        -(ν * w * δ) - e * (min s ((M + δ) * σ) - min s (M * σ)) := by ring
    rw [e1]
    have t1 : |ν * w * δ| ≤ |δ| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ν * w)]
      have : ν * w ≤ 1 := by nlinarith
      nlinarith [abs_nonneg δ]
    have t2 : |e * (min s ((M + δ) * σ) - min s (M * σ))| ≤ (1 + |a0| + |a1|) * |δ| := by
      rw [abs_mul, abs_of_nonneg he0]
      have : |δ| * σ ≤ |δ| * (1 + |a0| + |a1|) := mul_le_mul_of_nonneg_left hσ (abs_nonneg δ)
      have h3 : e * |min s ((M + δ) * σ) - min s (M * σ)| ≤ e * (|δ| * σ) :=
        mul_le_mul_of_nonneg_left hmin he0
      have h4 : e * (|δ| * σ) ≤ |δ| * σ := by
        have : 0 ≤ |δ| * σ := by positivity
        nlinarith
      linarith
    calc |-(ν * w * δ) - e * (min s ((M + δ) * σ) - min s (M * σ))|
        ≤ |-(ν * w * δ)| + |e * (min s ((M + δ) * σ) - min s (M * σ))| := by
          have := abs_add_le (-(ν * w * δ)) (-(e * (min s ((M + δ) * σ) - min s (M * σ))))
          rw [abs_neg (e * (min s ((M + δ) * σ) - min s (M * σ)))] at this
          rw [sub_eq_add_neg]; exact this
      _ ≤ |δ| + (1 + |a0| + |a1|) * |δ| := by rw [abs_neg]; linarith
      _ = lipH a0 a1 * |δ| := by unfold lipH; ring
  have hB : |(M + δ) * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1) -
      M * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1)| ≤ lipH a0 a1 * |δ| := by
    rw [show (M + δ) * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1) -
      M * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1) =
      δ * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1) by ring, abs_mul]
    have hc : |1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have := lipH_ge_one a0 a1
    nlinarith [abs_nonneg δ]
  have : |ν * P + e * s + max (-(ν * (M + δ) * w) - e * min s ((M + δ) * σ))
        ((M + δ) * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1)) -
      (ν * P + e * s + max (-(ν * M * w) - e * min s (M * σ))
        (M * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1)))| =
      |max (-(ν * (M + δ) * w) - e * min s ((M + δ) * σ))
        ((M + δ) * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1)) -
      max (-(ν * M * w) - e * min s (M * σ))
        (M * (1 / 6 + (5 / 6 - ν) * (3 * w / 2 + 1 / 1000000) - 1))| := by
    congr 1; ring
  rw [this]
  exact hm.trans (max_le hA hB)

theorem detEx_zero (a0 a1 ν e w : ℝ) : detEx a0 a1 ν e w 0 0 0 = 0 := by
  unfold detEx shortCnt longCnt; simp

/-- A uniform bound on `|detEx|` over the classes and the cutoffs. -/
theorem abs_detEx_le (hν0 : 0 ≤ ν) (hν1 : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he1 : e ≤ ν)
    (hw : w ∈ cutoffs) (P s M : ℝ) :
    |detEx a0 a1 ν e w P s M| ≤ |P| + |s| + lipH a0 a1 * |M| := by
  have h1 : detEx a0 a1 ν e w P s M = detEx a0 a1 ν e w 0 s M + ν * P := by
    have := detEx_P a0 a1 ν e w 0 s M P; rw [zero_add] at this; exact this
  have h2 : |detEx a0 a1 ν e w 0 s M - detEx a0 a1 ν e w 0 0 M| ≤ |s| := by
    rcases le_total 0 s with hs | hs
    · obtain ⟨l, u⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := ν) (w := w) he0 0 0 M s hs
      rw [zero_add] at l u
      rw [abs_le, abs_of_nonneg hs]; constructor <;> nlinarith
    · obtain ⟨l, u⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := ν) (w := w) he0 0 s M (-s) (by linarith)
      rw [add_neg_cancel] at l u
      rw [abs_le, abs_of_nonpos hs]; constructor <;> nlinarith
  have h3 := detEx_M (a0 := a0) (a1 := a1) hν0 hν1 he0 (he1.trans hν1) hw 0 0 0 M
  rw [zero_add, detEx_zero, sub_zero] at h3
  have h4 : |ν * P| ≤ |P| := by
    rw [abs_mul, abs_of_nonneg hν0]; nlinarith [abs_nonneg P]
  have h5 := abs_sub_abs_le_abs_sub (detEx a0 a1 ν e w 0 s M) (detEx a0 a1 ν e w 0 0 M)
  have h6 := abs_add_le (detEx a0 a1 ν e w 0 s M) (ν * P)
  rw [h1]
  linarith

end Pointwise

/-! ### The detector price -/

section DetPrice
variable {a0 a1 k : ℝ}

/-- Bound of `detEx` used for the `inf`/`sup` bookkeeping. -/
def bnd (a0 a1 P s M : ℝ) : ℝ := |P| + |s| + lipH a0 a1 * |M|

theorem detEx_bounds (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) {w : ℝ} (hw : w ∈ cutoffs)
    (P s M : ℝ) :
    -bnd a0 a1 P s M ≤ detEx a0 a1 p.1 p.2 w P s M ∧ detEx a0 a1 p.1 p.2 w P s M ≤ bnd a0 a1 P s M := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact abs_le.mp (abs_detEx_le (hk0.trans h1) h2 h3 h4 hw P s M)

theorem infW_detEx_le (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) (P s M : ℝ) :
    infW (fun w => detEx a0 a1 p.1 p.2 w P s M) ≤ bnd a0 a1 P s M :=
  (infW_le (fun w hw => (detEx_bounds hk0 hp hw P s M).1) cutLo_mem).trans
    (detEx_bounds hk0 hp cutLo_mem P s M).2

theorem infW_le_detPrice (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) (P s M : ℝ) :
    infW (fun w => detEx a0 a1 p.1 p.2 w P s M) ≤ detPrice a0 a1 k P s M :=
  le_supC (F := fun p => infW fun w => detEx a0 a1 p.1 p.2 w P s M)
    (fun q hq => infW_detEx_le hk0 hq P s M) hp

/-- Comparison of two detector prices from a pointwise comparison. -/
theorem detPrice_le_add (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M P' s' M' c : ℝ}
    (h : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P' s' M' ≤ detEx a0 a1 p.1 p.2 w P s M + c) :
    detPrice a0 a1 k P' s' M' ≤ detPrice a0 a1 k P s M + c := by
  refine supC_le hk1 fun p hp => ?_
  have h1 : infW (fun w => detEx a0 a1 p.1 p.2 w P' s' M') ≤
      infW (fun w => detEx a0 a1 p.1 p.2 w P s M) + c :=
    infW_le_add (fun w hw => (detEx_bounds hk0 hp hw P' s' M').1) (h p hp)
  have h2 := infW_le_detPrice (a0 := a0) (a1 := a1) hk0 hp P s M
  linarith

/-- The detector price is at most `c` when every class has a cutoff with excess `≤ c`. -/
theorem detPrice_le_of (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M c : ℝ}
    (h : ∀ p ∈ classes k, ∃ w ∈ cutoffs, detEx a0 a1 p.1 p.2 w P s M ≤ c) :
    detPrice a0 a1 k P s M ≤ c := by
  refine supC_le hk1 fun p hp => ?_
  obtain ⟨w, hw, hle⟩ := h p hp
  exact (infW_le (fun w hw => (detEx_bounds hk0 hp hw P s M).1) hw).trans hle

end DetPrice

/-! ### The HIGH price -/

section HighPrice
variable {a0 a1 k : ℝ}

theorem highPriceF_nonneg (a0 a1 k P s M : ℝ) : 0 ≤ highPriceF a0 a1 k P s M := le_max_left _ _

theorem tinyEx_le_highPriceF (a0 a1 k P s M : ℝ) : tinyEx P s M ≤ highPriceF a0 a1 k P s M :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem detPrice_le_highPriceF (a0 a1 k P s M : ℝ) :
    detPrice a0 a1 k P s M ≤ highPriceF a0 a1 k P s M :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem highPriceF_le_add (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M P' s' M' c : ℝ} (hc : 0 ≤ c)
    (ht : tinyEx P' s' M' ≤ tinyEx P s M + c)
    (h : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P' s' M' ≤ detEx a0 a1 p.1 p.2 w P s M + c) :
    highPriceF a0 a1 k P' s' M' ≤ highPriceF a0 a1 k P s M + c := by
  have hd := detPrice_le_add hk0 hk1 h
  unfold highPriceF
  refine max_le (by linarith [le_max_left 0 (max (tinyEx P s M) (detPrice a0 a1 k P s M))])
    (max_le ?_ ?_)
  · linarith [le_max_left (tinyEx P s M) (detPrice a0 a1 k P s M),
      le_max_right 0 (max (tinyEx P s M) (detPrice a0 a1 k P s M))]
  · linarith [le_max_right (tinyEx P s M) (detPrice a0 a1 k P s M),
      le_max_right 0 (max (tinyEx P s M) (detPrice a0 a1 k P s M))]

/-- **Ledger form.** If the tiny-core excess is at most `c` and every class has a cutoff
with excess at most `c`, the HIGH price is at most `max 0 c`. -/
theorem highPriceF_le_of (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P s M c : ℝ}
    (ht : tinyEx P s M ≤ c)
    (h : ∀ p ∈ classes k, ∃ w ∈ cutoffs, detEx a0 a1 p.1 p.2 w P s M ≤ c) :
    highPriceF a0 a1 k P s M ≤ max 0 c :=
  max_le_max le_rfl (max_le ht (detPrice_le_of hk0 hk1 h))

/-- **Leaf form.** For every class and every `ε' > 0` there is a cutoff width whose excess is
within `ε'` of the HIGH price. -/
theorem exists_cutoff (hk0 : 0 ≤ k) {p : ℝ × ℝ} (hp : p ∈ classes k) (P s M : ℝ) {ε' : ℝ}
    (hε : 0 < ε') :
    ∃ w ∈ cutoffs, detEx a0 a1 p.1 p.2 w P s M < highPriceF a0 a1 k P s M + ε' := by
  have h1 := infW_le_detPrice (a0 := a0) (a1 := a1) hk0 hp P s M
  have h2 := detPrice_le_highPriceF a0 a1 k P s M
  exact exists_lt_infW (by linarith)

theorem tinyEx_P (P s M δ : ℝ) : tinyEx (P + δ) s M = tinyEx P s M + 3 / 4 * δ := by
  unfold tinyEx; ring

theorem tinyEx_s (P s M δ : ℝ) : tinyEx P (s + δ) M = tinyEx P s M + δ := by
  unfold tinyEx; ring

theorem tinyEx_M (P s M δ : ℝ) : tinyEx P s (M + δ) = tinyEx P s M - 5 / 6 * δ := by
  unfold tinyEx; ring

theorem highPriceF_mono (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P P' s s' : ℝ} (M : ℝ) (hP : P' ≤ P)
    (hs : s' ≤ s) : highPriceF a0 a1 k P' s' M ≤ highPriceF a0 a1 k P s M := by
  have := highPriceF_le_add (a0 := a0) (a1 := a1) (P := P) (s := s) (M := M) (P' := P')
    (s' := s') (M' := M) hk0 hk1 le_rfl (by unfold tinyEx; linarith) (fun p hp w hw => by
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have eP := detEx_P a0 a1 p.1 p.2 w P' s' M (P - P')
      rw [show P' + (P - P') = P by ring] at eP
      have hνP : 0 ≤ p.1 * (P - P') := mul_nonneg (hk0.trans h1) (by linarith)
      obtain ⟨l, -⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := p.1) (w := w) h3 P s' M (s - s')
        (by linarith)
      rw [show s' + (s - s') = s by ring] at l
      have := detEx_P a0 a1 p.1 p.2 w P' s' M (P - P')
      linarith)
  linarith

theorem highPriceF_lipP (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highPriceF a0 a1 k (P + δ) s M ≤ highPriceF a0 a1 k P s M + lipH a0 a1 * δ := by
  have hL := lipH_ge_one a0 a1
  refine highPriceF_le_add hk0 hk1 (by positivity) (by rw [tinyEx_P]; nlinarith)
    fun p hp w _ => ?_
  obtain ⟨h1, h2, -, -⟩ := hp
  rw [detEx_P]
  nlinarith

theorem highPriceF_lipS (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) (hδ : 0 ≤ δ) :
    highPriceF a0 a1 k P (s + δ) M ≤ highPriceF a0 a1 k P s M + lipH a0 a1 * δ := by
  have hL := lipH_ge_one a0 a1
  refine highPriceF_le_add hk0 hk1 (by positivity) (by rw [tinyEx_s]; nlinarith)
    fun p hp w _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨-, u⟩ := detEx_s (a0 := a0) (a1 := a1) (ν := p.1) (w := w) h3 P s M δ hδ
  have : p.2 * δ ≤ lipH a0 a1 * δ := by nlinarith
  linarith

theorem highPriceF_lipM (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (P s M δ : ℝ) :
    highPriceF a0 a1 k P s (M + δ) ≤ highPriceF a0 a1 k P s M + lipH a0 a1 * |δ| := by
  have hL := lipH_ge_one a0 a1
  refine highPriceF_le_add hk0 hk1 (by positivity) ?_ fun p hp w hw => ?_
  · rw [tinyEx_M]
    have := neg_abs_le δ
    nlinarith [abs_nonneg δ]
  · obtain ⟨h1, h2, h3, h4⟩ := hp
    have := detEx_M (a0 := a0) (a1 := a1) (hk0.trans h1) h2 h3 (h4.trans h2) hw P s M δ
    linarith [le_abs_self (detEx a0 a1 p.1 p.2 w P s (M + δ) - detEx a0 a1 p.1 p.2 w P s M)]

/-- Larger radius: for `ν ≥ 1/6` the excess decreases in `M` (both relative rates are `< 1`).
Used for ordinary children of radius `H' ≥ H`. -/
theorem highPriceF_antitoneM (hk0 : 1 / 6 ≤ k) (hk1 : k ≤ 3 / 4) (P s : ℝ) {M M' : ℝ}
    (hM : M ≤ M') : highPriceF a0 a1 k P s M' ≤ highPriceF a0 a1 k P s M := by
  have key : ∀ p ∈ classes k, ∀ w ∈ cutoffs,
      detEx a0 a1 p.1 p.2 w P s M' ≤ detEx a0 a1 p.1 p.2 w P s M + 0 := by
    intro p hp w hw
    obtain ⟨h1, h2, h3, h4⟩ := hp
    obtain ⟨hw1, hw2⟩ := hw
    unfold cutLo at hw1; unfold cutHi at hw2
    have hσ := sig_nonneg a0 a1 w
    rw [detEx_eq, detEx_eq]
    generalize sig a0 a1 w = σ at hσ ⊢
    have hmin : min s (M * σ) ≤ min s (M' * σ) :=
      min_le_min le_rfl (mul_le_mul_of_nonneg_right hM hσ)
    have hs : -(p.1 * M' * w) - p.2 * min s (M' * σ) ≤ -(p.1 * M * w) - p.2 * min s (M * σ) := by
      have : p.1 * M * w ≤ p.1 * M' * w := by
        have : 0 ≤ p.1 * w := mul_nonneg (by linarith) (by linarith)
        nlinarith
      nlinarith
    have hl : M' * (1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1) ≤
        M * (1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1) := by
      have hc : 1 / 6 + (5 / 6 - p.1) * (3 * w / 2 + 1 / 1000000) - 1 ≤ 0 := by nlinarith
      nlinarith
    have := max_le_max hs hl
    linarith
  have := highPriceF_le_add (a0 := a0) (a1 := a1) (P := P) (s := s) (M := M) (P' := P)
    (s' := s) (M' := M') (by linarith) hk1 le_rfl (by unfold tinyEx; linarith) key
  linarith

/-- The HIGH price as an exponential leaf price (`QRH.SilDensitySplit.CubeFree.Price`). The live
width argument is unused. -/
def highPrice (a0 a1 k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) :
    QRH.SilDensitySplit.CubeFree.Price where
  f _ P s M := highPriceF a0 a1 k P s M
  nonneg _ P s M := highPriceF_nonneg a0 a1 k P s M
  mono _ P P' s s' M hP hs := highPriceF_mono hk0 hk1 M hP hs
  lip := lipH a0 a1
  lip_nonneg := zero_le_one.trans (lipH_ge_one a0 a1)
  lipP _ P s M δ hδ := highPriceF_lipP hk0 hk1 P s M δ hδ
  lipS _ P s M δ hδ := highPriceF_lipS hk0 hk1 P s M δ hδ
  lipM _ P s M δ := highPriceF_lipM hk0 hk1 P s M δ

theorem highPrice_f (a0 a1 k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) (w P s M : ℝ) :
    (highPrice a0 a1 k hk0 hk1).f w P s M = highPriceF a0 a1 k P s M := rfl

end HighPrice

end
end Qrh.MarkedAnchor.High
