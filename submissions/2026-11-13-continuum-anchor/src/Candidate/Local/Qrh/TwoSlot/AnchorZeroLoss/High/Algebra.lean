/- Modified by Joseph Bebel (2026-11-12): coupled source/witness/detector
pads 1e-13, 1e-12, 1e-12 and HIGH reserve 3e-11. Generic price and
stage algebra only; the finite physical HIGH suppliers are separate.
Original notices and pinned PR137 attribution follow. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Price

/-!
# High.Algebra

The scalar inequalities of the HIGH child, as pure real inequalities parametrized by stage data.
No calculus: the derivative bound on the long-branch margin `G` is used in its difference form
`G ν - G k = (ν - k)·[…]`.

Stage data `d : Stg` = `(R, z, k, a0, a1, H)`: established anchor `(R, z_R)`, threshold `k`, line
`l(w) = a0 - a1 w`, relative radius `H = r/R`. Derived: `r = H R`, `u = (1-H)/6`,
`s = H S_R + u/k` with `S_R = (1-R)/2 + z_R`; `g ν = (r + s - H/2 - H a0 - u/ν)/(1/2 - a1)`,
`w ν = g ν / H + 10^-12`; the long-branch margin `G ν`; `w_b`, `F0`.

`Stg.Hyp` collects the stage gates used: `l(R) ≤ z_R`, `0 ≤ a1 ≤ 2/5`, `1/6 ≤ k ≤ 3/4`,
`H F0 > 3·10^-11` (gate 1), the derivative gate 9 (in the weak form `≥ 0`), gate 10 (tiny cores),
`w k ≥ 2/3` (gate 11), `w (3/4) ≤ 79/100` (gate 12).

Main results: `Stg.g_ge_r` (`g ν ≥ r`), `Stg.excess_B3` (short excess after pointwise payment),
`Stg.G_k` (`G k = H F0`), `Stg.G_mono` (`G` increasing), `Stg.short_le`, `Stg.long_le`,
`Stg.detEx_le`, `Stg.tiny_le` (tiny cores) and `Stg.highPriceF_le : highPriceF a0 a1 k r s H ≤ u`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section

/-- Stage data: anchor `(R, z)`, threshold `k`, line `(a0, a1)`, relative radius `H`. -/
structure Stg where
  R : ℝ
  z : ℝ
  k : ℝ
  a0 : ℝ
  a1 : ℝ
  H : ℝ

namespace Stg
variable (d : Stg)

/-- Free width `r = H R`. -/
def r : ℝ := d.H * d.R
/-- `u = (1-H)/6`. -/
def u : ℝ := (1 - d.H) / 6
/-- Child mark width `s = H S_R + u/k`. -/
def s : ℝ := d.H * ((1 - d.R) / 2 + d.z) + d.u / d.k
/-- `1/2 - a1`. -/
def D : ℝ := 1 / 2 - d.a1
/-- The short-branch width `g ν`. -/
def g (ν : ℝ) : ℝ := (d.r + d.s - d.H / 2 - d.H * d.a0 - d.u / ν) / d.D
/-- The relative cutoff width `w ν = g ν / H + 10^-12`. -/
def w (ν : ℝ) : ℝ := d.g ν / d.H + 1 / 1000000000000
/-- The long-branch margin. -/
def G (ν : ℝ) : ℝ := d.H + d.u - d.H / 6 - (5 / 6 - ν) * (3 * d.g ν / 2) - ν * (d.r + d.s)
/-- `w_b = (R/2 + z - a0)/(1/2 - a1)`. -/
def wb : ℝ := (d.R / 2 + d.z - d.a0) / d.D
/-- `F0`. -/
def F0 : ℝ := 5 / 6 - (5 / 4 - 3 * d.k / 2) * d.wb - d.k * (1 + d.R) / 2 - d.k * d.z
/-- Gate 9 without the `1/10`. -/
def gate9 : ℝ := d.r / 2 - d.s - 3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * d.k)) / d.D

/-- The stage gates used by the HIGH child. -/
structure Hyp (fee : ℝ := 3/100000000000) : Prop where
  R_pos : 0 < d.R
  H_pos : 0 < d.H
  H_le : d.H ≤ 1
  k_lo : 1 / 6 ≤ d.k
  k_hi : d.k ≤ 3 / 4
  a1_nonneg : 0 ≤ d.a1
  a1_le : d.a1 ≤ 2 / 5
  line : d.a0 - d.a1 * d.R ≤ d.z
  supply : 0 ≤ (1 - d.R) / 2 + d.z
  gF0 : fee < d.H * d.F0
  g9 : 0 ≤ d.gate9
  g10 : 3 / 100 < d.H + d.u - d.H / 6 - 1 / 15 - 3 / 4 * d.r - d.s
  g11 : cutLo ≤ d.w d.k
  g12 : d.w (3 / 4) ≤ cutHi

variable {d} {fee : ℝ}

theorem Hyp.D_pos (h : d.Hyp fee) : 1 / 10 ≤ d.D := by
  unfold D; linarith [h.a1_le]

theorem Hyp.k_pos (h : d.Hyp fee) : 0 < d.k := by linarith [h.k_lo]

theorem Hyp.u_nonneg (h : d.Hyp fee) : 0 ≤ d.u := by unfold u; linarith [h.H_le]

theorem Hyp.s_nonneg (h : d.Hyp fee) : 0 ≤ d.s := by
  unfold s
  have := mul_nonneg h.H_pos.le h.supply
  have := div_nonneg h.u_nonneg h.k_pos.le
  linarith

/-- Numerator identity: `(1/2 - a1)(g ν - r) = H (z - a0 + a1 R) + u (1/k - 1/ν)`. -/
theorem g_sub_r (h : d.Hyp fee) (ν : ℝ) :
    d.D * (d.g ν - d.r) = d.H * (d.z - d.a0 + d.a1 * d.R) + (d.u / d.k - d.u / ν) := by
  have hD : d.D ≠ 0 := by linarith [h.D_pos]
  unfold g
  rw [mul_sub, mul_div_cancel₀ _ hD]
  unfold r s D
  ring

/-- `g ν ≥ r` for `ν ≥ k`. -/
theorem g_ge_r (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) : d.r ≤ d.g ν := by
  have hk := h.k_pos
  have hD := h.D_pos
  have e := g_sub_r h ν
  have h1 : 0 ≤ d.H * (d.z - d.a0 + d.a1 * d.R) := mul_nonneg h.H_pos.le (by linarith [h.line])
  have h2 : d.u / ν ≤ d.u / d.k := div_le_div_of_nonneg_left h.u_nonneg hk hν
  have : 0 ≤ d.D * (d.g ν - d.r) := by rw [e]; linarith
  have := (mul_nonneg_iff_of_pos_left (by linarith : 0 < d.D)).mp this
  linarith

/-- `g` increases with `ν`. -/
theorem g_mono (h : d.Hyp fee) {ν ν' : ℝ} (hν : d.k ≤ ν) (hνν : ν ≤ ν') : d.g ν ≤ d.g ν' := by
  have hD := h.D_pos
  have hν0 : 0 < ν := lt_of_lt_of_le h.k_pos hν
  unfold g
  apply div_le_div_of_nonneg_right _ (by linarith)
  have : d.u / ν' ≤ d.u / ν := div_le_div_of_nonneg_left h.u_nonneg hν0 hνν
  linarith

theorem w_mono (h : d.Hyp fee) {ν ν' : ℝ} (hν : d.k ≤ ν) (hνν : ν ≤ ν') : d.w ν ≤ d.w ν' := by
  unfold w
  have := div_le_div_of_nonneg_right (g_mono h hν hνν) h.H_pos.le
  linarith

/-- The cutoff width of every HIGH class is an admissible cutoff (`1 < t < 3/2`). -/
theorem w_mem (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) (hν' : ν ≤ 3 / 4) : d.w ν ∈ cutoffs :=
  ⟨h.g11.trans (w_mono h le_rfl hν), (w_mono h hν hν').trans h.g12⟩

/-- `w ν ≥ R` (so the witness widths lie above the current stage). -/
theorem R_le_w (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) : d.R + 1 / 1000000000000 ≤ d.w ν := by
  have h1 := g_ge_r h hν
  unfold w
  have : d.R ≤ d.g ν / d.H := by
    rw [le_div_iff₀ h.H_pos]; unfold r at h1; linarith
  linarith

/-- The short excess after pointwise payment is `≤ 0` for every `e ≤ ν`. -/
theorem excess_B3 (h : d.Hyp fee) {ν e : ℝ} (hν : d.k ≤ ν) (he0 : 0 ≤ e) (he : e ≤ ν) :
    ν * (d.r - d.g ν) + e * (d.s - (d.H - d.g ν) / 2 - (d.H * d.a0 - d.a1 * d.g ν)) - d.u ≤ 0 := by
  have hν0 : 0 < ν := lt_of_lt_of_le h.k_pos hν
  have hD := h.D_pos
  have hdef : d.g ν * d.D = d.r + d.s - d.H / 2 - d.H * d.a0 - d.u / ν := by
    unfold g; field_simp [show d.D ≠ 0 by linarith]
  have hcoef : d.s - (d.H - d.g ν) / 2 - (d.H * d.a0 - d.a1 * d.g ν) = d.g ν - d.r + d.u / ν := by
    have : d.D = 1 / 2 - d.a1 := rfl
    rw [this] at hdef
    linarith
  rw [hcoef]
  have hzero : ν * (d.r - d.g ν) + ν * (d.g ν - d.r + d.u / ν) - d.u = 0 := by
    field_simp; ring
  have hc : 0 ≤ d.g ν - d.r + d.u / ν := by
    have := g_ge_r h hν
    have := div_nonneg h.u_nonneg hν0.le
    linarith
  have : e * (d.g ν - d.r + d.u / ν) ≤ ν * (d.g ν - d.r + d.u / ν) :=
    mul_le_mul_of_nonneg_right he hc
  linarith

/-- The supply covers the selection: `H σ(w ν) ≤ s`. -/
theorem sig_le_supply (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) : d.H * sig d.a0 d.a1 (d.w ν) ≤ d.s := by
  have hw := R_le_w h hν
  have hs := h.s_nonneg
  unfold sig
  rcases le_total 0 ((1 - d.w ν) / 2 + (d.a0 - d.a1 * d.w ν) - 1 / 10000000000000) with hX | hX
  · rw [max_eq_right hX]
    have h1 : (1 - d.w ν) / 2 + (d.a0 - d.a1 * d.w ν) - 1 / 10000000000000 ≤ (1 - d.R) / 2 + d.z := by
      have : d.a1 * d.R ≤ d.a1 * d.w ν := mul_le_mul_of_nonneg_left (by linarith) h.a1_nonneg
      linarith [h.line]
    have h2 : d.H * ((1 - d.R) / 2 + d.z) ≤ d.s := by
      unfold s; have := div_nonneg h.u_nonneg h.k_pos.le; linarith
    exact (mul_le_mul_of_nonneg_left h1 h.H_pos.le).trans h2
  · rw [max_eq_left hX, mul_zero]; exact hs

/-- Short branch: excess over `H + u` after the pointwise price is `≤ 0` (with the paddings). -/
theorem short_le (h : d.Hyp fee) {ν e : ℝ} (hν : d.k ≤ ν) (hν' : ν ≤ 3 / 4) (he0 : 0 ≤ e)
    (he : e ≤ ν) :
    ν * d.r + e * d.s + shortCnt d.a0 d.a1 ν e (d.w ν) d.s d.H - d.H ≤ d.u := by
  have hH := h.H_pos
  have hν0 : 0 < ν := lt_of_lt_of_le h.k_pos hν
  have hB3 := excess_B3 h hν he0 he
  set X := (1 - d.w ν) / 2 + (d.a0 - d.a1 * d.w ν) - 1 / 10000000000000 with hXdef
  have hmin : d.H * X ≤ min d.s (d.H * sig d.a0 d.a1 (d.w ν)) := by
    refine le_min ?_ ?_
    · refine le_trans ?_ (sig_le_supply h hν)
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) hH.le
    · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hH.le
  have hemin := mul_le_mul_of_nonneg_left hmin he0
  have hwdef : d.H * d.w ν = d.g ν + d.H / 1000000000000 := by
    unfold w; field_simp
  have hHX : d.H * X = (d.H - d.g ν) / 2 + (d.H * d.a0 - d.a1 * d.g ν)
      - d.H * ((1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000) := by
    rw [hXdef]
    have : d.H * ((1 - d.w ν) / 2 + (d.a0 - d.a1 * d.w ν) - 1 / 10000000000000) =
        d.H / 2 - (d.H * d.w ν) / 2 + d.H * d.a0 - d.a1 * (d.H * d.w ν) - d.H / 10000000000000 := by ring
    rw [this, hwdef]; ring
  unfold shortCnt
  have hpad : ν * (d.H / 1000000000000) ≥ e * (d.H * ((1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000)) := by
    have ha := h.a1_le
    have h1 : e * (d.H * ((1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000)) ≤
        ν * (d.H * ((1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000)) :=
      mul_le_mul_of_nonneg_right he (mul_nonneg hH.le (add_nonneg
        (div_nonneg (by linarith [h.a1_nonneg]) (by norm_num)) (by norm_num)))
    have h2 : (1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000 ≤ 1 / 1000000000000 := by linarith
    have h3 : ν * (d.H * ((1 / 2 + d.a1) / 1000000000000 + 1 / 10000000000000)) ≤ ν * (d.H / 1000000000000) := by
      apply mul_le_mul_of_nonneg_left _ hν0.le
      have := mul_le_mul_of_nonneg_left h2 hH.le
      linarith
    linarith
  have hνHw : ν * d.H * d.w ν = ν * (d.g ν + d.H / 1000000000000) := by rw [mul_assoc, hwdef]
  rw [hνHw]
  rw [hHX] at hemin
  nlinarith

/-- `G k = H F0`. -/
theorem G_k (h : d.Hyp fee) : d.G d.k = d.H * d.F0 := by
  have hk := h.k_pos
  have hD : d.D ≠ 0 := by linarith [h.D_pos]
  have hg : d.g d.k = d.H * d.wb := by
    unfold g wb
    rw [mul_div_assoc']
    congr 1
    unfold r s
    field_simp
    ring
  unfold G F0
  rw [hg]
  unfold r s
  field_simp
  ring

/-- The derivative bound in difference form: `G ν - G k = (ν - k)·(3g ν/2 - (3/2)(5/6-k) u/(k ν D) - (r+s))`. -/
theorem G_sub (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) :
    d.G ν - d.G d.k = (ν - d.k) *
      (3 * d.g ν / 2 - 3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * ν * d.D)) - (d.r + d.s)) := by
  have hk := h.k_pos
  have hν0 : 0 < ν := lt_of_lt_of_le hk hν
  have hD : d.D ≠ 0 := by linarith [h.D_pos]
  have hgg : d.g ν - d.g d.k = (d.u / d.k - d.u / ν) / d.D := by
    unfold g; field_simp; ring
  have hfrac : (d.u / d.k - d.u / ν) / d.D = (ν - d.k) * (d.u / (d.k * ν * d.D)) := by
    field_simp
  have hG : d.G ν - d.G d.k = 3 / 2 * ((ν - d.k) * d.g ν + (d.k - 5 / 6) * (d.g ν - d.g d.k))
      - (ν - d.k) * (d.r + d.s) := by
    unfold G; ring
  rw [hG, hgg, hfrac]; ring

/-- `G ν ≥ G k` on `[k, 3/4]` (gate 9). -/
theorem G_mono (h : d.Hyp fee) {ν : ℝ} (hν : d.k ≤ ν) (hν' : ν ≤ 3 / 4) : d.G d.k ≤ d.G ν := by
  have hk := h.k_pos
  have hν0 : 0 < ν := lt_of_lt_of_le hk hν
  have hDp : 0 < d.D := by linarith [h.D_pos]
  rw [← sub_nonneg, G_sub h hν]
  apply mul_nonneg (by linarith)
  have hg := g_ge_r h hν
  have hfr : d.u / (d.k * ν * d.D) ≤ d.u / (d.k * d.k) / d.D := by
    rw [div_div]
    apply div_le_div_of_nonneg_left h.u_nonneg (by positivity)
    have : d.k * d.k ≤ d.k * ν := mul_le_mul_of_nonneg_left hν hk.le
    nlinarith
  have hc : 0 ≤ 5 / 6 - d.k := by linarith [h.k_hi]
  have := mul_le_mul_of_nonneg_left hfr (show 0 ≤ 3 / 2 * (5 / 6 - d.k) by positivity)
  have h9 := h.g9
  unfold gate9 at h9
  have e1 : 3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * d.k)) / d.D =
      3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * d.k) / d.D) := by ring
  rw [e1] at h9
  have e2 : 3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * ν * d.D)) =
      3 / 2 * (5 / 6 - d.k) * (d.u / (d.k * ν * d.D)) := rfl
  nlinarith

/-- Long branch: excess over `H + u` is at most `-(3·10^-11 - 2.5·10^-12)`. -/
theorem long_le (h : d.Hyp) {ν e : ℝ} (hν : d.k ≤ ν) (hν' : ν ≤ 3 / 4) (he0 : 0 ≤ e)
    (he : e ≤ ν) :
    ν * d.r + e * d.s + longCnt ν (d.w ν) d.H - d.H ≤ d.u - 11 / 400000000000 := by
  have hH := h.H_pos
  have hGk := G_k h
  have hGm := G_mono h hν hν'
  have hF := h.gF0
  have hes : e * d.s ≤ ν * d.s := mul_le_mul_of_nonneg_right he h.s_nonneg
  have hwdef : d.H * d.w ν = d.g ν + d.H / 1000000000000 := by
    unfold w; field_simp
  have hL : longCnt ν (d.w ν) d.H =
      d.H / 6 + (5 / 6 - ν) * (3 * d.g ν / 2) + (5 / 6 - ν) * d.H * (5 / 2000000000000) := by
    unfold longCnt
    simp only [WitnessShift.value, fixedWitnessShift]
    have : (5 / 6 - ν) * d.H * (3 * d.w ν / 2 + 1 / 1000000000000) =
        (5 / 6 - ν) * (3 / 2 * (d.H * d.w ν) + d.H / 1000000000000) := by ring
    rw [this, hwdef]; ring
  rw [hL]
  have hG : d.G ν = d.H + d.u - d.H / 6 - (5 / 6 - ν) * (3 * d.g ν / 2) - ν * (d.r + d.s) := rfl
  have hpad : (5 / 6 - ν) * d.H * (5 / 2000000000000) ≤ 1 / 400000000000 := by
    have : (5 / 6 - ν) * d.H ≤ 1 := by nlinarith [h.H_le]
    nlinarith
  nlinarith

/-- The detector excess of every HIGH class at its cutoff `w ν` is at most `u`. -/
theorem detEx_le (h : d.Hyp) {ν e : ℝ} (hν : d.k ≤ ν) (hν' : ν ≤ 3 / 4) (he0 : 0 ≤ e)
    (he : e ≤ ν) : detEx d.a0 d.a1 ν e (d.w ν) d.r d.s d.H ≤ d.u := by
  have h1 := short_le h hν hν' he0 he
  have h2 := long_le h hν hν' he0 he
  unfold detEx
  rcases le_total (shortCnt d.a0 d.a1 ν e (d.w ν) d.s d.H) (longCnt ν (d.w ν) d.H) with hm | hm
  · rw [max_eq_right hm]; linarith
  · rw [max_eq_left hm]; linarith

/-- Tiny cores (gate 10). -/
theorem tiny_le (h : d.Hyp) : tinyEx d.r d.s d.H ≤ d.u - 3 / 100 := by
  have := h.g10
  unfold tinyEx
  linarith

/-- **The HIGH price of the stage is at most `u`.** -/
theorem highPriceF_le (h : d.Hyp) : highPriceF d.a0 d.a1 d.k d.r d.s d.H ≤ d.u := by
  have hk0 : 0 ≤ d.k := h.k_pos.le
  have := highPriceF_le_of (a0 := d.a0) (a1 := d.a1) hk0 h.k_hi
    ((tiny_le h).trans (by linarith)) (fun p hp => ⟨d.w p.1, w_mem h hp.1 hp.2.1,
      detEx_le h hp.1 hp.2.1 hp.2.2.1 hp.2.2.2⟩)
  exact this.trans (max_le h.u_nonneg le_rfl)

end Stg

end
end Qrh.TwoSlot.AnchorZeroLoss.High
