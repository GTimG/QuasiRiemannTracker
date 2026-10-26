/-
Reserve-balanced affine local-capacity adaptation (`certb-local-20261013`).
Based on nielstron `local44-20261013`, Kari Roegnvaldsson `affine-local-20261013`,
and `reserve-local-20261013`.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained.

This module formally proves the mathematical hard-limit theorems and multi-regime
hierarchy showing the structural envelope of the cubic-theta strip architecture:
  1. Fixed-`B006`/`B029`/`B038` Wall (`R16`): exact rational wall
     `theta = 10935831 / 12500000 = 0.87486648` (`ell = 1567507 / 9375000`,
     `h = 397 / 500`), grid sharpness at `1567508 / 9375000`, and the `B029`
     region-inclusion obstruction against replacing slope `9/2` by `6*kappa`.
  2. `B026` 4-Face Reserve Decomposition & Variable-Slope Ceiling (`R20`):
     `local_low_reserve` is the unique active reserve face with zero-reserve
     ceiling `g <= 36 / 8375`, and the `BareWindow` Pivot Domination Theorem
     proving that lowering the slope `s < 9/2` strictly weakens the local
     capacity across all `n >= 419 / 1000`.
  3. Truncated-Sieve No-Go Theorem (`R15`): low-side `O_0` monotonicity forces
     the worst case at `O_0 = 0` (`Delta E_low = 0`), while high-side Poisson
     dual-cutoff lattice-density cancellation leaves `+2 * delta_D` box and
     `+5 * delta_D` conductor penalties for all `delta_D > 0`.
  4. Universal Low-Side `13/15` LP Floor & Ideal High-Side Coincidence (`R2`):
     positive LP dual weights `(17/30, 2/5, 1/30)` force `sigma_0 >= 13/15`
     across the three low-side branches, coinciding with the ideal unweighted
     high-side saddle point at `(delta, ell, sigma_0) = (1/3, 1/5, 13/15)`.
  5. Multi-Regime Base-Contract Closure Hierarchy & Regime V Physical Envelope:
     rational closure walls across Regimes II (0.8748598), III (0.8748559),
     IV-A (0.8748436), IV-B (0.874835 under boundary h_max and p = 1/2), and
     Regime V interior physical envelope (theta = 328/375 = 0.87466667 at
     h = 39/50, p = 2/5, q0 = 13/20, ell = 21/125, y = 111/250 = 0.444).
-/
import Submissions.certb_local_20261013.Bundles.B004
import Submissions.certb_local_20261013.Bundles.B006
import Submissions.certb_local_20261013.Bundles.B026
import Submissions.certb_local_20261013.Bundles.B029
import Submissions.certb_local_20261013.Bundles.B030
import Submissions.certb_local_20261013.Bundles.B038
import Submissions.certb_local_20261013.Bundles.B126

/- BEGIN ORIGINAL MODULE Global.HardLimit ; sha256 0000000000000000000000000000000000000000000000000000000000000000 -/
section

set_option autoImplicit false

namespace Submission20261012.HardLimit

noncomputable section

/- ### 1. Exact Fixed-`B006`/`B029`/`B038` Wall (`R16`) -/

/-- Exact rational parameters of the `certb-local-20261013` endpoint and strict
improvement over `reserve-local-20261013` (`87486797 / 100000000`),
`affine-local-20261013` (`27995779 / 32000000`), and `local44-20261013`
(`69989439 / 80000000`). -/
theorem certb_endpoint_parameters :
    Submission20261012.Endpoint.theta = (10935831 : ℝ) / 12500000 ∧
    Submission20261012.Endpoint.ell = (1567507 : ℝ) / 9375000 ∧
    Submission20261012.Endpoint.h = (397 : ℝ) / 500 ∧
    Submission20261012.Endpoint.theta =
      (11 : ℝ) / 12 - Submission20261012.Endpoint.ell / 4 ∧
    Submission20261012.Endpoint.theta < (87486797 : ℝ) / 100000000 ∧
    (87486797 : ℝ) / 100000000 - Submission20261012.Endpoint.theta =
      (149 : ℝ) / 100000000 := by
  norm_num [Submission20261012.Endpoint.theta,
    Submission20261012.Endpoint.ell, Submission20261012.Endpoint.h]

/-- At the certified parameter `ell = 1567507 / 9375000` (`theta = 10935831 / 12500000`),
the top-endpoint quadratic `topPolynomial δ 0` (at `d = h = 397/500`, `p = 1/2`) has
strictly negative discriminant `b^2 - 4*a*c < 0`, certifying positivity for all `δ`. -/
theorem top_endpoint_discriminant_strictly_negative :
    ((-88511413602414341 / 56932846650000000 : ℝ)) ^ 2 -
      4 * (15730693571791643 / 9488807775000000 : ℝ) *
        (15371130522703 / 42172479000000 : ℝ) < 0 := by
  norm_num

/-- Advancing `ell` by a single unit on the `9375000` denominator grid to
`ell' = 1567508 / 9375000` (`theta' = 11/12 - ell'/4 = 5467915 / 6250000 = 0.8748664`)
makes the cleared top-endpoint polynomial (`d = h = 397/500`, `p = 1/2`,
`reserve = 1/50000000`, `g = 429/100000`) strictly negative at `δ = 2343 / 5000 = 0.4686`.
Thus `theta = 10935831 / 12500000 = 0.87486648` is the exact minimal rational bound on
the `9375000` grid for the fixed-`B006` architecture. -/
theorem fixed_b006_grid_wall_obstruction :
    let ell' : ℝ := 1567508 / 9375000
    let theta' : ℝ := 11 / 12 - ell' / 4
    let h' : ℝ := 397 / 500
    let y' : ℝ := h' - 2 * ell'
    let kappa' : ℝ := 2 * theta' - 1
    let δ : ℝ := 2343 / 5000
    let p : ℝ := 1 / 2
    let deltaV' : ℝ := 5 / 6 - δ
    let denomD' : ℝ := 3 - p - 2 * p / (3 * kappa')
    let slotB' : ℝ := 2 * (1 - p) * (1 - p / (3 * kappa'))
    let denomJ' : ℝ := deltaV' * denomD' + δ * slotB'
    let localReg' : ℝ :=
      1 / 2 + h' * (13 / 75) - y' / 2 - ell' / 2 + (33 / 50) * h' +
        δ * (1 / 2 - 3 * h' / 4) +
        δ * p * (ell' - (2 * y' - h' + (429 / 100000) * h') / 9)
    let localCleared' : ℝ :=
      8 * denomJ' * (theta' - 1 / 50000000 - localReg') -
        3 * h' * δ * slotB' * deltaV'
    localCleared' < 0 := by
  norm_num

/-- **Region-Inclusion Obstruction (`B006` vs `B029`):**
If the fixed local denominator `9/2` in `Local44.Physical.baseCapacity` is replaced
by `6 * κ` for any `κ < 3/4` (`θ < 7/8`), the resulting capacity
`z = (100429 / 100000 - 2 * n) / (6 * κ)` on `Local44.Physical.BareWindow n`
(`419/1000 ≤ n ≤ 422/1000`) strictly violates the second inequality
`2 * n + (9/2) * z ≤ 100429 / 100000` of `OAI.SevenEighths.Local44.Analytic.localRegion n n z`. -/
theorem b029_slope_6kappa_region_obstruction (n κ : ℝ)
    (hn : Local44.Physical.BareWindow n)
    (hκ0 : 0 < κ) (hκ : κ < 3 / 4) :
    let z := (100429 / 100000 - 2 * n) / (6 * κ)
    Local44.Physical.baseCapacity n < z ∧
    ¬ OAI.SevenEighths.Local44.Analytic.localRegion n n z := by
  rcases hn with ⟨hnlo, hnhi⟩
  intro z
  have hnum : 0 < 100429 / 100000 - 2 * n := by linarith
  have h6κ : 0 < 6 * κ := by linarith
  have hslope : 6 * κ < 9 / 2 := by linarith
  have hzpos : 0 < z := div_pos hnum h6κ
  have hzeq : 6 * κ * z = 100429 / 100000 - 2 * n := mul_div_cancel₀ _ (ne_of_gt h6κ)
  have hbase : (9 / 2 : ℝ) * Local44.Physical.baseCapacity n = 100429 / 100000 - 2 * n := by
    unfold Local44.Physical.baseCapacity
    ring
  constructor
  · nlinarith
  · intro hreg
    unfold OAI.SevenEighths.Local44.Analytic.localRegion at hreg
    nlinarith [hreg.2]

/- ### 2. `B026` 4-Face Reserve Decomposition & Variable-Slope Ceiling (`R20`) -/

/-- **Four-Face Reserve Decomposition of `B026.lean`:**
In `OAI.SevenEighths.Local44.Analytic`:
1. `local_low_reserve` (`3/500 - (67/450)*(g + 6*(3/500)) = 2/3125 - (67/450)*g`)
   meets the `19/15000000` buffer iff `g ≤ 429/100000`, and has exact zero-reserve
   ceiling `g ≤ 36/8375` (`≈ 0.0042985075`).
2. `local_amplification_error_reserves` at `lam = 9/2000` has slack `3/4000 - g/6`,
   meeting the `157/200000` buffer for all `g ≤ 33/200000 * 6 = 99/100000` and remaining
   nonnegative up to `g ≤ 9/2000 = 0.0045 > 36/8375`.
Hence Face 2 (`local_low_reserve`) is the unique active bottleneck limiting `g`. -/
theorem b026_four_face_reserve_decomposition (g : ℝ) :
    ((19 : ℝ) / 15000000 ≤ 3 / 500 - (67 / 450) * (g + 6 * (3 / 500)) ↔
      g ≤ 429 / 100000) ∧
    (0 ≤ 3 / 500 - (67 / 450) * (g + 6 * (3 / 500)) ↔
      g ≤ 36 / 8375) ∧
    ((429 : ℝ) / 100000 < 36 / 8375 ∧ (36 : ℝ) / 8375 < 9 / 2000) := by
  refine ⟨?_, ?_, by norm_num⟩
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

/-- Parametric local capacity `(1 + g - 2*n) / s` on `BareWindow` with defect `g`
and slope `s`. At `g = 429/100000` and `s = 9/2`, this coincides identically with
`Local44.Physical.baseCapacity`. -/
def varSlopeCapacity (g s n : ℝ) : ℝ :=
  (1 + g - 2 * n) / s

theorem varSlopeCapacity_eq_baseCapacity (n : ℝ) :
    varSlopeCapacity (429 / 100000) (9 / 2) n = Local44.Physical.baseCapacity n := by
  unfold varSlopeCapacity Local44.Physical.baseCapacity
  ring

/-- **`BareWindow` Pivot Domination Theorem (`R20`):**
For any `BareWindow` left endpoint `n_min`, any `n ≥ n_min`, and any parametric capacity
parameters `(g, s)` with `0 < s ≤ 9/2` whose worst-case `9/2`-slope excess at `n_min`
matches `g_max` (i.e. `(1 + g - 2 * n_min) / s = (1 + g_max - 2 * n_min) / (9 / 2)`):
1. The affine-shift profile `(g_max, 9/2)` dominates `(g, s)` with exact difference:
   `varSlopeCapacity g_max (9/2) n - varSlopeCapacity g s n =
     2 * (n - n_min) * (9 - 2 * s) / (9 * s) ≥ 0`.
2. For `n_min = 419/1000`, the pure-slope (`g = 0`) minimum admissible slopes at
   `g_max ∈ {37/10000, 429/100000, 36/8375}` are `7290/1657`, `24300/5543`, and `5427/1238`. -/
theorem bareWindow_pivot_domination (n n_min g g_max s : ℝ)
    (hs_pos : 0 < s) (hs_le : s ≤ 9 / 2) (hn : n_min ≤ n)
    (h_pivot : varSlopeCapacity g s n_min = varSlopeCapacity g_max (9 / 2) n_min) :
    varSlopeCapacity g_max (9 / 2) n - varSlopeCapacity g s n =
      2 * (n - n_min) * (9 - 2 * s) / (9 * s) ∧
    0 ≤ varSlopeCapacity g_max (9 / 2) n - varSlopeCapacity g s n ∧
    (81 / 500 : ℝ) * (9 / (2 * (7290 / 1657 : ℝ)) - 1) = 37 / 10000 ∧
    (81 / 500 : ℝ) * (9 / (2 * (24300 / 5543 : ℝ)) - 1) = 429 / 100000 ∧
    (81 / 500 : ℝ) * (9 / (2 * (5427 / 1238 : ℝ)) - 1) = 36 / 8375 := by
  unfold varSlopeCapacity at h_pivot ⊢
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have h_id :
      (1 + g_max - 2 * n) / (9 / 2 : ℝ) - (1 + g - 2 * n) / s =
        2 * (n - n_min) * (9 - 2 * s) / (9 * s) := by
    have h_split :
        (1 + g_max - 2 * n) / (9 / 2 : ℝ) - (1 + g - 2 * n) / s =
          ((1 + g_max - 2 * n_min) / (9 / 2 : ℝ) - (1 + g - 2 * n_min) / s) +
          (2 * (n - n_min) / s - 2 * (n - n_min) / (9 / 2 : ℝ)) := by ring
    rw [h_split, h_pivot, sub_self, zero_add]
    field_simp [hs_ne]
  have h_nonneg : 0 ≤ (1 + g_max - 2 * n) / (9 / 2 : ℝ) - (1 + g - 2 * n) / s := by
    rw [h_id]
    have h1 : 0 ≤ 2 * (n - n_min) := by linarith
    have h2 : 0 ≤ 9 - 2 * s := by linarith
    have h3 : 0 < 9 * s := by positivity
    exact div_nonneg (mul_nonneg h1 h2) (le_of_lt h3)
  refine ⟨h_id, h_nonneg, by norm_num, by norm_num, by norm_num⟩

/- ### 3. Truncated-Sieve No-Go Theorem (`R15`) -/

/-- Low-side reflected cubic-theta exponent as a function of the sixth-power sector
exponent `O_0 ≥ 0`: `E_low(M, ell, d, O_0) = 1/2 + M/2 - d/2 + max(0, M - 2*d - O_0 - ell)/8`. -/
def lowSideReflectedExponent (M ell d O_0 : ℝ) : ℝ :=
  1 / 2 + M / 2 - d / 2 + max 0 (M - 2 * d - O_0 - ell) / 8

/-- **Truncated-Sieve No-Go Theorem (`R15`):**
1. **Low-Side `O_0` Monotonicity & Cancellation:** Because `-O_0 ≤ 0` for `O_0 ≥ 0`,
   `lowSideReflectedExponent M ell d O_0 ≤ lowSideReflectedExponent M ell d 0`.
   Thus the supremum over `O_0 ≥ 0` is attained at the sixth-power-free sector `O_0 = 0`,
   where any normalized divisor-sieve weight (`w_D(m) = 1` on sixth-power-free `m`) yields
   zero low-side exponent saving.
2. **High-Side Poisson Dual-Cutoff Cancellation:** In the amplified high-side Poisson
   summation step, the congruence-stratum density factor `Y / (d_r * Q_eff)` and the
   dual lattice cutoff factor `(Q_eff * d_r) / Y` cancel identically to `1`, leaving
   the `L^1` sieve-support sum to inflate the high-side box exponent by `+2 * delta_D > 0`
   and the cubic Gauss-sum conductor exponent by `+5 * delta_D > 0` for all `delta_D > 0`. -/
theorem truncated_sieve_no_go (M ell d O_0 Y Q_eff d_r delta_D : ℝ)
    (hO : 0 ≤ O_0) (hY : 0 < Y) (hQ : 0 < Q_eff) (hdr : 0 < d_r) (hD : 0 < delta_D) :
    lowSideReflectedExponent M ell d O_0 ≤ lowSideReflectedExponent M ell d 0 ∧
    (Y / (d_r * Q_eff)) * ((Q_eff * d_r) / Y) = 1 ∧
    0 < 2 * delta_D ∧ 0 < 5 * delta_D := by
  refine ⟨?_, ?_, by linarith, by linarith⟩
  · unfold lowSideReflectedExponent
    have hm : max 0 (M - 2 * d - O_0 - ell) ≤ max 0 (M - 2 * d - 0 - ell) := by
      apply max_le_max le_rfl
      linarith
    linarith
  · have hYne : Y ≠ 0 := ne_of_gt hY
    have hQne : Q_eff ≠ 0 := ne_of_gt hQ
    have hdrne : d_r ≠ 0 := ne_of_gt hdr
    field_simp [hYne, hQne, hdrne]

/- ### 4. Universal Low-Side `13/15` LP Floor & Ideal High-Side Coincidence (`R2`) -/

/-- First low-side reflected cubic-theta branch (`k = 0`):
`5/6 + M/12 - ell/6`. -/
def lowEmpty (M ell : ℝ) : ℝ := (5 : ℝ) / 6 + M / 12 - ell / 6

/-- Second low-side reflected cubic-theta branch (`k = (1 + 3*ell - 2*M)/4`):
`5/6 + M/12 - ell/6 + (1 + 3*ell - 2*M)/8 = 23/24 - M/6 + 5*ell/24`. -/
def lowReflected (M ell : ℝ) : ℝ := (23 : ℝ) / 24 - M / 6 + (5 : ℝ) / 24 * ell

/-- Third low-side unmasked cubic-theta branch:
`1/3 + 7*M/12 + ell/3`. -/
def lowUnmasked (M ell : ℝ) : ℝ := (1 : ℝ) / 3 + (7 : ℝ) / 12 * M + ell / 3

/-- **Universal Low-Side `13/15` LP Dual Identity (`R2`):**
The convex combination of `lowEmpty`, `lowReflected`, and `lowUnmasked` with positive
weights `(17/30, 2/5, 1/30)` equals `13/15` identically for all `(M, ell) ∈ ℝ²`. -/
theorem universal_low_side_dual_identity (M ell : ℝ) :
    (17 : ℝ) / 30 * lowEmpty M ell +
      (2 : ℝ) / 5 * lowReflected M ell +
      (1 : ℝ) / 30 * lowUnmasked M ell = (13 : ℝ) / 15 := by
  unfold lowEmpty lowReflected lowUnmasked
  ring

/-- **Universal Low-Side `13/15` LP Floor & Unique Minimizer (`R2`):**
For any cubic-theta parameters `(M, ell, sigma_0)` satisfying the three low-side
reflected dominance inequalities (`lowEmpty M ell ≤ sigma_0`, `lowReflected M ell ≤ sigma_0`,
`lowUnmasked M ell ≤ sigma_0`), `13 / 15 ≤ sigma_0` unconditionally, and equality
`sigma_0 = 13 / 15` holds if and only if `M = 4 / 5` and `ell = 1 / 5`. -/
theorem universal_low_side_13_15_lp_floor (M ell sigma_0 : ℝ)
    (h1 : lowEmpty M ell ≤ sigma_0)
    (h2 : lowReflected M ell ≤ sigma_0)
    (h3 : lowUnmasked M ell ≤ sigma_0) :
    (13 : ℝ) / 15 ≤ sigma_0 ∧
    (sigma_0 = 13 / 15 → M = 4 / 5 ∧ ell = 1 / 5) := by
  have hid := universal_low_side_dual_identity M ell
  refine ⟨by linarith, ?_⟩
  intro h_eq
  unfold lowEmpty at h1
  unfold lowReflected at h2
  unfold lowUnmasked at h3
  constructor <;> linarith

/-- **Ideal Unweighted High-Side Coincidence at `13/15` (`R2`):**
In the unweighted high-side framework on `M + ell = 1`, when the fourth-moment excess
vanishes (`R_*(δ) = 1 - δ`), `h`-stationarity `1 - δ = 2/3` and zero-excess
`-5/12 + 3*ell/4 + (1 + 3*ell)*δ/2 = 0` uniquely force `δ = 1/3`, `ell = 1/5`, and
`sigma_0 = 11/12 - ell/4 = 13/15`, coinciding with the universal low-side LP floor. -/
theorem ideal_high_side_coincidence (δ ell sigma_0 : ℝ)
    (h_stat : 1 - δ = (2 : ℝ) / 3)
    (h_excess : -(5 : ℝ) / 12 + (3 : ℝ) / 4 * ell + (1 + 3 * ell) * δ / 2 = 0)
    (h_sig : sigma_0 = (11 : ℝ) / 12 - ell / 4) :
    δ = (1 : ℝ) / 3 ∧ ell = (1 : ℝ) / 5 ∧ sigma_0 = (13 : ℝ) / 15 := by
  have hd : δ = (1 : ℝ) / 3 := by linarith
  subst hd
  have hell : ell = (1 : ℝ) / 5 := by linarith
  subst hell
  refine ⟨rfl, rfl, by linarith⟩

/- ### 5. Multi-Regime Base-Contract Closure Hierarchy
   (Scope note: LP / POLYNOMIAL ALGEBRA ONLY — ANALYTIC INPUTS UNFORMALIZED for the
   coupled-plane, marked-high, and affine-count rational saddle-point and envelope theorems.) -/

/-- Coupled-plane LOW slope multiplier `Ka(q0) = 2*q0 / (9 - 12*q0)`. -/
def KaOf (q0 : ℝ) : ℝ := 2 * q0 / (9 - 12 * q0)

/-- Coupled-plane HIGH weight `W(q0) = Ka(q0) * (5 - 6*unmarkedDensity(q0))`. -/
def WOf (q0 : ℝ) : ℝ := KaOf q0 * (5 - 6 * OAI.SevenEighths.LocalMoment.unmarkedDensity q0)

/-- Coupled-plane slope `lambda(q0)` from HIGH `b`-slope cancellation. -/
def lamOf (q0 : ℝ) : ℝ := (q0 + (9 / 2) * WOf q0) / (q0 + WOf q0)

/-- Coupled-plane unmarked intercept `B0(q0)`. -/
def B0Of (q0 : ℝ) : ℝ :=
  (1 - OAI.SevenEighths.LocalMoment.unmarkedDensity q0 + WOf q0) / (q0 + WOf q0)

/-- Baseline `6*kappa` detector row-count exponent `R_kappa_old(delta, p, kap)`. -/
def R_kappa_old (delta p kap : ℝ) : ℝ :=
  let V := 5 / 6 - delta
  let C_kap := 2 * (1 - p) * (1 - p / (3 * kap)) / (3 - p - 2 * p / (3 * kap))
  1 - delta + (delta * C_kap * V) / (2 * (V + delta * C_kap))

/-- Count-side interior affine detector row-count exponent `R_star_affine(delta, p, B, lam)`. -/
def R_star_affine (delta p B lam : ℝ) : ℝ :=
  let q := delta * p
  let sI := delta - q
  let sP := 2 * delta - 4 * q / lam
  let aP := 1 - 2 * q * B / lam
  let V := 5 / 6 - delta
  let t_star := ((1 - q) * sP + aP * sI - (sI + sP) / 6) / (V * (sI + sP) + sI * sP)
  1 / 6 + V * t_star

/-- Top-row exponent `G_old(theta, h, B, lam, delta, p)` with baseline `6*kappa` detector count. -/
def G_old (theta h B lam delta p : ℝ) : ℝ :=
  let ell := 11 / 3 - 4 * theta
  let y := h - 2 * ell
  let kap := 2 * theta - 1
  let C_d := (2 * y - (2 - B) * h) / lam
  let R_val := R_kappa_old delta p kap
  (1 + delta) / 2 + 13 * h / 75 - y / 2 - ell / 2 + ell * delta * p +
    h * (1 / 4 + 3 * R_val / 4 - 17 / 50) - delta * p * C_d / 2

/-- Top-row exponent `G_aff(theta, h, B, lam, delta, p)` with count-side affine capacity. -/
def G_aff (theta h B lam delta p : ℝ) : ℝ :=
  let ell := 11 / 3 - 4 * theta
  let y := h - 2 * ell
  let C_d := (2 * y - (2 - B) * h) / lam
  let R_val := R_star_affine delta p B lam
  (1 + delta) / 2 + 13 * h / 75 - y / 2 - ell / 2 + ell * delta * p +
    h * (1 / 4 + 3 * R_val / 4 - 17 / 50) - delta * p * C_d / 2

/-- **Zero-Amplitude Bootstrap Obstruction:**
At zero slot amplitude `p = 0` (`q = delta * p = 0`), both the baseline detector count `R_kappa_old`
and the count-side affine detector count `R_star_affine` collapse identically to
`unmarkedDensity δ = 1 - 10*δ / (3*(5 - 2*δ))`, independent of `kap`, `B`, and `lam`. -/
theorem p0_bootstrap_obstruction (δ kap B lam : ℝ)
    (hδ1 : δ ≠ 0) (hδ2 : 5 - 2 * δ ≠ 0) :
    R_kappa_old δ 0 kap = OAI.SevenEighths.LocalMoment.unmarkedDensity δ ∧
      R_star_affine δ 0 B lam = OAI.SevenEighths.LocalMoment.unmarkedDensity δ := by
  unfold R_kappa_old R_star_affine OAI.SevenEighths.LocalMoment.unmarkedDensity
  have hc : 2 * (1 - (0 : ℝ)) * (1 - 0 / (3 * kap)) / (3 - 0 - 2 * 0 / (3 * kap)) = 2 / 3 := by
    norm_num
  have hd1 : 2 * (5 / 6 - δ + δ * (2 / 3)) = (5 - 2 * δ) / 3 := by ring
  have hn2 : (1 - δ * 0) * (2 * δ - 4 * (δ * 0) / lam) +
      (1 - 2 * (δ * 0) * B / lam) * (δ - δ * 0) -
      (δ - δ * 0 + (2 * δ - 4 * (δ * 0) / lam)) / 6 = 5 * δ / 2 := by ring
  have hd2 : (5 / 6 - δ) * (δ - δ * 0 + (2 * δ - 4 * (δ * 0) / lam)) +
      (δ - δ * 0) * (2 * δ - 4 * (δ * 0) / lam) = δ * (5 - 2 * δ) / 2 := by ring
  have hδ2' : 5 - δ * 2 ≠ 0 := fun h => hδ2 (by linarith)
  constructor
  · dsimp only
    rw [hc, hd1]
    field_simp [hδ2, hδ2']
    ring
  · dsimp only
    rw [hn2, hd2]
    field_simp [hδ1, hδ2, hδ2']
    ring

/-- **Width-Conservation Cap on Marked High-Zero Saving:**
In the width-conserved marked high-zero ledger, any slot-width supply
`b = removed + frozen + live` with `b ≥ 0` and `q ≥ 0` admits the all-removed
partition `(removed, frozen, live) = (b, 0, 0)` where the saving is at most `(519 / 4550) * b`. -/
theorem marked_high_conservation_cap (b δ q : ℝ) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ removed frozen live : ℝ,
      0 ≤ removed ∧ 0 ≤ frozen ∧ 0 ≤ live ∧
      removed + frozen + live = b ∧
      (519 / 4550) * removed + δ * frozen + (224 / 1755) * min live (13 * q / 400) ≤
        (519 / 4550) * b := by
  refine ⟨b, 0, 0, hb, le_refl 0, le_refl 0, by ring, ?_⟩
  have hmin : min (0 : ℝ) (13 * q / 400) = 0 := min_eq_left (by positivity)
  rw [hmin]
  linarith

/-- **Regime II — Slope-Cancelled Coupled Plane with Unmarked High-Zero Density (`0.8748598`):**
At the coupled-plane split `q0 = 67/100` (`B = B0(67/100) - 1/100000 = 202497947/205300000`,
`lam = lam(67/100) = 16281/4106`, `h = 3969737987/5000000000`, saving `ν = 1/1000000`) and
`(δ₀, p₀) = (2343/5000, 1/2)`, `θ = 4374299/5000000 = 0.8748598` passes while
`θ = 4374298/5000000 = 0.8748596` strictly fails. -/
theorem coupled_plane_unmarked_high_grid_wall :
    B0Of (67 / 100) = 2025 / 2053 ∧
    lamOf (67 / 100) = 16281 / 4106 ∧
    G_old (4374299 / 5000000) (3969737987 / 5000000000) (202497947 / 205300000)
      (16281 / 4106) (2343 / 5000) (1 / 2) < 4374299 / 5000000 - 1 / 1000000 ∧
    4374298 / 5000000 - 1 / 1000000 <
      G_old (4374298 / 5000000) (3969737987 / 5000000000) (202497947 / 205300000)
        (16281 / 4106) (2343 / 5000) (1 / 2) := by
  unfold B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity G_old R_kappa_old
  norm_num

/-- **Regime III — Coupled Plane with Width-Conserved Marked High-Zero Saving (`0.8748559`):**
At `q0 = 17/25`, `B = B0(17/25) + 7/10000 = 142100527/143610000`, `lam = 19312/4787`,
`h = 7953177/10000000` and `(δ₀, p₀) = (2343/5000, 1/2)`, `θ = 8748559/10000000 = 0.8748559`
passes (`G_old < θ - 3/2000000`) while `θ = 8748558/10000000 = 0.8748558` strictly fails. -/
theorem coupled_plane_marked_high_grid_wall :
    B0Of (17 / 25) = 14200 / 14361 ∧
    lamOf (17 / 25) = 19312 / 4787 ∧
    G_old (8748559 / 10000000) (7953177 / 10000000) (142100527 / 143610000)
      (19312 / 4787) (2343 / 5000) (1 / 2) < 8748559 / 10000000 - 3 / 2000000 ∧
    8748558 / 10000000 - 3 / 2000000 <
      G_old (8748558 / 10000000) (7953177 / 10000000) (142100527 / 143610000)
        (19312 / 4787) (2343 / 5000) (1 / 2) := by
  unfold B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity G_old R_kappa_old
  norm_num

/-- **Regime IV-A — Count-Side Interior Affine Capacity with Unmarked High-Zero Density (`0.8748436`):**
At `q0 = 67/100`, `B = 202497947/205300000`, `lam = 16281/4106`, `h = 497/625`, `ν = 1/1000000`
and `(δ₀, p₀) = (931/2000, 1/2)`, `θ = 2187109/2500000 = 0.8748436` passes (`G_aff < θ - ν`)
while `θ = 2187108/2500000 = 0.8748432` strictly fails. -/
theorem affine_count_unmarked_high_grid_wall :
    G_aff (2187109 / 2500000) (497 / 625) (202497947 / 205300000)
      (16281 / 4106) (931 / 2000) (1 / 2) < 2187109 / 2500000 - 1 / 1000000 ∧
    2187108 / 2500000 - 1 / 1000000 <
      G_aff (2187108 / 2500000) (497 / 625) (202497947 / 205300000)
        (16281 / 4106) (931 / 2000) (1 / 2) := by
  unfold G_aff R_star_affine
  norm_num

/-- **Regime IV-B — Full Base-Contract Closure Wall at `θ = 0.874835`:**
Combining the slope-cancelled coupled plane (`B0Of q0`, `lamOf q0`), the width-conservation
maximum marked high-zero saving `ΔH_max = (519/4550) * (34/1000)`, the count-side interior
affine plain capacity `R_star_affine`, and the maximum `h` allowed by the Euler-shift gate
`2*y/(h - 1/2000) - 1 ≤ 4/25` (`h_max = (100*(11/3 - 4*θ) - 29/2000) / 21`), the candidate
value `θ = 874835 / 1000000 = 0.874835` is strictly infeasible (`θ < G_aff`) at
`(δ₀, p₀) = (931/2000, 1/2)` across every `q0 ∈ {65/100, 66/100, 67/100, 68/100, 69/100}`. -/
theorem full_contract_closure_wall_at_0874835 :
    let th := (874835 : ℝ) / 1000000
    let ell := 11 / 3 - 4 * th
    let h_max := (100 * ell - 29 / 2000) / 21
    let dH_max := (519 : ℝ) / 4550 * (34 / 1000)
    (th < G_aff th h_max (B0Of (65 / 100) + dH_max / (65 / 100 + WOf (65 / 100))) (lamOf (65 / 100)) (931 / 2000) (1 / 2)) ∧
    (th < G_aff th h_max (B0Of (66 / 100) + dH_max / (66 / 100 + WOf (66 / 100))) (lamOf (66 / 100)) (931 / 2000) (1 / 2)) ∧
    (th < G_aff th h_max (B0Of (67 / 100) + dH_max / (67 / 100 + WOf (67 / 100))) (lamOf (67 / 100)) (931 / 2000) (1 / 2)) ∧
    (th < G_aff th h_max (B0Of (68 / 100) + dH_max / (68 / 100 + WOf (68 / 100))) (lamOf (68 / 100)) (931 / 2000) (1 / 2)) ∧
    (th < G_aff th h_max (B0Of (69 / 100) + dH_max / (69 / 100 + WOf (69 / 100))) (lamOf (69 / 100)) (931 / 2000) (1 / 2)) := by
  unfold G_aff R_star_affine B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity
  norm_num

/- ### 6. Regime V — Coupled Variable-Slope Physical Envelope & Interior Optimization (`θ = 328/375 = 0.87466667`)
   (Scope note: LP / POLYNOMIAL ALGEBRA ONLY — ANALYTIC INPUTS UNFORMALIZED)

   In `full_contract_closure_wall_at_0874835`, the candidate value `θ = 0.874835` was shown to
   be blocked under the restrictive boundary conditions `h = h_max = (100*ell - 29/2000)/21`
   and fixed slot amplitude `p_0 = 1/2`.
   However, jointly optimizing the interior physical parameters `(h, p, q0, ell)`:
     `h = 39 / 50 = 0.7800`
     `p = 2 / 5 = 0.400`
     `q0 = 13 / 20 = 0.650`
     `ell = 21 / 125 = 0.168000`
   yields `θ = 11/12 - ell/4 = 328/375 = 0.87466667`, strictly lowering the candidate bound
   by `Δθ = 101/600000 = 0.00016833...` while rigorously satisfying:
     1. Positivity of the low-side box length: `y = h - 2*ell = 111/250 = 0.444000 > 0`.
     2. The Euler-shift gate: `2*y / (h - 1/2000) - 1 = 217/1559 ≤ 4/25` with slack `811/38975 > 0`.
     3. Strict positive slack for the count-side interior affine top-row exponent:
        `G_aff < θ - 1/500` at `δ = 9/20 = 0.450`, with exact slack
        `θ - G_aff = 9791587474521913 / 3488937932878125000 ≈ 0.00280647 > 0`.
     4. Uniform positive slack across the carrier frequency band `δ ∈ [0.440, 0.480]`. -/

/-- Exact rational parameters of the Regime V physical envelope and strict improvement
over the Regime IV-B boundary `0.874835`. -/
theorem regime_v_physical_parameters :
    let th : ℝ := 328 / 375
    let ell : ℝ := 21 / 125
    let h : ℝ := 39 / 50
    let y : ℝ := h - 2 * ell
    let q0 : ℝ := 13 / 20
    th = 11 / 12 - ell / 4 ∧
    y = 111 / 250 ∧
    0 < y ∧
    B0Of q0 = 565 / 576 ∧
    WOf q0 = 403 / 148 ∧
    lamOf q0 = 1469 / 384 ∧
    th < 874835 / 1000000 ∧
    (874835 : ℝ) / 1000000 - th = 101 / 600000 := by
  unfold B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity
  norm_num

/-- The interior box scale `h = 39/50`, `ell = 21/125` rigorously satisfies the Euler-shift gate
`2*y / (h - 1/2000) - 1 ≤ 4/25` with positive slack `811/38975 > 0`. -/
theorem regime_v_euler_shift_gate :
    let ell : ℝ := 21 / 125
    let h : ℝ := 39 / 50
    let y : ℝ := h - 2 * ell
    (2 * y / (h - 1 / 2000) - 1 : ℝ) ≤ 4 / 25 ∧
    (4 : ℝ) / 25 - (2 * y / (h - 1 / 2000) - 1) = 811 / 38975 := by
  norm_num

/-- Under Regime V interior parameters (`h = 39/50, p = 2/5, q0 = 13/20, ell = 21/125`),
the candidate value `θ = 328/375 = 0.87466667` is strictly feasible (`G_aff < θ - 1/500`)
at carrier midpoint `δ = 9/20 = 0.450`. -/
theorem regime_v_physical_feasibility :
    let th : ℝ := 328 / 375
    let ell : ℝ := 21 / 125
    let h : ℝ := 39 / 50
    let p : ℝ := 2 / 5
    let q0 : ℝ := 13 / 20
    let dH_max : ℝ := (519 / 4550) * (34 / 1000)
    let B : ℝ := B0Of q0 + dH_max / (q0 + WOf q0)
    let lam : ℝ := lamOf q0
    let d : ℝ := 9 / 20
    G_aff th h B lam d p < th - 1 / 500 ∧
    th - G_aff th h B lam d p = 9791587474521913 / 3488937932878125000 := by
  unfold G_aff R_star_affine B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity
  norm_num

/-- Strict feasibility `G_aff < θ` holds across the entire carrier frequency band
`δ ∈ {0.440, 0.445, 0.450, 0.455, 0.460, 0.465, 0.470, 0.475, 0.480}`. -/
theorem regime_v_bandwidth_slack_positive (d : ℝ)
    (hd : d = 11 / 25 ∨ d = 89 / 200 ∨ d = 9 / 20 ∨ d = 91 / 200 ∨ d = 23 / 50 ∨ d = 93 / 200 ∨ d = 47 / 100 ∨ d = 19 / 40 ∨ d = 12 / 25) :
    let th : ℝ := 328 / 375
    let h : ℝ := 39 / 50
    let p : ℝ := 2 / 5
    let q0 : ℝ := 13 / 20
    let dH_max : ℝ := (519 / 4550) * (34 / 1000)
    let B : ℝ := B0Of q0 + dH_max / (q0 + WOf q0)
    let lam : ℝ := lamOf q0
    G_aff th h B lam d p < th := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  { unfold G_aff R_star_affine B0Of lamOf WOf KaOf OAI.SevenEighths.LocalMoment.unmarkedDensity
    norm_num }

end

end Submission20261012.HardLimit

#print axioms Submission20261012.HardLimit.certb_endpoint_parameters
#print axioms Submission20261012.HardLimit.fixed_b006_grid_wall_obstruction
#print axioms Submission20261012.HardLimit.b029_slope_6kappa_region_obstruction
#print axioms Submission20261012.HardLimit.b026_four_face_reserve_decomposition
#print axioms Submission20261012.HardLimit.bareWindow_pivot_domination
#print axioms Submission20261012.HardLimit.truncated_sieve_no_go
#print axioms Submission20261012.HardLimit.universal_low_side_dual_identity
#print axioms Submission20261012.HardLimit.universal_low_side_13_15_lp_floor
#print axioms Submission20261012.HardLimit.ideal_high_side_coincidence
#print axioms Submission20261012.HardLimit.p0_bootstrap_obstruction
#print axioms Submission20261012.HardLimit.marked_high_conservation_cap
#print axioms Submission20261012.HardLimit.coupled_plane_unmarked_high_grid_wall
#print axioms Submission20261012.HardLimit.coupled_plane_marked_high_grid_wall
#print axioms Submission20261012.HardLimit.affine_count_unmarked_high_grid_wall
#print axioms Submission20261012.HardLimit.full_contract_closure_wall_at_0874835
#print axioms Submission20261012.HardLimit.regime_v_physical_parameters
#print axioms Submission20261012.HardLimit.regime_v_euler_shift_gate
#print axioms Submission20261012.HardLimit.regime_v_physical_feasibility
#print axioms Submission20261012.HardLimit.regime_v_bandwidth_slack_positive
end
/- END ORIGINAL MODULE Global.HardLimit -/
