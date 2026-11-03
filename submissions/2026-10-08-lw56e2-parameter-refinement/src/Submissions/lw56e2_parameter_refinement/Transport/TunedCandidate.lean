/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/TunedCandidate.lean
Original SHA-256: ea68368eaef74fb5ea1fd54f224440b55c8f73807c40e9224064e5a4b73953a4
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.LocalBounds
import Submissions.lw56e2_parameter_refinement.Transport.SupportedMass

/-!
# Two-parameter geometry and exact tuned side conditions

These independently authored definitions allow the Gram exponent b to vary.
The fixed rational instance is the candidate of optimize_transport_b.py.
All numerical claims below are proved by Lean arithmetic; no certificate is
accepted as an axiom. The separate TunedEndpoint module proves its continuous
endpoint inequality. Neither module asserts an analytic zero-free theorem.

The supported-mass interface is a genuine finite-sum inequality, while its
application to the manuscript's ideals still requires the stated arithmetic
mass hypothesis. The local tables concern exponents, not analytic products.
-/

namespace LW56e2.Transport.TunedCandidate

open LW56e2.Transport.LocalBounds

noncomputable section

def lxAt (e b : ℝ) : ℝ := (1 - e - b) / 2
def lyAt (e b : ℝ) : ℝ := (1 - e + b) / 2
def hAt (e b : ℝ) : ℝ := (1 + 3 * e + b) / 2
def widthAt (e : ℝ) : ℝ := 1 - e
def boundaryAt (e : ℝ) : ℝ := 11 / 12 - e / 4
def signalAt (e b s : ℝ) : ℝ := s + lxAt e b / 2 - 1 + hAt e b / 6
def lowExponentAt (e b : ℝ) : ℝ := lxAt e b / 2 + b / 12

theorem widthAt_eq_sum (e b : ℝ) :
    widthAt e = lxAt e b + lyAt e b := by
  dsimp [widthAt, lxAt, lyAt]
  ring

theorem hAt_eq (e b : ℝ) : hAt e b = 1 - lxAt e b + e := by
  dsimp [hAt, lxAt]
  ring

theorem lyAt_eq (e b : ℝ) : lyAt e b = lxAt e b + b := by
  dsimp [lyAt, lxAt]
  ring

theorem signalAt_eq (e b s : ℝ) : signalAt e b s = s - 2 / 3 - b / 6 := by
  dsimp [signalAt, lxAt, hAt]
  ring

theorem lowExponentAt_eq (e b : ℝ) :
    lowExponentAt e b = 1 / 4 - e / 4 - b / 6 := by
  dsimp [lowExponentAt, lxAt]
  ring

theorem signalAt_boundaryAt (e b : ℝ) :
    signalAt e b (boundaryAt e) = lowExponentAt e b := by
  rw [signalAt_eq, lowExponentAt_eq]
  dsimp [boundaryAt]
  ring

theorem boundaryAt_eq_geometry (p : ℝ) :
    boundaryAt (Geometry.ell p) = Geometry.boundary p := by
  dsimp [boundaryAt, Geometry.ell, Geometry.boundary]
  ring

theorem reflected_loss_identity (e d : ℝ) :
    1 + 3 * (e - d) - 2 * (widthAt e - 2 * d) = 5 * e - 1 + d := by
  dsimp [widthAt]
  ring

def p : ℝ := 214651 / 1250000000
def b : ℝ := 192821 / 1562500
def ell : ℝ := Geometry.ell p
def lx : ℝ := lxAt ell b
def ly : ℝ := lyAt ell b
def h : ℝ := hAt ell b
def width : ℝ := widthAt ell
def B : ℝ := boundaryAt ell
def signal (s : ℝ) : ℝ := signalAt ell b s
def lowExponent : ℝ := lowExponentAt ell b
def cushion : ℝ := 1 / 1000000000000
def zeta : ℝ := 1 / 8000000000000

theorem p_pos : 0 < p := by norm_num [p]
theorem p_lt_one_thousandth : p < 1 / 1000 := by norm_num [p]
theorem p_lt_one_thirtieth : p < 1 / 30 := by norm_num [p]
theorem b_pos : 0 < b := by norm_num [b]

theorem geometry_values :
    ell = 625643953 / 3750000000 ∧
    lx = 2661585647 / 7500000000 ∧
    ly = 3587126447 / 7500000000 ∧
    h = 2029900753 / 2500000000 := by
  norm_num [ell, Geometry.ell, lx, ly, h, lxAt, lyAt, hAt, p, b]

theorem boundary_eq_geometry : B = Geometry.boundary p :=
  boundaryAt_eq_geometry p

theorem boundary_value : B = 4374785349 / 5000000000 := by
  norm_num [B, boundaryAt, ell, Geometry.ell, p]

theorem boundary_decrement_value :
    (7 / 8 : ℝ) - B = 214651 / 5000000000 := by
  rw [boundary_value]
  norm_num

theorem boundary_improvement : B < 7 / 8 := by
  rw [boundary_eq_geometry]
  exact Geometry.boundary_lt_seven_eighths p_pos

theorem width_eq_sum : width = lx + ly := widthAt_eq_sum ell b
theorem width_add_ell : width + ell = 1 := by dsimp [width, widthAt]; ring
theorem h_eq : h = 1 - lx + ell := hAt_eq ell b
theorem ly_eq : ly = lx + b := lyAt_eq ell b

theorem signal_eq (s : ℝ) : signal s = s - 2 / 3 - b / 6 :=
  signalAt_eq ell b s

theorem signal_intercept_value (s : ℝ) :
    signal s = s - 2147607 / 3125000 := by
  rw [signal_eq]
  norm_num [b]
  ring

theorem signal_boundary : signal B = lowExponent :=
  signalAt_boundaryAt ell b

theorem signal_difference (s t : ℝ) : signal s - signal t = s - t := by
  rw [signal_eq, signal_eq]
  ring

theorem lowExponent_value : lowExponent = 938614149 / 5000000000 := by
  norm_num [lowExponent, lowExponentAt, lxAt, ell, Geometry.ell, b, p]

theorem cushion_pos : 0 < cushion := by norm_num [cushion]
theorem zeta_pos : 0 < zeta := by norm_num [zeta]
theorem zeta_eq_cushion_eighth : zeta = cushion / 8 := by
  norm_num [zeta, cushion]
theorem central_remaining_value : cushion - 2 * zeta = 3 / 4000000000000 := by
  norm_num [cushion, zeta]
theorem central_remaining_pos : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]

/-- The intermediate-row exponent with row scale one half. -/
def intermediateExponent (δ x : ℝ) : ℝ :=
  let a := (1 + δ) / 2
  let q := δ * x
  let R := 76 / 75 - 2 * δ / 3
  a - B + h * (17 / 50 - 1 / 6) - a * ly - ell / 2 + q * ell
    + (1 / 2) * (R + δ / 2 - 17 / 50)

theorem intermediateExponent_eq (δ x : ℝ) :
    intermediateExponent δ x =
      -41270920211 / 187500000000 +
        (2662873553 / 15000000000) * δ +
        (625643953 / 3750000000) * δ * x := by
  norm_num [intermediateExponent, B, boundaryAt, h, hAt, ly, lyAt,
    ell, Geometry.ell, p, b]
  ring

/-- The stated intermediate margin is valid on the entire bin rectangle. -/
theorem intermediateExponent_le_corner {δ x : ℝ}
    (hd0 : 0 ≤ δ) (hd : δ ≤ 3 / 4) (hx : x ≤ 1 / 2) :
    intermediateExponent δ x ≤ intermediateExponent (3 / 4) (1 / 2) := by
  have hm : δ * x ≤ δ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hx hd0
  rw [intermediateExponent_eq, intermediateExponent_eq]
  nlinarith

inductive SideCondition where
  | gramScale | lowSubset | minimumWidth | minimumLx | minimumLy | gram
  | floor | intermediate | small | selectedSupply | strongSupply
  | bufferedUpperScale | principalW | principalZ | goodTail
  | principalMixed | smallFirstRegion

def sideMargin (term : SideCondition) : ℝ :=
  match term with
  | .gramScale => b
  | .lowSubset => 1 / 5 - ell
  | .minimumWidth => 1 - 3 * ell
  | .minimumLx => lx - ell
  | .minimumLy => ly - ell
  | .gram => ly - ell - 11 * b / 6
  | .floor => 7 / 1200 - (32 / 25) * p - (b - 1 / 8) / 6
  | .intermediate => -intermediateExponent (3 / 4) (1 / 2)
  | .small => ly / 2 - h * (17 / 50 - 1 / 6) - 1 / 50
  | .selectedSupply => ell / (h + zeta) - 7 / 37
  | .strongSupply => 5 * ell - h - zeta
  | .bufferedUpperScale => 1 - h - zeta
  | .principalW => ly / 20
  | .principalZ => h / 600
  | .goodTail => goodTailDecay p - 4 / 5
  | .principalMixed => 4 * B - 301 / 100
  | .smallFirstRegion => B - 1 / 2

def sideMarginValue (term : SideCondition) : ℝ :=
  match term with
  | .gramScale => 192821 / 1562500
  | .lowSubset => 124356047 / 3750000000
  | .minimumWidth => 624356047 / 1250000000
  | .minimumLx => 470099247 / 2500000000
  | .minimumLy => 778612847 / 2500000000
  | .gram => 639013741 / 7500000000
  | .floor => 34448969 / 5859375000
  | .intermediate => 36605252263 / 1500000000000
  | .small => 9800247199 / 125000000000
  | .selectedSupply => 1067559769889 / 65547340678701
  | .strongSupply => 533559267197 / 24000000000000
  | .bufferedUpperScale => 1504317590399 / 8000000000000
  | .principalW => 3587126447 / 150000000000
  | .principalZ => 2029900753 / 1500000000000
  | .goodTail => 74785349 / 5000000000
  | .principalMixed => 612285349 / 1250000000
  | .smallFirstRegion => 1874785349 / 5000000000

theorem sideMargin_eq_value (term : SideCondition) :
    sideMargin term = sideMarginValue term := by
  cases term <;>
    norm_num [sideMargin, sideMarginValue, intermediateExponent, ell,
      Geometry.ell, lx, ly, h, lxAt, lyAt, hAt, b,
      B, boundaryAt, goodTailDecay, p, zeta]

theorem all_side_margins_pos (term : SideCondition) : 0 < sideMargin term := by
  rw [sideMargin_eq_value]
  cases term <;> norm_num [sideMarginValue]

theorem floor_exceeds_cushion : cushion < sideMargin .floor := by
  rw [sideMargin_eq_value]
  norm_num [cushion, sideMarginValue]

theorem intermediate_exceeds_cushion : cushion < sideMargin .intermediate := by
  rw [sideMargin_eq_value]
  norm_num [cushion, sideMarginValue]

theorem intermediate_uniform_cushion {δ x : ℝ}
    (hd0 : 0 ≤ δ) (hd : δ ≤ 3 / 4) (hx : x ≤ 1 / 2) :
    intermediateExponent δ x < -cushion := by
  have hm := intermediateExponent_le_corner hd0 hd hx
  have hc := intermediate_exceeds_cushion
  dsimp [sideMargin] at hc
  linarith

theorem small_exceeds_cushion : cushion < sideMargin .small := by
  rw [sideMargin_eq_value]
  norm_num [cushion, sideMarginValue]

theorem selected_supply_strict : (7 / 37 : ℝ) < ell / (h + zeta) := by
  have hm := all_side_margins_pos SideCondition.selectedSupply
  dsimp [sideMargin] at hm
  linarith

theorem extension_supply_strict : zeta < 5 * ell - h := by
  have hm := all_side_margins_pos SideCondition.strongSupply
  dsimp [sideMargin] at hm
  linarith

theorem buffered_upper_scale_lt_one : h + zeta < 1 := by
  have hm := all_side_margins_pos SideCondition.bufferedUpperScale
  dsimp [sideMargin] at hm
  linarith

theorem all_subset_lengths_pos {d : ℝ} (hd : d ≤ ell) :
    0 < width - 2 * d ∧ 0 < lx - d ∧ 0 < ly - d ∧
      0 < ly - d - 11 * b / 6 := by
  have hM := all_side_margins_pos SideCondition.minimumWidth
  have hx := all_side_margins_pos SideCondition.minimumLx
  have hy := all_side_margins_pos SideCondition.minimumLy
  have hG := all_side_margins_pos SideCondition.gram
  dsimp [sideMargin] at hM hx hy hG
  dsimp [width, widthAt]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The supported-mass decay absorbs the square-root reflected row loss. -/
theorem half_subset_loss_le {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ -3 * d / 8 := by
  have hm := Geometry.positive_part_le_subset p_lt_one_thirtieth hd
  change max 0 (5 * ell - 1 + d) ≤ d at hm
  linarith

theorem half_subset_loss_nonpos {d : ℝ} (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * ell - 1 + d) / 8 ≤ 0 := by
  have hm := half_subset_loss_le hd
  linarith

theorem support_decay_absorbs_row_loss {d Z C mass : ℝ}
    (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * ell - 1 + d) / 8) ≤ C :=
  SupportedMass.support_decay_absorbs_row_loss
    p_lt_one_thirtieth hd hZ hC hmass

theorem local_good_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 := by
  rw [boundary_eq_geometry] at hs
  exact good_power_lt_neg_one p_pos p_lt_one_thousandth hs hw hz term

theorem local_ramified_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 := by
  rw [boundary_eq_geometry] at hs
  exact ramified_power_neg p_lt_one_thousandth hs hw hz term

theorem local_principal_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -B := by
  rw [boundary_eq_geometry] at hs ⊢
  exact principal_power_le p_pos p_lt_one_thousandth hs hw hz term

end
end LW56e2.Transport.TunedCandidate
