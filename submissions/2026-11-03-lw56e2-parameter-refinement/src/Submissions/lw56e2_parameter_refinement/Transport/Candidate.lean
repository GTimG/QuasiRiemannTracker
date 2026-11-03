/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/Candidate.lean
Original SHA-256: b79d57e3f228eb9b2c7d32fc7739a7faa6b888c1f7dd2de92b564a700753a1ab
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.LocalBounds

/-!
# Exact side conditions for the strongest screened rational candidate

This module checks rational geometry, local-power and loss-budget side
conditions for the parameter selected by our exact arithmetic exploration.
The number named cushion is a proposed endpoint budget. This module does not
assert the endpoint inequality that would justify that budget, and it does not
assert any analytic estimate or zero-free theorem.
-/

namespace LW56e2.Transport.Candidate

open LW56e2.Transport.Geometry
open LW56e2.Transport.LocalBounds

noncomputable section

def p : ℝ := 68479 / 400000000

def B : ℝ := boundary p

def cushion : ℝ := 1 / 40000000000

def zeta : ℝ := 1 / 320000000000

theorem p_pos : 0 < p := by norm_num [p]

theorem p_lt_one_thousandth : p < 1 / 1000 := by norm_num [p]

theorem p_lt_one_thirtieth : p < 1 / 30 := by norm_num [p]

theorem boundary_value : B = 1399931521 / 1600000000 := by
  norm_num [B, boundary, p]

theorem boundary_decrement_value :
    (7 / 8 : ℝ) - B = 68479 / 1600000000 := by
  norm_num [B, boundary, p]

theorem boundary_improvement : B < 7 / 8 := by
  exact boundary_lt_seven_eighths p_pos

theorem lowExponent_value :
    lowExponent p = 299931521 / 1600000000 := by
  norm_num [lowExponent, lx, b, p]

theorem signal_boundary : signal p B = lowExponent p := by
  exact (lowExponent_eq_signal_boundary p).symm

theorem cushion_pos : 0 < cushion := by norm_num [cushion]

theorem zeta_pos : 0 < zeta := by norm_num [zeta]

theorem zeta_eq_cushion_eighth : zeta = cushion / 8 := by
  norm_num [zeta, cushion]

theorem central_remaining_value :
    cushion - 2 * zeta = 3 / 160000000000 := by
  norm_num [cushion, zeta]

theorem central_remaining_pos : 0 < cushion - 2 * zeta := by
  norm_num [cushion, zeta]

inductive SideCondition where
  | lowSubset
  | minimumWidth
  | minimumLx
  | minimumLy
  | gram
  | floor
  | intermediate
  | small
  | selectedSupply
  | strongSupply
  | bufferedUpperScale
  | principalW
  | principalZ
  | goodTail
  | principalMixed
  | smallFirstRegion

def sideMargin (term : SideCondition) : ℝ :=
  match term with
  | .lowSubset => 1 / 5 - ell p
  | .minimumWidth => 1 - 3 * ell p
  | .minimumLx => lx p - ell p
  | .minimumLy => ly p - ell p
  | .gram => ly p - ell p - 11 * b / 6
  | .floor => 7 / 1200 - (32 / 25) * p
  | .intermediate => 241 / 9600 - (329 / 400) * p
  | .small => 63 / 800 - (51 / 100) * p
  | .selectedSupply => ell p / (h p + zeta) - 7 / 37
  | .strongSupply => 5 * ell p - h p - zeta
  | .bufferedUpperScale => 1 - h p - zeta
  | .principalW => ly p / 20
  | .principalZ => h p / 600
  | .goodTail => goodTailDecay p - 4 / 5
  | .principalMixed => 4 * B - 301 / 100
  | .smallFirstRegion => B - 1 / 2

/-- Exact rational values of the sixteen side-condition margins. -/
def sideMarginValue (term : SideCondition) : ℝ :=
  match term with
  | .lowSubset => 39794563 / 1200000000
  | .minimumWidth => 199794563 / 400000000
  | .minimumLx => 149794563 / 800000000
  | .minimumLy => 249794563 / 800000000
  | .gram => 199383689 / 2400000000
  | .floor => 5263313 / 937500000
  | .intermediate => 11982411227 / 480000000000
  | .small => 3146507571 / 40000000000
  | .selectedSupply => 464355264379 / 28869121402911
  | .strongSupply => 20575223597 / 960000000000
  | .bufferedUpperScale => 59917825199 / 320000000000
  | .principalW => 1149794563 / 48000000000
  | .principalZ => 650205437 / 480000000000
  | .goodTail => 23931521 / 1600000000
  | .principalMixed => 195931521 / 400000000
  | .smallFirstRegion => 599931521 / 1600000000

theorem sideMargin_eq_value (term : SideCondition) :
    sideMargin term = sideMarginValue term := by
  cases term <;>
    norm_num [sideMargin, sideMarginValue, ell, lx, ly, h, b,
      B, boundary, goodTailDecay, p, zeta]

theorem all_side_margins_pos (term : SideCondition) :
    0 < sideMargin term := by
  rw [sideMargin_eq_value]
  cases term <;> norm_num [sideMarginValue]

theorem floor_exceeds_cushion :
    cushion - 2 * zeta < sideMargin .floor - 2 * zeta := by
  norm_num [cushion, zeta, sideMargin, p]

theorem intermediate_exceeds_cushion :
    cushion < sideMargin .intermediate := by
  norm_num [cushion, sideMargin, p]

theorem small_exceeds_cushion :
    cushion < sideMargin .small := by
  norm_num [cushion, sideMargin, p]

theorem selected_supply_strict :
    (7 / 37 : ℝ) < ell p / (h p + zeta) := by
  have hm := all_side_margins_pos SideCondition.selectedSupply
  dsimp [sideMargin] at hm
  linarith

theorem extension_supply_strict : zeta < 5 * ell p - h p := by
  have hm := all_side_margins_pos SideCondition.strongSupply
  dsimp [sideMargin] at hm
  linarith

theorem buffered_upper_scale_lt_one : h p + zeta < 1 := by
  have hm := all_side_margins_pos SideCondition.bufferedUpperScale
  dsimp [sideMargin] at hm
  linarith

theorem subset_loss_nonpos {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ ell p) :
    subsetLoss p d ≤ 0 :=
  subsetLoss_nonpos p_pos p_lt_one_thirtieth hd0 hd

theorem local_good_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 :=
  good_power_lt_neg_one p_pos p_lt_one_thousandth hs hw hz term

theorem local_ramified_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 :=
  ramified_power_neg p_lt_one_thousandth hs hw hz term

theorem local_principal_table {s w z : ℝ}
    (hs : B ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -B :=
  principal_power_le p_pos p_lt_one_thousandth hs hw hz term

end

end LW56e2.Transport.Candidate
