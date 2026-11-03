/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/LocalBounds.lean
Original SHA-256: 5d0beed5bac266a36733f16d68797b1558c2000c45249f1e7d8b22cd2c763dfe
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.Geometry

/-!
# Affine local exponent tables

These formulas are transcribed from the local rational-factor calculations in
the accepted OpenAI manuscript, as recorded in our research draft and
experiments/check_transport_local.py. The proofs below are independent
real-linear arithmetic proofs, uniform for 0 < p < 1/1000.

Only the exponents are formalized. There are no declarations asserting bounds
for actual Euler factors, convergence of an infinite product, holomorphy,
or analytic nonvanishing.
-/

namespace LW56e2.Transport.LocalBounds

open LW56e2.Transport.Geometry

noncomputable section

inductive DenominatorTerm where
  | r | v | d

def denominatorPower (term : DenominatorTerm) (s z : ℝ) : ℝ :=
  match term with
  | .r => 4 - 6 * s - 6 * z
  | .v => -6 * z
  | .d => -s

def denominatorCap (term : DenominatorTerm) (p : ℝ) : ℝ :=
  match term with
  | .r => -56 / 25 + 3 * p / 2
  | .v => -99 / 100
  | .d => -boundary p

theorem denominator_power_le {p s z : ℝ}
    (hs : boundary p ≤ s) (hz : (33 / 200 : ℝ) ≤ z)
    (term : DenominatorTerm) :
    denominatorPower term s z ≤ denominatorCap term p := by
  cases term <;>
    dsimp [denominatorPower, denominatorCap, boundary] at * <;>
    linarith

theorem denominator_cap_neg {p : ℝ} (hp : p < 1 / 1000)
    (term : DenominatorTerm) : denominatorCap term p < 0 := by
  cases term <;> dsimp [denominatorCap, boundary] <;> linarith

theorem denominator_power_neg {p s z : ℝ} (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hz : (33 / 200 : ℝ) ≤ z)
    (term : DenominatorTerm) : denominatorPower term s z < 0 :=
  lt_of_le_of_lt (denominator_power_le hs hz term)
    (denominator_cap_neg hp term)

inductive GoodTerm where
  | dv | dw | dvw | vw | r | strictFamily

def goodPower (term : GoodTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .dv => -s - 6 * z
  | .dw => -s - w
  | .dvw => -s - w - 6 * z
  | .vw => -w - 6 * z
  | .r => 4 - 6 * s - 6 * z
  | .strictFamily => 1 - s - w - 6 * z

def goodCap (p : ℝ) : ℝ := -363 / 200 + p / 4

theorem good_power_le {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z ≤ goodCap p := by
  cases term <;> dsimp [goodPower, goodCap, boundary] at * <;> linarith

theorem good_cap_lt_neg_one {p : ℝ} (hp : p < 1 / 1000) :
    goodCap p < -1 := by
  dsimp [goodCap]
  linarith

theorem good_power_lt_neg_one {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : GoodTerm) :
    goodPower term s w z < -1 :=
  lt_of_le_of_lt (good_power_le hp0 hp hs hw hz term)
    (good_cap_lt_neg_one hp)

/-- The grouped strict-family exponent attains the specified cap at the corner. -/
theorem good_cap_attained (p : ℝ) :
    goodPower .strictFamily (boundary p) (19 / 20) (33 / 200) =
      goodCap p := by
  dsimp [goodPower, goodCap, boundary]
  ring

inductive RamifiedTerm where
  | r | strictFamily | j1 | j2 | j3First | j3Second | j4 | j5

def ramifiedPower (term : RamifiedTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .r => 4 - 6 * s - 6 * z
  | .strictFamily => 1 - s - w
  | .j1 => -s - w
  | .j2 => 3 / 2 - 3 * s
  | .j3First => 2 - 3 * s - w
  | .j3Second => 2 - 4 * s
  | .j4 => 5 / 2 - 4 * s - w
  | .j5 => 3 - 6 * s

def ramifiedCap (p : ℝ) : ℝ := -33 / 40 + p / 4

theorem ramified_power_le {p s w z : ℝ}
    (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z ≤ ramifiedCap p := by
  cases term <;> dsimp [ramifiedPower, ramifiedCap, boundary] at * <;> linarith

theorem ramified_cap_neg {p : ℝ} (hp : p < 1 / 1000) :
    ramifiedCap p < 0 := by
  dsimp [ramifiedCap]
  linarith

theorem ramified_power_neg {p s w z : ℝ}
    (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : RamifiedTerm) :
    ramifiedPower term s w z < 0 :=
  lt_of_le_of_lt (ramified_power_le hp hs hw hz term)
    (ramified_cap_neg hp)

theorem ramified_cap_attained (p : ℝ) :
    ramifiedPower .strictFamily (boundary p) (19 / 20) (33 / 200) =
      ramifiedCap p := by
  dsimp [ramifiedPower, ramifiedCap, boundary]
  ring

inductive PrincipalTerm where
  | inverse | sixthPower | mixed | numerator

def principalPower (term : PrincipalTerm) (s w z : ℝ) : ℝ :=
  match term with
  | .inverse => -s
  | .sixthPower => -6 * z
  | .mixed => 4 - 5 * s - 6 * z
  | .numerator => 1 - w - 6 * z

theorem principal_power_le {p s w z : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 1000)
    (hs : boundary p ≤ s) (hw : (19 / 20 : ℝ) ≤ w)
    (hz : (33 / 200 : ℝ) ≤ z) (term : PrincipalTerm) :
    principalPower term s w z ≤ -boundary p := by
  cases term <;> dsimp [principalPower, boundary] at * <;> linarith

theorem principal_inverse_cap_attained (p : ℝ) :
    principalPower .inverse (boundary p) (19 / 20) (33 / 200) =
      -boundary p := by
  rfl

def goodTailDecay (p : ℝ) : ℝ := 163 / 200 - p / 4

theorem goodTailDecay_eq (p : ℝ) :
    goodTailDecay p = -1 - goodCap p := by
  dsimp [goodTailDecay, goodCap]
  ring

theorem goodTailDecay_gt_four_fifths {p : ℝ} (hp : p < 1 / 1000) :
    (4 / 5 : ℝ) < goodTailDecay p := by
  dsimp [goodTailDecay]
  linarith

theorem goodTailDecay_margin (p : ℝ) :
    goodTailDecay p - 4 / 5 = 3 / 200 - p / 4 := by
  dsimp [goodTailDecay]
  ring

/-- Exponents on the small-row contour, not bounds for the local factors. -/
theorem small_coprime_power_neg {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : PrincipalTerm) :
    principalPower term s (1 / 2) (17 / 50) < 0 := by
  cases term <;> dsimp [principalPower, boundary] at * <;> linarith

inductive SmallRamifiedTerm where
  | strictFamily | j1 | j2OrJ3First | j3SecondOrJ4 | j5 | r

def smallRamifiedPower (term : SmallRamifiedTerm) (s : ℝ) : ℝ :=
  match term with
  | .strictFamily => 1 / 2
  | .j1 => -1 / 2
  | .j2OrJ3First => 3 / 2 - 2 * s
  | .j3SecondOrJ4 => 2 - 3 * s
  | .j5 => 3 - 5 * s
  | .r => 4 - 5 * s - 6 * (17 / 50)

theorem small_ramified_power_le_half {p s : ℝ}
    (hp : p < 1 / 1000) (hs : boundary p ≤ s)
    (term : SmallRamifiedTerm) :
    smallRamifiedPower term s ≤ 1 / 2 := by
  cases term <;> dsimp [smallRamifiedPower, boundary] at * <;> linarith

theorem small_first_region_margin_pos {p : ℝ} (hp : p < 1 / 1000) :
    0 < boundary p - 1 / 2 := by
  dsimp [boundary]
  linarith

end

end LW56e2.Transport.LocalBounds
