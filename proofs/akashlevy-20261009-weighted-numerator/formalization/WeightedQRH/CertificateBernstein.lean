import WeightedQRH.Parameters

namespace WeightedQRH

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- D_x in the manuscript. -/
def countD (x : ℝ) : ℝ := 3 - (17 / 9 : ℝ) * x
/-- P_x in the manuscript. -/
def countP (x : ℝ) : ℝ := (2 - (8 / 9 : ℝ) * x) * (1 - x)
/-- The common strictly positive denominator J. -/
def countDen (δ x : ℝ) : ℝ := (5 / 6 - δ) * countD x + δ * countP x
/-- The numerator R J of the selected row count. -/
def countNum (δ x : ℝ) : ℝ := (1 - δ) * countDen δ x +
  (5 / 6 - δ) * δ * countP x / 2

def rowCount (δ x : ℝ) : ℝ := countNum δ x / countDen δ x

def oldRest (δ x : ℝ) : ℝ :=
  (1 + δ) * (1 - ly) / 2 - ell / 2 + δ * x * ell + h * δ / 2 - h / 6 - theta

def oldCert (δ x : ℝ) : ℝ :=
  -((oldRest δ x + endpointMargin) * countDen δ x + h * countNum δ x)

def weightedCert (δ x : ℝ) : ℝ := oldCert δ x -
  (h / 4 * (countDen δ x - countNum δ x) +
   δ * (ly - h) / 2 * countDen δ x -
   δ * x * (2 * ly - h) / (12 * kappa) * countDen δ x)

theorem countDen_pos {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 < countDen δ x := by
  have ha : 0 < (5 / 6 : ℝ) - δ := by linarith
  have hb : 0 < countD x := by unfold countD; linarith
  have hc : 0 ≤ countP x := by
    have hc1 : 0 ≤ (2 : ℝ) - 8 / 9 * x := by linarith
    have hc2 : 0 ≤ (1 : ℝ) - x := by linarith
    exact mul_nonneg hc1 hc2
  exact add_pos_of_pos_of_nonneg (mul_pos ha hb) (mul_nonneg hδ0 hc)

/-- Exact unnormalised Bernstein identity on certificate leaf 0. -/
private theorem old_identity_0 (δ x : ℝ) :
    oldCert δ x =
      (4827 / 1000 : ℝ) * ((1 / 3 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (46661 / 3600 : ℝ) * ((1 / 3 : ℝ) - δ) ^ 2 * (x - 0) * ((1 / 2 : ℝ) - x) ^ 2
      + (12872 / 1125 : ℝ) * ((1 / 3 : ℝ) - δ) ^ 2 * (x - 0) ^ 2 * ((1 / 2 : ℝ) - x)
      + (59533 / 18000 : ℝ) * ((1 / 3 : ℝ) - δ) ^ 2 * (x - 0) ^ 3
      + (913 / 1250 : ℝ) * (δ - 0) * ((1 / 3 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (7231 / 2500 : ℝ) * (δ - 0) * ((1 / 3 : ℝ) - δ) * (x - 0) * ((1 / 2 : ℝ) - x) ^ 2
      + (159773 / 45000 : ℝ) * (δ - 0) * ((1 / 3 : ℝ) - δ) * (x - 0) ^ 2 * ((1 / 2 : ℝ) - x)
      + (62483 / 45000 : ℝ) * (δ - 0) * ((1 / 3 : ℝ) - δ) * (x - 0) ^ 3
      + (6197 / 5000 : ℝ) * (δ - 0) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (136471 / 90000 : ℝ) * (δ - 0) ^ 2 * (x - 0) * ((1 / 2 : ℝ) - x) ^ 2
      + (24103 / 45000 : ℝ) * (δ - 0) ^ 2 * (x - 0) ^ 2 * ((1 / 2 : ℝ) - x)
      + (3307 / 30000 : ℝ) * (δ - 0) ^ 2 * (x - 0) ^ 3 := by
  unfold oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem old_leaf_0 {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ (1 / 3 : ℝ))
    (hx0 : 0 ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ oldCert δ x := by
  have ha : 0 ≤ δ - 0 := by linarith
  have hb : 0 ≤ (1 / 3 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - 0 := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [old_identity_0]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 0. -/
private theorem weighted_identity_0 (δ x : ℝ) :
    weightedCert δ x =
      (159072 / 15625 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * ((1 / 4 : ℝ) - x) ^ 3
      + (3272396 / 140625 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - 0) * ((1 / 4 : ℝ) - x) ^ 2
      + (22306468 / 1265625 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - 0) ^ 2 * ((1 / 4 : ℝ) - x)
      + (625504 / 140625 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - 0) ^ 3
      + (434284 / 15625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((3 / 4 : ℝ) - δ) * ((1 / 4 : ℝ) - x) ^ 3
      + (7643162 / 140625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - 0) * ((1 / 4 : ℝ) - x) ^ 2
      + (40767421 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - 0) ^ 2 * ((1 / 4 : ℝ) - x)
      + (6660067 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - 0) ^ 3
      + (775212 / 15625 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * ((1 / 4 : ℝ) - x) ^ 3
      + (32133907 / 281250 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - 0) * ((1 / 4 : ℝ) - x) ^ 2
      + (24452059 / 281250 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - 0) ^ 2 * ((1 / 4 : ℝ) - x)
      + (2049331 / 93750 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - 0) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_0 {δ x : ℝ}
    (hδ0 : (1 / 3 : ℝ) ≤ δ) (hδ1 : δ ≤ (3 / 4 : ℝ))
    (hx0 : 0 ≤ x) (hx1 : x ≤ (1 / 4 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (1 / 3 : ℝ) := by linarith
  have hb : 0 ≤ (3 / 4 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - 0 := by linarith
  have hd : 0 ≤ (1 / 4 : ℝ) - x := by linarith
  rw [weighted_identity_0]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 1. -/
private theorem weighted_identity_1 (δ x : ℝ) :
    weightedCert δ x =
      (20016128 / 140625 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * ((3 / 8 : ℝ) - x) ^ 3
      + (453749696 / 1265625 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) * ((3 / 8 : ℝ) - x) ^ 2
      + (126960608 / 421875 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - x)
      + (2374144 / 28125 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) ^ 3
      + (286706224 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((13 / 24 : ℝ) - δ) * ((3 / 8 : ℝ) - x) ^ 3
      + (202378384 / 421875 : ℝ) * (δ - (1 / 3 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (1 / 4 : ℝ)) * ((3 / 8 : ℝ) - x) ^ 2
      + (44100532 / 140625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (1 / 4 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - x)
      + (185292 / 3125 : ℝ) * (δ - (1 / 3 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (1 / 4 : ℝ)) ^ 3
      + (319644572 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - x) ^ 3
      + (745967956 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) * ((3 / 8 : ℝ) - x) ^ 2
      + (188662738 / 421875 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - x)
      + (6155593 / 56250 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_1 {δ x : ℝ}
    (hδ0 : (1 / 3 : ℝ) ≤ δ) (hδ1 : δ ≤ (13 / 24 : ℝ))
    (hx0 : (1 / 4 : ℝ) ≤ x) (hx1 : x ≤ (3 / 8 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (1 / 3 : ℝ) := by linarith
  have hb : 0 ≤ (13 / 24 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (1 / 4 : ℝ) := by linarith
  have hd : 0 ≤ (3 / 8 : ℝ) - x := by linarith
  rw [weighted_identity_1]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 2. -/
private theorem weighted_identity_2 (δ x : ℝ) :
    weightedCert δ x =
      (9496576 / 28125 : ℝ) * ((7 / 16 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (346849408 / 421875 : ℝ) * ((7 / 16 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (169808128 / 253125 : ℝ) * ((7 / 16 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (234075136 / 1265625 : ℝ) * ((7 / 16 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) ^ 3
      + (12831832 / 28125 : ℝ) * (δ - (1 / 3 : ℝ)) * ((7 / 16 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (382419256 / 421875 : ℝ) * (δ - (1 / 3 : ℝ)) * ((7 / 16 : ℝ) - δ) * (x - (3 / 8 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (137822176 / 253125 : ℝ) * (δ - (1 / 3 : ℝ)) * ((7 / 16 : ℝ) - δ) * (x - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (114657152 / 1265625 : ℝ) * (δ - (1 / 3 : ℝ)) * ((7 / 16 : ℝ) - δ) * (x - (3 / 8 : ℝ)) ^ 3
      + (4746379 / 18750 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (21426247 / 46875 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (18421366 / 84375 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (5051672 / 421875 : ℝ) * (δ - (1 / 3 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_2 {δ x : ℝ}
    (hδ0 : (1 / 3 : ℝ) ≤ δ) (hδ1 : δ ≤ (7 / 16 : ℝ))
    (hx0 : (3 / 8 : ℝ) ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (1 / 3 : ℝ) := by linarith
  have hb : 0 ≤ (7 / 16 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (3 / 8 : ℝ) := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [weighted_identity_2]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 3. -/
private theorem weighted_identity_3 (δ x : ℝ) :
    weightedCert δ x =
      (18985516 / 9375 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * ((7 / 16 : ℝ) - x) ^ 3
      + (228096358 / 46875 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) * ((7 / 16 : ℝ) - x) ^ 2
      + (1596319717 / 421875 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) ^ 2 * ((7 / 16 : ℝ) - x)
      + (158715301 / 168750 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (3 / 8 : ℝ)) ^ 3
      + (125171536 / 28125 : ℝ) * (δ - (7 / 16 : ℝ)) * ((13 / 24 : ℝ) - δ) * ((7 / 16 : ℝ) - x) ^ 3
      + (4372062104 / 421875 : ℝ) * (δ - (7 / 16 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (3 / 8 : ℝ)) * ((7 / 16 : ℝ) - x) ^ 2
      + (9723989132 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (3 / 8 : ℝ)) ^ 2 * ((7 / 16 : ℝ) - x)
      + (446600158 / 253125 : ℝ) * (δ - (7 / 16 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (3 / 8 : ℝ)) ^ 3
      + (98489488 / 28125 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * ((7 / 16 : ℝ) - x) ^ 3
      + (3629436632 / 421875 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) * ((7 / 16 : ℝ) - x) ^ 2
      + (8716491356 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) ^ 2 * ((7 / 16 : ℝ) - x)
      + (451110494 / 253125 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (3 / 8 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_3 {δ x : ℝ}
    (hδ0 : (7 / 16 : ℝ) ≤ δ) (hδ1 : δ ≤ (13 / 24 : ℝ))
    (hx0 : (3 / 8 : ℝ) ≤ x) (hx1 : x ≤ (7 / 16 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (7 / 16 : ℝ) := by linarith
  have hb : 0 ≤ (13 / 24 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (3 / 8 : ℝ) := by linarith
  have hd : 0 ≤ (7 / 16 : ℝ) - x := by linarith
  rw [weighted_identity_3]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 4. -/
private theorem weighted_identity_4 (δ x : ℝ) :
    weightedCert δ x =
      (2539444816 / 84375 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * ((15 / 32 : ℝ) - x) ^ 3
      + (31596392888 / 421875 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) * ((15 / 32 : ℝ) - x) ^ 2
      + (340078052 / 5625 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) ^ 2 * ((15 / 32 : ℝ) - x)
      + (244542046 / 15625 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) ^ 3
      + (14763936976 / 253125 : ℝ) * (δ - (7 / 16 : ℝ)) * ((47 / 96 : ℝ) - δ) * ((15 / 32 : ℝ) - x) ^ 3
      + (177773322488 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (7 / 16 : ℝ)) * ((15 / 32 : ℝ) - x) ^ 2
      + (1823608708 / 16875 : ℝ) * (δ - (7 / 16 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (7 / 16 : ℝ)) ^ 2 * ((15 / 32 : ℝ) - x)
      + (3643313738 / 140625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (7 / 16 : ℝ)) ^ 3
      + (3028756276 / 84375 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * ((15 / 32 : ℝ) - x) ^ 3
      + (111523290074 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) * ((15 / 32 : ℝ) - x) ^ 2
      + (1176459907 / 16875 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) ^ 2 * ((15 / 32 : ℝ) - x)
      + (4917185023 / 281250 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_4 {δ x : ℝ}
    (hδ0 : (7 / 16 : ℝ) ≤ δ) (hδ1 : δ ≤ (47 / 96 : ℝ))
    (hx0 : (7 / 16 : ℝ) ≤ x) (hx1 : x ≤ (15 / 32 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (7 / 16 : ℝ) := by linarith
  have hb : 0 ≤ (47 / 96 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (7 / 16 : ℝ) := by linarith
  have hd : 0 ≤ (15 / 32 : ℝ) - x := by linarith
  rw [weighted_identity_4]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 5. -/
private theorem weighted_identity_5 (δ x : ℝ) :
    weightedCert δ x =
      (978168184 / 15625 : ℝ) * ((89 / 192 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (18813276736 / 140625 : ℝ) * ((89 / 192 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (35218400768 / 421875 : ℝ) * ((89 / 192 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (5172912128 / 421875 : ℝ) * ((89 / 192 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) ^ 3
      + (16090141132 / 140625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((89 / 192 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (96418689376 / 421875 : ℝ) * (δ - (7 / 16 : ℝ)) * ((89 / 192 : ℝ) - δ) * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (153992389888 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((89 / 192 : ℝ) - δ) * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (9444610048 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) * ((89 / 192 : ℝ) - δ) * (x - (15 / 32 : ℝ)) ^ 3
      + (16605569327 / 281250 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (48942554668 / 421875 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (74695703584 / 1265625 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (846181888 / 421875 : ℝ) * (δ - (7 / 16 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_5 {δ x : ℝ}
    (hδ0 : (7 / 16 : ℝ) ≤ δ) (hδ1 : δ ≤ (89 / 192 : ℝ))
    (hx0 : (15 / 32 : ℝ) ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (7 / 16 : ℝ) := by linarith
  have hb : 0 ≤ (89 / 192 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (15 / 32 : ℝ) := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [weighted_identity_5]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 6. -/
private theorem weighted_identity_6 (δ x : ℝ) :
    weightedCert δ x =
      (16605569327 / 281250 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (48942554668 / 421875 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (74695703584 / 1265625 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (846181888 / 421875 : ℝ) * ((47 / 96 : ℝ) - δ) ^ 2 * (x - (15 / 32 : ℝ)) ^ 3
      + (1902333058 / 15625 : ℝ) * (δ - (89 / 192 : ℝ)) * ((47 / 96 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (33117176432 / 140625 : ℝ) * (δ - (89 / 192 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (48263474816 / 421875 : ℝ) * (δ - (89 / 192 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (709572608 / 1265625 : ℝ) * (δ - (89 / 192 : ℝ)) * ((47 / 96 : ℝ) - δ) * (x - (15 / 32 : ℝ)) ^ 3
      + (9834370046 / 140625 : ℝ) * (δ - (89 / 192 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (59372670128 / 421875 : ℝ) * (δ - (89 / 192 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (96453236864 / 1265625 : ℝ) * (δ - (89 / 192 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (6783698944 / 1265625 : ℝ) * (δ - (89 / 192 : ℝ)) ^ 2 * (x - (15 / 32 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_6 {δ x : ℝ}
    (hδ0 : (89 / 192 : ℝ) ≤ δ) (hδ1 : δ ≤ (47 / 96 : ℝ))
    (hx0 : (15 / 32 : ℝ) ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (89 / 192 : ℝ) := by linarith
  have hb : 0 ≤ (47 / 96 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (15 / 32 : ℝ) := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [weighted_identity_6]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 7. -/
private theorem weighted_identity_7 (δ x : ℝ) :
    weightedCert δ x =
      (757189069 / 168750 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (10844068466 / 1265625 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (5392355528 / 1265625 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (211990592 / 1265625 : ℝ) * ((13 / 24 : ℝ) - δ) ^ 2 * (x - (7 / 16 : ℝ)) ^ 3
      + (2697642292 / 253125 : ℝ) * (δ - (47 / 96 : ℝ)) * ((13 / 24 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (8871775024 / 421875 : ℝ) * (δ - (47 / 96 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (7 / 16 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (4796124992 / 421875 : ℝ) * (δ - (47 / 96 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (7 / 16 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (1227595264 / 1265625 : ℝ) * (δ - (47 / 96 : ℝ)) * ((13 / 24 : ℝ) - δ) * (x - (7 / 16 : ℝ)) ^ 3
      + (1804441976 / 253125 : ℝ) * (δ - (47 / 96 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (19267293856 / 1265625 : ℝ) * (δ - (47 / 96 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (12355896448 / 1265625 : ℝ) * (δ - (47 / 96 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (232465408 / 140625 : ℝ) * (δ - (47 / 96 : ℝ)) ^ 2 * (x - (7 / 16 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_7 {δ x : ℝ}
    (hδ0 : (47 / 96 : ℝ) ≤ δ) (hδ1 : δ ≤ (13 / 24 : ℝ))
    (hx0 : (7 / 16 : ℝ) ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (47 / 96 : ℝ) := by linarith
  have hb : 0 ≤ (13 / 24 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (7 / 16 : ℝ) := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [weighted_identity_7]
  positivity

/-- Exact unnormalised Bernstein identity on certificate leaf 8. -/
private theorem weighted_identity_8 (δ x : ℝ) :
    weightedCert δ x =
      (79911143 / 2531250 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (133250549 / 2531250 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (59753687 / 2531250 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (227017 / 140625 : ℝ) * ((3 / 4 : ℝ) - δ) ^ 2 * (x - (1 / 4 : ℝ)) ^ 3
      + (123984008 / 1265625 : ℝ) * (δ - (13 / 24 : ℝ)) * ((3 / 4 : ℝ) - δ) * ((1 / 2 : ℝ) - x) ^ 3
      + (222232144 / 1265625 : ℝ) * (δ - (13 / 24 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - (1 / 4 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (117107722 / 1265625 : ℝ) * (δ - (13 / 24 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - (1 / 4 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (15636236 / 1265625 : ℝ) * (δ - (13 / 24 : ℝ)) * ((3 / 4 : ℝ) - δ) * (x - (1 / 4 : ℝ)) ^ 3
      + (4098662 / 46875 : ℝ) * (δ - (13 / 24 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x) ^ 3
      + (24871798 / 140625 : ℝ) * (δ - (13 / 24 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) * ((1 / 2 : ℝ) - x) ^ 2
      + (5401058 / 46875 : ℝ) * (δ - (13 / 24 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - x)
      + (3379412 / 140625 : ℝ) * (δ - (13 / 24 : ℝ)) ^ 2 * (x - (1 / 4 : ℝ)) ^ 3 := by
  unfold weightedCert oldCert oldRest countNum countDen countD countP
  norm_num [theta, ell, h, ly, kappa, endpointMargin]
  ring

theorem weighted_leaf_8 {δ x : ℝ}
    (hδ0 : (13 / 24 : ℝ) ≤ δ) (hδ1 : δ ≤ (3 / 4 : ℝ))
    (hx0 : (1 / 4 : ℝ) ≤ x) (hx1 : x ≤ (1 / 2 : ℝ)) :
    0 ≤ weightedCert δ x := by
  have ha : 0 ≤ δ - (13 / 24 : ℝ) := by linarith
  have hb : 0 ≤ (3 / 4 : ℝ) - δ := by linarith
  have hc : 0 ≤ x - (1 / 4 : ℝ) := by linarith
  have hd : 0 ≤ (1 / 2 : ℝ) - x := by linarith
  rw [weighted_identity_8]
  positivity

theorem oldCert_nonneg {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 3) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ oldCert δ x := old_leaf_0 hδ0 hδ1 hx0 hx1

theorem weightedCert_nonneg {δ x : ℝ}
    (hδ0 : 1 / 3 ≤ δ) (hδ1 : δ ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ weightedCert δ x := by
  by_cases hxa : x ≤ 1 / 4
  · apply weighted_leaf_0 <;> linarith
  · by_cases hda : δ ≤ 13 / 24
    · by_cases hxb : x ≤ 3 / 8
      · apply weighted_leaf_1 <;> linarith
      · by_cases hdb : δ ≤ 7 / 16
        · apply weighted_leaf_2 <;> linarith
        · by_cases hxc : x ≤ 7 / 16
          · apply weighted_leaf_3 <;> linarith
          · by_cases hdc : δ ≤ 47 / 96
            · by_cases hxd : x ≤ 15 / 32
              · apply weighted_leaf_4 <;> linarith
              · by_cases hdd : δ ≤ 89 / 192
                · apply weighted_leaf_5 <;> linarith
                · apply weighted_leaf_6 <;> linarith
            · apply weighted_leaf_7 <;> linarith
    · apply weighted_leaf_8 <;> linarith

end
end WeightedQRH
