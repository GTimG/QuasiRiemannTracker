/- A48 (AI-assisted, for liqsweep). WORK IN PROGRESS. Apache 2.0.
Record point of the count-side use of Collet's interior affine moment (cycle61 Thm 2.2):
theta = 2187109/2500000 = 0.8748436, h = 497/625, Gao's q0 = 67/100 (lambda, B unchanged).
The gate facts below are proved. `endpoint_certificate` is NOT yet formalized (explicit sorry). -/
import Candidate.CountAffine.ClosedForm

set_option autoImplicit false

namespace Cycle61.CountAffine.Record
noncomputable section
open Cycle61.CountAffine

def theta : ℝ := 2187109/2500000
def h : ℝ := 497/625
def ell : ℝ := 11/3 - 4*theta
def x : ℝ := 1 + ell - h
def y : ℝ := h - 2*ell
def kappaStar : ℝ := 2*theta - 1
def dMinus : ℝ := h - 1/1000
def dPlus : ℝ := h + 1/10000000000
def t0 : ℝ := 1/1000
def d0 : ℝ := 1/200

/-! Collet/Gao gates at the record point (all proved by exact rational arithmetic). -/

theorem plain_window : (41/100:ℝ) ≤ 1 - y/dMinus ∧ 1 - y/dPlus + t0 ≤ 264/625 := by
  constructor <;> norm_num [y, ell, theta, h, dMinus, dPlus, t0]

theorem slot_window :
    (17/500:ℝ) ≤ (B - 2*(1 - y/dPlus + t0))/lambda ∧ (B - 2*(1 - y/dMinus))/lambda ≤ 37/1000 := by
  constructor <;> norm_num [y, ell, theta, h, dMinus, dPlus, t0, B, lambda]

theorem shift_gate : 2*y/dMinus - 1 ≤ 4/25 := by
  norm_num [y, ell, theta, h, dMinus]

theorem kappa_window : (7/10:ℝ) ≤ kappaStar ∧ kappaStar ≤ 3/4 := by
  constructor <;> norm_num [kappaStar, theta]

theorem floor_gate : 0 < theta - (51/100 + h/3 + 51*ell/100) := by
  norm_num [theta, h, ell]

theorem lower_row_gate : 0 < theta - (7/8 - 49*h/150 + 7*ell/8 + 33*d0/50) := by
  norm_num [theta, h, ell, d0]

theorem supply_gates : (7/37:ℝ)*(7/8) ≤ ell ∧ (4/21:ℝ) < ell/dPlus ∧ (1/3:ℝ) < 2*ell := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ell, theta, dPlus, h]

theorem geometry_gates : 0 < ell ∧ ell < x ∧ x < y ∧ y < 1/2 ∧ y < 2*x ∧ h < 2*y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [ell, x, y, theta, h]

/-- The record h lies outside Gao's coarse interval `793/1000 < h < 795/1000`; the constants step must
widen those coarse facts. -/
theorem h_above_gao_interval : (795/1000:ℝ) < h := by norm_num [h]

/-! The endpoint claim with the new count (statement only). -/

/-- Collet's count `R_kappa` (cycle61 (3.9)), cleared form. -/
def kappaCoefficient (κ p : ℝ) : ℝ := 2*(1-p)*(3*κ-p)/(3*κ*(3-p)-2*p)
def kappaRowDen (κ d p : ℝ) : ℝ := (5/6-d)+d*kappaCoefficient κ p
def kappaCountR (κ d p : ℝ) : ℝ := 1-d+d*kappaCoefficient κ p*(5/6-d)/(2*kappaRowDen κ d p)

/-- The closed-form boxes of A44's exact certificate at this point (each delta-slice is an upper set). -/
def regionA44 (δ p : ℝ) : Prop :=
  (57/128 ≤ δ ∧ δ ≤ 115/256 ∧ 63/128 ≤ p ∧ p ≤ 1/2) ∨
  (115/256 ≤ δ ∧ δ ≤ 29/64 ∧ 31/64 ≤ p ∧ p ≤ 1/2) ∨
  (29/64 ≤ δ ∧ δ ≤ 59/128 ∧ 15/32 ≤ p ∧ p ≤ 1/2) ∨
  (59/128 ≤ δ ∧ δ ≤ 119/256 ∧ 31/64 ≤ p ∧ p ≤ 1/2) ∨
  (119/256 ≤ δ ∧ δ ≤ 15/32 ∧ 63/128 ≤ p ∧ p ≤ 1/2) ∨
  (15/32 ≤ δ ∧ δ ≤ 31/64 ∧ 7/16 ≤ p ∧ p ≤ 1/2) ∨
  (31/64 ≤ δ ∧ δ ≤ 63/128 ∧ 15/32 ≤ p ∧ p ≤ 1/2)

open Classical in
/-- The new class count: `min(R_kappa, max(R*, old plain at N))` on the closed-form region. -/
def newCount (κ d p : ℝ) : ℝ :=
  if regionA44 d p then min (kappaCountR κ d p) (newBranch κ d p) else kappaCountR κ d p

def newCapacity (d : ℝ) : ℝ := (2*y-(2-B)*d)/lambda
def oldCapacity (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)

/-- Collet's row exponent (cycle61 (3.14)) with the new count. -/
def rowExponent (κ d C δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+d*(1/4+3*newCount κ δ p/4-17/50)-δ*p*C/2

/-- The three certified rows (top d = h saving 1e-6; junction d- saving 1e-5; half saving 1e-3). -/
def EndpointClaim : Prop :=
  ∀ δ ∈ Set.Icc (0:ℝ) (3/4), ∀ p ∈ Set.Icc (0:ℝ) (1/2),
    rowExponent kappaStar h (newCapacity h) δ p < theta - 1/1000000 ∧
    rowExponent kappaStar dMinus (oldCapacity kappaStar dMinus) δ p < theta - 1/100000 ∧
    rowExponent kappaStar (1/2) (oldCapacity kappaStar (1/2)) δ p < theta - 1/1000

/-- STEP (endpoint certificate): NOT YET FORMALIZED.
Exact certificate (A44, agents/A44_close_record/out/closed_form_cert_gatefeasible.txt, old_rows_6boxes.txt):
top row 199 R_kappa Bernstein boxes + 8 closed-form boxes (min Bernstein coefficient 6.1e-8),
junction 6 boxes (min 1.897e-4), half row 1 box (min 5.203e-2).  Still to formalize: the Lean box
certificates (cf. RegionCert.lean for the pattern), and the closed-form gates on the boxes of
`regionA44` lying outside R1 ∪ R2 (RegionFacts.lean currently certifies R1 ∪ R2 only). -/
theorem endpoint_certificate : EndpointClaim := by
  sorry

end
end Cycle61.CountAffine.Record
