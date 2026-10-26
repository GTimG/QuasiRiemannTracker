/- Copyright (c) 2026 Sil. Apache-2.0.
Exact parameters of the independently audited 0.8746935 return.
This module proves arithmetic, not the analytical source theorem. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace Candidate.FourthPower
noncomputable section

def theta : ℝ := 1749387 / 2000000
def h : ℝ := 39823 / 50000
def reserve : ℝ := 1 / 1000000000
def incumbent : ℝ := 8747759 / 10000000
def kappa : ℝ := 2 * theta - 1
def ell : ℝ := 11 / 3 - 4 * theta
def x : ℝ := 1 + ell - h
def y : ℝ := h - 2 * ell
def eta : ℝ := 1 / 10000000
def physicalSlope : ℝ := 12567 / 4000
def physicalIntercept : ℝ := 4 * ell / (h + eta) + physicalSlope / 25
def d0 : ℝ := 1 / 200
def dplus : ℝ := h + 1 / 10000000000
def ds : ℝ := 2 * y / (1 + 6 * kappa / 25)
def dk : ℝ := 2 * y / (2 - physicalIntercept + physicalSlope / 25)
def sourceB : ℝ := 99999 / 100000
def sourceSlope : ℝ := 93 / 25
def sourceCap : ℝ := 3 / 50

theorem parameters_exact :
    kappa = 749387 / 1000000 ∧ ell = 251839 / 1500000 ∧
    x = 557149 / 1500000 ∧ y = 172753 / 375000 := by
  norm_num [kappa, ell, x, y, theta, h]

theorem physical_intercept_exact :
    physicalIntercept = 2314985422301 / 2389380300000 := by
  norm_num [physicalIntercept, physicalSlope, ell, theta, h, eta]

theorem joins_exact :
    ds = 34550600 / 44244483 ∧
    dk = 1375908716553 / 1727530375000 ∧
    dplus = 7964600001 / 10000000000 := by
  norm_num [ds, dk, dplus, physical_intercept_exact, physicalSlope,
    y, ell, kappa, theta, h]

theorem geometry_identities :
    x + y = 1 - ell ∧
    theta - (4 + y - x) / 6 = x / 2 + (y - x) / 12 := by
  dsimp [x, y, ell]
  constructor <;> ring

theorem conductor_order :
    d0 < y ∧ y < ds ∧ ds < dk ∧ dk < dplus ∧ dplus < 2 * y := by
  rw [joins_exact.1, joins_exact.2.1, joins_exact.2.2, parameters_exact.2.2.2]
  norm_num [d0]

theorem feedback_domain :
    7 / 10 < kappa ∧ dplus < 1 ∧ y < 1 / 2 ∧ theta < incumbent ∧
    (5 / 288 + 25 / 784 : ℝ) < 1 / 8 := by
  rw [parameters_exact.1, joins_exact.2.2, parameters_exact.2.2.2]
  norm_num [theta, incumbent]

/-- An algebraic domain, not an assumed analytical moment bound. -/
structure Face where
  intercept : ℝ
  slope : ℝ
  cap : ℝ

def countFace : Face := ⟨sourceB, sourceSlope, 5499 / 100000⟩
def physicalFace : Face := ⟨physicalIntercept, physicalSlope, 43 / 1000⟩
def xFace : Face :=
  ⟨48113075876991 / 50000000000000, 157406588190789 / 50000000000000,
    549989 / 10000000⟩
def yFace : Face :=
  ⟨48369515545621 / 50000000000000, 163653997694883 / 50000000000000,
    549989 / 10000000⟩

def Face.Included (f : Face) : Prop :=
  0 ≤ f.cap ∧ f.cap ≤ sourceCap ∧ 0 ≤ f.slope ∧
  f.slope ≤ sourceSlope ∧
  f.intercept + (sourceSlope - f.slope) * f.cap ≤ sourceB

theorem countFace_included : countFace.Included := by
  norm_num [Face.Included, countFace, sourceB, sourceSlope, sourceCap]

theorem physicalFace_included : physicalFace.Included := by
  norm_num [Face.Included, physicalFace, physical_intercept_exact,
    physicalSlope, sourceB, sourceSlope, sourceCap]

theorem xFace_included : xFace.Included := by
  norm_num [Face.Included, xFace, sourceB, sourceSlope, sourceCap]

theorem yFace_included : yFace.Included := by
  norm_num [Face.Included, yFace, sourceB, sourceSlope, sourceCap]

/-- Whole-domain inclusion, not merely an isolated rational test point. -/
theorem Face.source_domain {f : Face} (hf : f.Included) {P S : ℝ}
    (_hS : 0 ≤ S) (hcap : S ≤ f.cap)
    (hbudget : P + f.slope * S ≤ f.intercept) :
    S ≤ sourceCap ∧ P + sourceSlope * S ≤ sourceB := by
  rcases hf with ⟨_, hc, _, hl, hb⟩
  have hslope : 0 ≤ sourceSlope - f.slope := sub_nonneg.mpr hl
  have hm := mul_le_mul_of_nonneg_left hcap hslope
  exact ⟨hcap.trans hc, by nlinarith⟩

theorem physical_inclusion_margins :
    sourceB - physicalIntercept = 9296372987 / 298672537500 ∧
    sourceB - physicalIntercept -
      (sourceSlope - physicalSlope) * (43 / 1000) =
        598385603263 / 95575212000000 := by
  norm_num [physical_intercept_exact, physicalSlope, sourceB, sourceSlope]

end
end Candidate.FourthPower
