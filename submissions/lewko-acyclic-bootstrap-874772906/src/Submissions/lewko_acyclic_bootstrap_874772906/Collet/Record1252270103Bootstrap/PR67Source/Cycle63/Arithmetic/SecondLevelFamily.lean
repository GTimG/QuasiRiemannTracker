import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelPosition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The finite family of the second step's ledgers: the positions on a grid of mesh `1/N` whose facts hold, and every
first-level LOW child that the second step bounds lies at one of them. Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63

noncomputable section
open Cycle63.Optimization

/-! The thresholds of the second step's eventual bounds depend on its ledger, so the second step is run over a
finite family of ledgers and its thresholds are taken uniform over the family. The family is indexed by the points
of the grid of mesh `1/N` in `[0, 1]` for the plane's intercept, the slot top, the window bottom and the sum
bottom; the plain-loss cap is the one that `childPosition` gives a child at these grid points. -/

/-- The coordinates of the grid positions of mesh `1/N`: four grid points in `[0, 1]`. -/
abbrev GridCoordinates (N : ℕ) : Type := Fin (N + 1) × Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

/-- The position of the second step at the grid coordinates `i` of mesh `1/N`. -/
def gridPosition (N : ℕ) (i : GridCoordinates N) : SecondPosition where
  intercept := (i.1 : ℝ)/N
  slotTop := (i.2.1 : ℝ)/N
  mesh := 1/N
  windowBottom := (i.2.2.1 : ℝ)/N
  sumBottom := (i.2.2.2 : ℝ)/N
  plainLossCap := max 0 (max (1/4 - (i.2.2.1 : ℝ)/N)
    (1/4 - ((i.2.2.2 : ℝ)/N - (9/2)*((i.2.1 : ℝ)/N) - 1/100)/2))

/-- The grid positions of mesh `1/N` whose facts hold: the index set of the family of the second step's ledgers. -/
def SecondIndex (N : ℕ) : Type := {i : GridCoordinates N // (gridPosition N i).Facts}

instance (N : ℕ) : Finite (SecondIndex N) := Subtype.finite

/-- The ledger of the second step at a grid position of the family. -/
@[instance_reducible]
def secondFamily (N : ℕ) (i : SecondIndex N) : AffineLedger := secondLedger (gridPosition N i.1) i.2

/-- The ledger of the second step depends on the position only. -/
theorem secondLedger_congr {P P' : SecondPosition} (hP : P = P') (h : P.Facts) (h' : P'.Facts) :
    secondLedger P h = secondLedger P' h' := by
  subst hP
  rfl

/-- The grid point of mesh `1/N` at or above a real `x ≥ 0` is the coordinate `⌈x N⌉` over `N`. -/
theorem gridUp_eq_coordinate {N : ℕ} {x : ℝ} (hx : 0 ≤ x) : gridUp (1/N) x = ((⌈x*N⌉).toNat : ℝ)/N := by
  have hc : 0 ≤ ⌈x*N⌉ := Int.ceil_nonneg (mul_nonneg hx (Nat.cast_nonneg N))
  unfold gridUp
  rw [div_div_eq_mul_div, div_one, mul_one_div]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hc).symm

/-- The grid point of mesh `1/N` at or below a real `x ≥ 0` is the coordinate `⌊x N⌋` over `N`. -/
theorem gridDown_eq_coordinate {N : ℕ} {x : ℝ} (hx : 0 ≤ x) : gridDown (1/N) x = ((⌊x*N⌋).toNat : ℝ)/N := by
  have hc : 0 ≤ ⌊x*N⌋ := Int.floor_nonneg.mpr (mul_nonneg hx (Nat.cast_nonneg N))
  unfold gridDown
  rw [div_div_eq_mul_div, div_one, mul_one_div]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hc).symm

/-- The coordinates `⌈x N⌉` and `⌊x N⌋` of a real `x ≤ 1` are at most `N`. -/
theorem coordinate_le {N : ℕ} {x : ℝ} (hx : x ≤ 1) : (⌈x*N⌉).toNat ≤ N ∧ (⌊x*N⌋).toNat ≤ N := by
  have h : ⌈x*N⌉ ≤ N := Int.ceil_le.mpr (by push_cast; exact mul_le_of_le_one_left (Nat.cast_nonneg N) hx)
  have h' : ⌊x*N⌋ ≤ N := (Int.floor_le_ceil _).trans h
  omega

/-- A child placed on the grid of mesh `1/N` lies at grid coordinates. -/
theorem exists_gridPosition {N : ℕ} {n₁ n₂ ζ : ℝ} (hN : 0 < N) (hζ : 0 ≤ ζ)
    (h : (childPosition (1/N) n₁ n₂ ζ).Facts) : ∃ i : GridCoordinates N, gridPosition N i = childPosition (1/N) n₁ n₂ ζ := by
  have hg : (0:ℝ) < 1/N := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    positivity
  have hslope := secondSlope_bounds
  have hmin : 0 < min n₁ n₂ := lt_of_lt_of_le h.windowBottom_pos (gridDown_le hg _)
  have hn₁ : 0 < n₁ := lt_of_lt_of_le hmin (min_le_left _ _)
  have hn₂ : 0 < n₂ := lt_of_lt_of_le hmin (min_le_right _ _)
  have hI : n₁ + n₂ + secondSlope*ζ ≤ 1 := (le_gridUp hg _).trans h.intercept_le_one
  have hz : ζ ≤ 1 := (le_gridUp hg _).trans h.slotTop_le_one
  have hslopeζ : 0 ≤ secondSlope*ζ := mul_nonneg (by linarith [hslope.1]) hζ
  have hI₀ : 0 ≤ n₁ + n₂ + secondSlope*ζ := by linarith
  have hs₀ : 0 ≤ n₁ + n₂ := by linarith
  have hs : n₁ + n₂ ≤ 1 := by linarith
  have hm : min n₁ n₂ ≤ 1 := (min_le_left _ _).trans (by linarith)
  refine ⟨(⟨_, Nat.lt_succ_of_le (coordinate_le hI).1⟩, ⟨_, Nat.lt_succ_of_le (coordinate_le hz).1⟩,
    ⟨_, Nat.lt_succ_of_le (coordinate_le hm).2⟩, ⟨_, Nat.lt_succ_of_le (coordinate_le hs).2⟩), ?_⟩
  simp only [gridPosition, childPosition, gridUp_eq_coordinate hI₀, gridUp_eq_coordinate hζ,
    gridDown_eq_coordinate hmin.le, gridDown_eq_coordinate hs₀]

/-- The ledger of the second step at a child placed on the grid of mesh `1/N` is a ledger of the family. -/
theorem childLedger_mem_family {N : ℕ} {n₁ n₂ ζ : ℝ} (hN : 0 < N) (hζ : 0 ≤ ζ)
    (h : (childPosition (1/N) n₁ n₂ ζ).Facts) :
    ∃ i : SecondIndex N, secondFamily N i = secondLedger (childPosition (1/N) n₁ n₂ ζ) h := by
  obtain ⟨i, hi⟩ := exists_gridPosition hN hζ h
  exact ⟨⟨i, hi ▸ h⟩, secondLedger_congr hi _ _⟩

/-- A child placed on the grid lies in the plain window of its position. -/
theorem childPosition_window {g n₁ n₂ ζ : ℝ} (hg : 0 < g) :
    PlainWindow (childPosition g n₁ n₂ ζ).windowBottom (childPosition g n₁ n₂ ζ).sumBottom
      ((childPosition g n₁ n₂ ζ).slotTop - (childPosition g n₁ n₂ ζ).mesh) (childPosition g n₁ n₂ ζ).slotTop
      secondSlope (childPosition g n₁ n₂ ζ).intercept n₁ n₂ ζ where
  left_ge := (gridDown_le hg _).trans (min_le_left _ _)
  right_ge := (gridDown_le hg _).trans (min_le_right _ _)
  sum_ge := gridDown_le hg _
  slots_ge := by
    show gridUp g ζ - g ≤ ζ
    linarith [gridUp_le hg ζ]
  slots_le := le_gridUp hg ζ
  plane := le_gridUp hg _

/-- The total length of the position of a child exceeds the child's total length by at most `secondSlope` meshes. -/
theorem childPosition_totalA_le {g n₁ n₂ ζ : ℝ} (hg : 0 < g) :
    (childPosition g n₁ n₂ ζ).totalA ≤ n₁ + n₂ + ζ + secondSlope*g := by
  show gridUp g (n₁ + n₂ + secondSlope*ζ) - (secondSlope - 1)*(gridUp g ζ - g) ≤ n₁ + n₂ + ζ + secondSlope*g
  have h₁ := gridUp_le hg (n₁ + n₂ + secondSlope*ζ)
  have h₂ : 0 ≤ (secondSlope - 1)*(gridUp g ζ - ζ) :=
    mul_nonneg (by linarith [secondSlope_bounds.1]) (by linarith [le_gridUp hg ζ])
  linarith

/-- The amplifier of the position of a child is at most the amplifier of the child's overshoot over the old region,
with the overshoot raised by `1 + 6κ` meshes. -/
theorem childPosition_amp_le {g n₁ n₂ ζ : ℝ} (hg : 0 < g) :
    (childPosition g n₁ n₂ ζ).amp ≤
      amplifierRatio slotPrice 1 secondJunction*(n₁ + n₂ + 6*slotPrice*ζ - 1 + (1 + 6*slotPrice)*g) +
        lowReserveWeight := by
  show amplifierRatio slotPrice 1 secondJunction*
      (gridUp g (n₁ + n₂ + secondSlope*ζ) - 1 + (6*slotPrice - secondSlope)*gridUp g ζ) + lowReserveWeight ≤ _
  have h₁ := gridUp_le hg (n₁ + n₂ + secondSlope*ζ)
  have h₂ : (6*slotPrice - secondSlope)*gridUp g ζ ≤ (6*slotPrice - secondSlope)*(ζ + g) :=
    mul_le_mul_of_nonneg_left (gridUp_le hg ζ) (by linarith [secondSlope_bounds.2, slotPrice_bounds.1])
  have h₃ : 0 ≤ secondSlope*g := mul_nonneg (by linarith [secondSlope_bounds.1]) hg.le
  have hin : gridUp g (n₁ + n₂ + secondSlope*ζ) - 1 + (6*slotPrice - secondSlope)*gridUp g ζ ≤
      n₁ + n₂ + 6*slotPrice*ζ - 1 + (1 + 6*slotPrice)*g := by linarith
  have := mul_le_mul_of_nonneg_left hin (by linarith [secondAmplifierRatio_bounds.1] :
    (0:ℝ) ≤ amplifierRatio slotPrice 1 secondJunction)
  linarith

/-- The arithmetic conditions under which the second step applies to a state of width `width`, plain lengths `x₁`,
`x₂` and slot length `z`: its unit `W` is the width and at least the least width of the second step, the lengths in
the unit `W` place the state at a position of the grid of mesh `1/G` whose facts hold, `length` and `amp` are at
least the total length and the amplifier of that position in the units of the state, `loss` is at least
`lossFloor`, and the capacity of the state exceeds its unit by at most `7/2500`:
`x₁ + x₂ + 6 slotPrice z - W ≤ 7/2500`. -/
def SecondStepArithmetic (G : ℕ) (lossFloor width x₁ x₂ z W length amp loss : ℝ) : Prop :=
  W = width ∧ secondStepWidthFloor ≤ W ∧ (childPosition (1/G) (x₁/W) (x₂/W) (z/W)).Facts ∧
    W*(childPosition (1/G) (x₁/W) (x₂/W) (z/W)).totalA ≤ length ∧
    W*(childPosition (1/G) (x₁/W) (x₂/W) (z/W)).amp ≤ amp ∧ lossFloor ≤ loss ∧
    x₁ + x₂ + 6*slotPrice*z - W ≤ 7/2500

/-- Under the arithmetic conditions of the second step, the lengths of the state in its unit `W` lie in the plain
window of a ledger of the family, and the total length and the amplifier of that ledger's cell, in the units of the
state, are at most `length` and `amp`. -/
theorem SecondStepArithmetic.family {G : ℕ} {lossFloor width x₁ x₂ z W length amp loss : ℝ} (hN : 0 < G)
    (hz : 0 ≤ z) (h : SecondStepArithmetic G lossFloor width x₁ x₂ z W length amp loss) :
    ∃ i : SecondIndex G,
      PlainWindow (gridPosition G i.1).windowBottom (gridPosition G i.1).sumBottom
        ((gridPosition G i.1).slotTop - (gridPosition G i.1).mesh) (gridPosition G i.1).slotTop secondSlope
        (gridPosition G i.1).intercept (x₁/W) (x₂/W) (z/W) ∧
      W*(gridPosition G i.1).totalA ≤ length ∧ W*(gridPosition G i.1).amp ≤ amp := by
  obtain ⟨-, hfloor, hfacts, hlength, hamp, -, -⟩ := h
  have hW : 0 < W := lt_of_lt_of_le (by norm_num [secondStepWidthFloor]) hfloor
  have hg : (0:ℝ) < 1/G := by
    have : (0:ℝ) < G := by exact_mod_cast hN
    positivity
  obtain ⟨i, hi⟩ := exists_gridPosition hN (div_nonneg hz hW.le) hfacts
  refine ⟨⟨i, hi ▸ hfacts⟩, ?_⟩
  dsimp only
  rw [hi]
  exact ⟨childPosition_window hg, hlength, hamp⟩

end

end Cycle63

end Record1252270103Bootstrap.PR67
