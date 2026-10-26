import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The numeric certificates of a first-level LOW child with the second step, at chosen slacks. Released under Apache
2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization Cycle63.Certificate

bracket firstAmpFirst_enclosure (digits := 9) : firstAmp firstCellTop
  using [twoLevelLedgerSlope_enclosure, twoLevelLedgerIntercept_enclosure]
  unfolding [firstAmp, twoLevelSlope, twoLevelPlaneIntercept, planeAmplifier, amplifierRatio, twoLevelPrice,
    twoLevelIntercept, regionPrice, regionIntercept, regionSlope, secondRatio, amplifierCost, density, regionMargin,
    allowanceUnit, lowReserveWeight, slotPrice, betaBound, secondJunction, firstJunction, firstCellTop, slotFloor,
    cellMesh]

bracket firstLowReserve_enclosure (digits := 12) : lowReserveAt twoLevelPrice twoLevelIntercept firstJunction
  unfolding *

/-- The certificates of the first-level LOW child with the second step hold for every grid of mesh `1/G` with
`G ≥ 10⁶` and all paddings with `2 ωmax + εpad ≤ 9·10⁻⁷`, at the width bound `1 + 1/100`, the reflection slack
`1/1000` and margin `7/2500`, with the slacks of the length and of the amplifier equal to the terms they bound. -/
theorem twoLevelCertificates_of_small {G : ℕ} {εpad ωmax : ℝ} (hG : 1000000 ≤ G) (hω : 0 ≤ ωmax)
    (hsmall : 2*ωmax + εpad ≤ 9/10000000) :
    TwoLevelCertificates G (1 + 1/100) εpad ωmax (1/1000) (7/2500) (secondSlope/G)
      (amplifierRatio slotPrice 1 secondJunction*(2*ωmax + εpad) +
        amplifierRatio slotPrice 1 secondJunction*(1 + 6*slotPrice)/G) where
  grid := hG
  width := by linarith [firstAmpFirst_enclosure.1]
  small := hsmall
  mesh := by
    have h : planeSlope (regionPrice secondJunction) (regionIntercept secondJunction regionMargin) firstJunction ≤ 4 :=
      by linarith [twoLevelLedgerSlope_enclosure.2]
    have hm : cellMesh = 1/100000000 := by norm_num [cellMesh, allowanceUnit]
    show (twoLevelSlope - 1)*cellMesh ≤ 1/10000000
    unfold twoLevelSlope twoLevelPrice twoLevelIntercept
    rw [hm]
    nlinarith
  reflect := by
    intro b hb₁ hb₂
    have h := min_le_of_affine (f := fun x => -childOvershoot x)
      (fun x => by linarith [childOvershoot_affine x, childOvershoot_affine 0, childOvershoot_affine 1]) hb₁ hb₂
    have h₁ := childOvershootFirst_enclosure
    have h₂ := childOvershootTop_enclosure
    have hmin : -(2/1000 + 3/10000 : ℝ) ≤ min (-childOvershoot firstCellTop) (-childOvershoot slotTop) :=
      le_min (by linarith [h₁.2]) (by linarith [h₂.2])
    have := hmin.trans h
    linarith
  reflect_margin := by norm_num
  reflect_small := by norm_num
  room := by
    have hr := firstLowReserve_enclosure
    have h₁ := directDeletionRoomFirst_enclosure
    have h₂ := directDeletionRoomTop_enclosure
    have hrate : directDeletionRate ≤ 15/100 := by
      norm_num [directDeletionRate, firstJunction, slotPrice, betaBound]
    have hrate0 : 0 ≤ directDeletionRate := by
      norm_num [directDeletionRate, firstJunction, slotPrice, betaBound]
    have hpad : (1 + 1/100 - 1) + εpad + 2*ωmax ≤ 1/100 + 9/10000000 := by linarith
    have hprod := mul_le_mul_of_nonneg_left hpad hrate0
    unfold directDeletionMargin
    apply le_min <;> nlinarith
  length := le_rfl
  amp := le_rfl
end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
