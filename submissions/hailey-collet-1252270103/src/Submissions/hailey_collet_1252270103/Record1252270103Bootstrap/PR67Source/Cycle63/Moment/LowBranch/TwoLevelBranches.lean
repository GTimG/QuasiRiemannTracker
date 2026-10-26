import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelCertificates
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.DirectBranchFacts
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.SecondStepOfChild
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The arithmetic of the two branches of a first-level LOW child that the old region does not pay: the second step for a
wide child and the direct deletion for a narrow one. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open Cycle63 Cycle63.Optimization

/-- The rate of the direct deletion is between zero and a half. -/
theorem directDeletionRate_bounds : 0 ≤ directDeletionRate ∧ directDeletionRate ≤ 1 / 2 := by
  have hq := firstJunction_mem
  have hκ := slotPrice_bounds
  unfold directDeletionRate
  constructor
  · apply div_nonneg (by linarith [hq.1]) (by linarith [hκ.1])
  · rw [div_le_iff₀ (by linarith [hκ.1])]
    linarith [hq.2, hκ.1]

/-- The direct deletion of a narrow first-level LOW child of the cell `b` is paid. The log norms are those of the own
first ideal `cc`, the other first ideal `dd`, the active conductor `RR`, the own second ideal `eE`, the common radical
`pp`, the common frequency generator `gg`, the inactive set `tt` and the nonunit frequency generator `VV`. -/
theorem two_level_branch_D {b cc dd eE gg tt VV RR pp spad rem x₁ x₂ nominal δ omega : ℝ}
    {G : ℕ} {Mcap εpad ωmax ξR δR gridSlack ampSlack : ℝ}
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop)
    (hcc : 0 ≤ cc) (hdd : 0 ≤ dd) (htt : 0 ≤ tt) (hRd : RR ≤ dd) (hpp : pp ≤ eE)
    (hεpad : 0 ≤ εpad) (hspad : spad ≤ εpad) (homega : 0 ≤ omega) (hωmax : omega ≤ ωmax)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ Mcap - 1)
    (hνdef : nominal = 1 - (max (cc - dd) 0 + gg - tt) - 6 * firstAmp b - omega)
    (hV : VV + tt ≤ nominal + δ)
    (hprime : directDeletionRate * (gg - tt - VV) ≤ (eE - pp) + directDeletionRate * ((eE - gg) + tt))
    (hN4 : x₁ + x₂ + 6 * slotPrice * rem - nominal ≤
      twoLevelOldGap b + 6 * firstAmp b + omega + spad - (min cc dd + ((eE - gg) + tt)))
    (hLr : lowReserveAt twoLevelPrice twoLevelIntercept firstJunction ≤ firstAmp b)
    (hnarrow : nominal + δ < secondStepWidthFloor) :
    0 ≤ max (twoLevelOldGap b + 6 * firstAmp b - (min cc dd + ((eE - gg) + tt))) 0 ∧
    x₁ + x₂ + 6 * slotPrice * rem - nominal ≤
      max (twoLevelOldGap b + 6 * firstAmp b - (min cc dd + ((eE - gg) + tt))) 0 + (omega + εpad) ∧
    directDeletionRate * max (twoLevelOldGap b + 6 * firstAmp b - (min cc dd + ((eE - gg) + tt))) 0 ≤
      firstAmp b + (max (3 * cc - 5 * dd - RR) 0 / 6 + (eE - pp)) -
        lowReserveAt twoLevelPrice twoLevelIntercept firstJunction := by
  obtain ⟨hrate0,hrate2⟩ := directDeletionRate_bounds
  have hroom := directDeletion_certificate hb
  have hr := hcert.room
  unfold directDeletionRoom directDeletionDeficit at hroom
  refine direct_branch_facts (κq := directDeletionRate) (κ := slotPrice) (a := firstAmp b)
    (gbar := twoLevelOldGap b) (L := lowReserveAt twoLevelPrice twoLevelIntercept firstJunction)
    (c := cc) (d := dd) (R := RR) (e := eE) (p₂ := pp) (g₂ := gg) (t₂ := tt) (V := VV) (x₁ := x₁) (x₂ := x₂)
    (rem := rem) (ν := nominal) (δ := δ) (omega := omega) (spad := spad) (εpad := εpad) (ωmax := ωmax)
    (δmax := Mcap - 1) (Mstar := secondStepWidthFloor) hrate0 hrate2 hcc hdd hRd hpp hLr htt homega hεpad hδ hspad
    hωmax hδmax hνdef hV hprime hN4 hnarrow ?_
  linarith [hroom, hr]

/-- The amplifier of the parent of the second step is at most the amplifier of the second step in the cell up to the
slack of the amplifier. -/
theorem two_level_amp_le {b spad omega : ℝ} {G : ℕ} {Mcap εpad ωmax ξR δR gridSlack ampSlack : ℝ}
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (hspad : spad ≤ εpad) (homega : omega ≤ ωmax) :
    secondAmp b + amplifierRatio slotPrice 1 secondJunction * ((omega + spad) + omega) +
      amplifierRatio slotPrice 1 secondJunction * (1 + 6 * slotPrice) / G ≤ secondAmp b + ampSlack := by
  have hK := secondAmplifierRatio_bounds
  have hK0 : 0 ≤ amplifierRatio slotPrice 1 secondJunction := by linarith [hK.1]
  have h := hcert.amp
  have h1 : amplifierRatio slotPrice 1 secondJunction * ((omega + spad) + omega) ≤
      amplifierRatio slotPrice 1 secondJunction * (2 * ωmax + εpad) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  linarith

/-- A first-level LOW child of the cell `b` that is wide enough for the second step, not in the old region and not
reflected into it, has the arithmetic conditions of the second step, with the total length and the amplifier of the
parent of the second step that do not depend on the slots deleted. -/
theorem two_level_branch_L2 {b cc dd eE gg tt spad rem x₁ x₂ nominal δ omega A dl z' lossFloor : ℝ}
    {G : ℕ} {Mcap εpad ωmax ξR δR gridSlack ampSlack : ℝ}
    (hcert : TwoLevelCertificates G Mcap εpad ωmax ξR δR gridSlack ampSlack)
    (hb : firstCellTop ≤ b ∧ b ≤ slotTop) (hξR : 0 < ξR)
    (hcc : 0 ≤ cc) (hdd : 0 ≤ dd) (htg : tt ≤ gg) (hge : gg - tt ≤ eE)
    (hspad0 : 0 ≤ spad) (hspad : spad ≤ εpad) (homega : 0 ≤ omega) (hωmax : omega ≤ ωmax)
    (hδ : 0 ≤ δ) (hδmax : δ ≤ Mcap - 1) (hmt : 0 ≤ (twoLevelSlope - 1) * cellMesh)
    (hνdef : nominal = 1 - (max (cc - dd) 0 + gg - tt) - 6 * firstAmp b - omega)
    (hN4 : x₁ + x₂ + 6 * slotPrice * rem - nominal ≤
      twoLevelOldGap b + 6 * firstAmp b + omega + spad - (min cc dd + ((eE - gg) + tt)))
    (hN4u : x₁ + x₂ + rem ≤ A - cc - eE + spad) (hA : A ≤ twoLevelTotalA b)
    (hrem : rem ≤ b)
    (hwd : secondStepWidthFloor ≤ nominal + δ) (hfirst : firstAmp firstCellTop ≤ firstAmp b)
    (hdl : fixedDeletion b ≤ dl) (hz' : z' = rem - dl) (hz'0 : 0 ≤ z')
    (hnotO : ¬ (x₁ + x₂ + 6 * slotPrice * z' ≤ nominal + δ))
    (hnotR : ¬ (x₁ + x₂ + 6 * slotPrice * z' ≤ nominal + δ + δR ∧
      (max 0 (nominal + δ - x₂ + ξR) + x₁ + 6 * slotPrice * z' + δR ≤ nominal + δ ∨
        max 0 (nominal + δ - x₁ + ξR) + x₂ + 6 * slotPrice * z' + δR ≤ nominal + δ))) :
    SecondStepArithmetic G lossFloor (nominal + δ) x₁ x₂ z' (nominal + δ)
      (x₁ + x₂ + (rem - fixedDeletion b) + secondSlope / G)
      (secondAmp b + amplifierRatio slotPrice 1 secondJunction * ((omega + spad) + omega) +
        amplifierRatio slotPrice 1 secondJunction * (1 + 6 * slotPrice) / G) lossFloor := by
  have hκ := slotPrice_bounds
  have hq := firstJunction_mem
  have hchild : ∀ b', firstCellTop ≤ b' → b' ≤ slotTop → childOvershoot b' + ωmax + εpad ≤ δR :=
    hcert.reflect
  have hmargin := hcert.reflect_margin
  have hcO := hchild b hb.1 hb.2
  -- the nominal width is at most one
  have hv0 : 0 ≤ max (cc - dd) 0 + gg - tt := by linarith [le_max_right (cc - dd) 0]
  have hsmallω : (omega + spad) + omega + (twoLevelSlope - 1) * cellMesh ≤ 1 / 1000000 := by
    have h1 := hcert.small
    have h2 := hcert.mesh
    linarith
  have hWu : nominal + δ ≤ 1 := by
    have h6 := hcert.width
    linarith
  have hRed0 : 0 ≤ min cc dd + ((eE - gg) + tt) := by
    have : 0 ≤ min cc dd := le_min hcc hdd
    linarith
  -- the overshoot of the zero-extraction child and the padding is at most seven thousandths of the least width
  have hcO7 : childOvershoot b + (omega + spad) ≤ 7 / 2500 := by
    have := hcert.reflect_small
    linarith [hcO, hωmax, hspad]
  -- the capacity of the state after the deletion of the slots exceeds the width by at most the margin
  have hcapR : x₁ + x₂ + 6 * slotPrice * z' ≤ nominal + δ + δR := by
    have h6 : 6 * slotPrice * z' ≤ 6 * slotPrice * (rem - fixedDeletion b) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith [hκ.1])
    have hcOdef := childOvershoot_eq b
    linarith [hN4, h6, hcOdef, hcO, hRed0, hωmax, hspad, hδ]
  have hδR2 : 2 * δR ≤ nominal + δ := by
    have : (2:ℝ) / 5 ≤ nominal + δ := hwd
    have hδR1 : δR + ξR ≤ 1 / 100 * (2 / 5) := hmargin
    linarith
  have hbal : |x₁ - x₂| ≤ 6 * slotPrice * z' + (ξR + δR) := by
    have hn := not_and.mp hnotR hcapR
    push Not at hn
    exact balance_of_not_reflection hz'0 (by linarith [hκ.1]) hξR hδR2 hcapR (not_le.mpr hn.1)
      (not_le.mpr hn.2)
  have hv : 0 ≤ max (cc - dd) 0 + gg - tt := hv0
  refine second_step_arithmetic_of_child (b := b) (ν := nominal) (δ := δ) (x₁ := x₁) (x₂ := x₂) (z' := z')
    (rem := rem) (pad := omega + spad) (omega := omega) (ξ := ξR) (δR := δR) (v := max (cc - dd) 0 + gg - tt)
    (Red := min cc dd + ((eE - gg) + tt)) (lossFloor := lossFloor)
    (lengthL := x₁ + x₂ + (rem - fixedDeletion b) + secondSlope / G)
    (ampL := secondAmp b + amplifierRatio slotPrice 1 secondJunction * ((omega + spad) + omega) +
        amplifierRatio slotPrice 1 secondJunction * (1 + 6 * slotPrice) / G)
    G hcert.grid hb hwd hWu hδ (by linarith) homega hmt hz'0 hrem (by linarith) hv hRed0 hνdef ?_ ?_
    (not_le.mp hnotO) hbal (by linarith) hsmallω (by linarith) le_rfl hcO7
  · linarith
  · have hc : cc + eE = (max (cc - dd) 0 + gg - tt) + (min cc dd + ((eE - gg) + tt)) := by
      rcases le_total cc dd with h | h
      · rw [max_eq_right (by linarith), min_eq_left h]; ring
      · rw [max_eq_left (by linarith), min_eq_right h]; ring
    linarith

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
