/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12609_12640
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96445939566617,96445521588520,96445103591320,96444685575018,96444267539614,96443849485108,96443431411500,96443013318791,96442595206982,96442177076073,96441758926064,96441340756955,96440922568747,96440504361441,96440086135037,96439667889535,96439249624935,96438831341238,96438413038445,96437994716555,96437576375570,96437158015489,96436739636313,96436321238043,96435902820678,96435484384219,96435065928667,96434647454022,96434228960284,96433810447454,96433391915532,96432973364519,96432554794415]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12608+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12609 := params 0
abbrev ray12609 := rays 0
def bank12609 : Fin 2 → Cell := twoBank p12609 ray12609
theorem signs12609 : ∀ j, Signs p12609 (bank12609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12610 := params 1
abbrev ray12610 := rays 1
def bank12610 : Fin 2 → Cell := twoBank p12610 ray12610
theorem signs12610 : ∀ j, Signs p12610 (bank12610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12611 := params 2
abbrev ray12611 := rays 2
def bank12611 : Fin 2 → Cell := twoBank p12611 ray12611
theorem signs12611 : ∀ j, Signs p12611 (bank12611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12612 := params 3
abbrev ray12612 := rays 3
def bank12612 : Fin 2 → Cell := twoBank p12612 ray12612
theorem signs12612 : ∀ j, Signs p12612 (bank12612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12613 := params 4
abbrev ray12613 := rays 4
def bank12613 : Fin 2 → Cell := twoBank p12613 ray12613
theorem signs12613 : ∀ j, Signs p12613 (bank12613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12614 := params 5
abbrev ray12614 := rays 5
def bank12614 : Fin 2 → Cell := twoBank p12614 ray12614
theorem signs12614 : ∀ j, Signs p12614 (bank12614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12615 := params 6
abbrev ray12615 := rays 6
def bank12615 : Fin 2 → Cell := twoBank p12615 ray12615
theorem signs12615 : ∀ j, Signs p12615 (bank12615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12616 := params 7
abbrev ray12616 := rays 7
def bank12616 : Fin 2 → Cell := twoBank p12616 ray12616
theorem signs12616 : ∀ j, Signs p12616 (bank12616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12617 := params 8
abbrev ray12617 := rays 8
def bank12617 : Fin 2 → Cell := twoBank p12617 ray12617
theorem signs12617 : ∀ j, Signs p12617 (bank12617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12618 := params 9
abbrev ray12618 := rays 9
def bank12618 : Fin 2 → Cell := twoBank p12618 ray12618
theorem signs12618 : ∀ j, Signs p12618 (bank12618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12619 := params 10
abbrev ray12619 := rays 10
def bank12619 : Fin 2 → Cell := twoBank p12619 ray12619
theorem signs12619 : ∀ j, Signs p12619 (bank12619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12620 := params 11
abbrev ray12620 := rays 11
def bank12620 : Fin 2 → Cell := twoBank p12620 ray12620
theorem signs12620 : ∀ j, Signs p12620 (bank12620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12621 := params 12
abbrev ray12621 := rays 12
def bank12621 : Fin 2 → Cell := twoBank p12621 ray12621
theorem signs12621 : ∀ j, Signs p12621 (bank12621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12622 := params 13
abbrev ray12622 := rays 13
def bank12622 : Fin 2 → Cell := twoBank p12622 ray12622
theorem signs12622 : ∀ j, Signs p12622 (bank12622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12623 := params 14
abbrev ray12623 := rays 14
def bank12623 : Fin 2 → Cell := twoBank p12623 ray12623
theorem signs12623 : ∀ j, Signs p12623 (bank12623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12624 := params 15
abbrev ray12624 := rays 15
def bank12624 : Fin 2 → Cell := twoBank p12624 ray12624
theorem signs12624 : ∀ j, Signs p12624 (bank12624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12625 := params 16
abbrev ray12625 := rays 16
def bank12625 : Fin 2 → Cell := twoBank p12625 ray12625
theorem signs12625 : ∀ j, Signs p12625 (bank12625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12626 := params 17
abbrev ray12626 := rays 17
def bank12626 : Fin 2 → Cell := twoBank p12626 ray12626
theorem signs12626 : ∀ j, Signs p12626 (bank12626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12627 := params 18
abbrev ray12627 := rays 18
def bank12627 : Fin 2 → Cell := twoBank p12627 ray12627
theorem signs12627 : ∀ j, Signs p12627 (bank12627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12628 := params 19
abbrev ray12628 := rays 19
def bank12628 : Fin 2 → Cell := twoBank p12628 ray12628
theorem signs12628 : ∀ j, Signs p12628 (bank12628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12629 := params 20
abbrev ray12629 := rays 20
def bank12629 : Fin 2 → Cell := twoBank p12629 ray12629
theorem signs12629 : ∀ j, Signs p12629 (bank12629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12630 := params 21
abbrev ray12630 := rays 21
def bank12630 : Fin 2 → Cell := twoBank p12630 ray12630
theorem signs12630 : ∀ j, Signs p12630 (bank12630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12631 := params 22
abbrev ray12631 := rays 22
def bank12631 : Fin 2 → Cell := twoBank p12631 ray12631
theorem signs12631 : ∀ j, Signs p12631 (bank12631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12632 := params 23
abbrev ray12632 := rays 23
def bank12632 : Fin 2 → Cell := twoBank p12632 ray12632
theorem signs12632 : ∀ j, Signs p12632 (bank12632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12633 := params 24
abbrev ray12633 := rays 24
def bank12633 : Fin 2 → Cell := twoBank p12633 ray12633
theorem signs12633 : ∀ j, Signs p12633 (bank12633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12634 := params 25
abbrev ray12634 := rays 25
def bank12634 : Fin 2 → Cell := twoBank p12634 ray12634
theorem signs12634 : ∀ j, Signs p12634 (bank12634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12635 := params 26
abbrev ray12635 := rays 26
def bank12635 : Fin 2 → Cell := twoBank p12635 ray12635
theorem signs12635 : ∀ j, Signs p12635 (bank12635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12636 := params 27
abbrev ray12636 := rays 27
def bank12636 : Fin 2 → Cell := twoBank p12636 ray12636
theorem signs12636 : ∀ j, Signs p12636 (bank12636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12637 := params 28
abbrev ray12637 := rays 28
def bank12637 : Fin 2 → Cell := twoBank p12637 ray12637
theorem signs12637 : ∀ j, Signs p12637 (bank12637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12638 := params 29
abbrev ray12638 := rays 29
def bank12638 : Fin 2 → Cell := twoBank p12638 ray12638
theorem signs12638 : ∀ j, Signs p12638 (bank12638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12639 := params 30
abbrev ray12639 := rays 30
def bank12639 : Fin 2 → Cell := twoBank p12639 ray12639
theorem signs12639 : ∀ j, Signs p12639 (bank12639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12640 := params 31
abbrev ray12640 := rays 31
def bank12640 : Fin 2 → Cell := twoBank p12640 ray12640
theorem signs12640 : ∀ j, Signs p12640 (bank12640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12609_12640
