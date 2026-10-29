/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07617_07648
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98284649089375,98284332668430,98284016225625,98283699760960,98283383274436,98283066766054,98282750235815,98282433683719,98282117109767,98281800513960,98281483896298,98281167256783,98280850595415,98280533912194,98280217207122,98279900480199,98279583731426,98279266960803,98278950168332,98278633354013,98278316517847,98277999659834,98277682779975,98277365878271,98277048954723,98276732009332,98276415042098,98276098053022,98275781042104,98275464009346,98275146954748,98274829878311,98274512780035]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7616+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7617 := params 0
abbrev ray7617 := rays 0
def bank7617 : Fin 2 → Cell := twoBank p7617 ray7617
theorem signs7617 : ∀ j, Signs p7617 (bank7617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7618 := params 1
abbrev ray7618 := rays 1
def bank7618 : Fin 2 → Cell := twoBank p7618 ray7618
theorem signs7618 : ∀ j, Signs p7618 (bank7618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7619 := params 2
abbrev ray7619 := rays 2
def bank7619 : Fin 2 → Cell := twoBank p7619 ray7619
theorem signs7619 : ∀ j, Signs p7619 (bank7619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7620 := params 3
abbrev ray7620 := rays 3
def bank7620 : Fin 2 → Cell := twoBank p7620 ray7620
theorem signs7620 : ∀ j, Signs p7620 (bank7620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7621 := params 4
abbrev ray7621 := rays 4
def bank7621 : Fin 2 → Cell := twoBank p7621 ray7621
theorem signs7621 : ∀ j, Signs p7621 (bank7621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7622 := params 5
abbrev ray7622 := rays 5
def bank7622 : Fin 2 → Cell := twoBank p7622 ray7622
theorem signs7622 : ∀ j, Signs p7622 (bank7622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7623 := params 6
abbrev ray7623 := rays 6
def bank7623 : Fin 2 → Cell := twoBank p7623 ray7623
theorem signs7623 : ∀ j, Signs p7623 (bank7623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7624 := params 7
abbrev ray7624 := rays 7
def bank7624 : Fin 2 → Cell := twoBank p7624 ray7624
theorem signs7624 : ∀ j, Signs p7624 (bank7624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7625 := params 8
abbrev ray7625 := rays 8
def bank7625 : Fin 2 → Cell := twoBank p7625 ray7625
theorem signs7625 : ∀ j, Signs p7625 (bank7625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7626 := params 9
abbrev ray7626 := rays 9
def bank7626 : Fin 2 → Cell := twoBank p7626 ray7626
theorem signs7626 : ∀ j, Signs p7626 (bank7626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7627 := params 10
abbrev ray7627 := rays 10
def bank7627 : Fin 2 → Cell := twoBank p7627 ray7627
theorem signs7627 : ∀ j, Signs p7627 (bank7627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7628 := params 11
abbrev ray7628 := rays 11
def bank7628 : Fin 2 → Cell := twoBank p7628 ray7628
theorem signs7628 : ∀ j, Signs p7628 (bank7628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7629 := params 12
abbrev ray7629 := rays 12
def bank7629 : Fin 2 → Cell := twoBank p7629 ray7629
theorem signs7629 : ∀ j, Signs p7629 (bank7629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7630 := params 13
abbrev ray7630 := rays 13
def bank7630 : Fin 2 → Cell := twoBank p7630 ray7630
theorem signs7630 : ∀ j, Signs p7630 (bank7630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7631 := params 14
abbrev ray7631 := rays 14
def bank7631 : Fin 2 → Cell := twoBank p7631 ray7631
theorem signs7631 : ∀ j, Signs p7631 (bank7631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7632 := params 15
abbrev ray7632 := rays 15
def bank7632 : Fin 2 → Cell := twoBank p7632 ray7632
theorem signs7632 : ∀ j, Signs p7632 (bank7632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7633 := params 16
abbrev ray7633 := rays 16
def bank7633 : Fin 2 → Cell := twoBank p7633 ray7633
theorem signs7633 : ∀ j, Signs p7633 (bank7633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7634 := params 17
abbrev ray7634 := rays 17
def bank7634 : Fin 2 → Cell := twoBank p7634 ray7634
theorem signs7634 : ∀ j, Signs p7634 (bank7634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7635 := params 18
abbrev ray7635 := rays 18
def bank7635 : Fin 2 → Cell := twoBank p7635 ray7635
theorem signs7635 : ∀ j, Signs p7635 (bank7635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7636 := params 19
abbrev ray7636 := rays 19
def bank7636 : Fin 2 → Cell := twoBank p7636 ray7636
theorem signs7636 : ∀ j, Signs p7636 (bank7636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7637 := params 20
abbrev ray7637 := rays 20
def bank7637 : Fin 2 → Cell := twoBank p7637 ray7637
theorem signs7637 : ∀ j, Signs p7637 (bank7637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7638 := params 21
abbrev ray7638 := rays 21
def bank7638 : Fin 2 → Cell := twoBank p7638 ray7638
theorem signs7638 : ∀ j, Signs p7638 (bank7638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7639 := params 22
abbrev ray7639 := rays 22
def bank7639 : Fin 2 → Cell := twoBank p7639 ray7639
theorem signs7639 : ∀ j, Signs p7639 (bank7639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7640 := params 23
abbrev ray7640 := rays 23
def bank7640 : Fin 2 → Cell := twoBank p7640 ray7640
theorem signs7640 : ∀ j, Signs p7640 (bank7640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7641 := params 24
abbrev ray7641 := rays 24
def bank7641 : Fin 2 → Cell := twoBank p7641 ray7641
theorem signs7641 : ∀ j, Signs p7641 (bank7641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7642 := params 25
abbrev ray7642 := rays 25
def bank7642 : Fin 2 → Cell := twoBank p7642 ray7642
theorem signs7642 : ∀ j, Signs p7642 (bank7642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7643 := params 26
abbrev ray7643 := rays 26
def bank7643 : Fin 2 → Cell := twoBank p7643 ray7643
theorem signs7643 : ∀ j, Signs p7643 (bank7643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7644 := params 27
abbrev ray7644 := rays 27
def bank7644 : Fin 2 → Cell := twoBank p7644 ray7644
theorem signs7644 : ∀ j, Signs p7644 (bank7644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7645 := params 28
abbrev ray7645 := rays 28
def bank7645 : Fin 2 → Cell := twoBank p7645 ray7645
theorem signs7645 : ∀ j, Signs p7645 (bank7645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7646 := params 29
abbrev ray7646 := rays 29
def bank7646 : Fin 2 → Cell := twoBank p7646 ray7646
theorem signs7646 : ∀ j, Signs p7646 (bank7646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7647 := params 30
abbrev ray7647 := rays 30
def bank7647 : Fin 2 → Cell := twoBank p7647 ray7647
theorem signs7647 : ∀ j, Signs p7647 (bank7647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7648 := params 31
abbrev ray7648 := rays 31
def bank7648 : Fin 2 → Cell := twoBank p7648 ray7648
theorem signs7648 : ∀ j, Signs p7648 (bank7648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07617_07648
