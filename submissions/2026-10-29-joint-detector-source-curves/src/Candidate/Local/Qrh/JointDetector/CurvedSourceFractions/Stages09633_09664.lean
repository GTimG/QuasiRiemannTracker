/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09633_09664
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97603286009493,97602926895451,97602567760864,97602208605733,97601849430058,97601490233840,97601131017079,97600771779776,97600412521932,97600053243547,97599693944621,97599334625156,97598975285151,97598615924608,97598256543527,97597897141908,97597537719753,97597178277061,97596818813834,97596459330071,97596099825774,97595740300943,97595380755579,97595021189682,97594661603252,97594301996291,97593942368799,97593582720776,97593223052223,97592863363141,97592503653530,97592143923391,97591784172724]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9632+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9633 := params 0
abbrev ray9633 := rays 0
def bank9633 : Fin 2 → Cell := twoBank p9633 ray9633
theorem signs9633 : ∀ j, Signs p9633 (bank9633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9634 := params 1
abbrev ray9634 := rays 1
def bank9634 : Fin 2 → Cell := twoBank p9634 ray9634
theorem signs9634 : ∀ j, Signs p9634 (bank9634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9635 := params 2
abbrev ray9635 := rays 2
def bank9635 : Fin 2 → Cell := twoBank p9635 ray9635
theorem signs9635 : ∀ j, Signs p9635 (bank9635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9636 := params 3
abbrev ray9636 := rays 3
def bank9636 : Fin 2 → Cell := twoBank p9636 ray9636
theorem signs9636 : ∀ j, Signs p9636 (bank9636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9637 := params 4
abbrev ray9637 := rays 4
def bank9637 : Fin 2 → Cell := twoBank p9637 ray9637
theorem signs9637 : ∀ j, Signs p9637 (bank9637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9638 := params 5
abbrev ray9638 := rays 5
def bank9638 : Fin 2 → Cell := twoBank p9638 ray9638
theorem signs9638 : ∀ j, Signs p9638 (bank9638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9639 := params 6
abbrev ray9639 := rays 6
def bank9639 : Fin 2 → Cell := twoBank p9639 ray9639
theorem signs9639 : ∀ j, Signs p9639 (bank9639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9640 := params 7
abbrev ray9640 := rays 7
def bank9640 : Fin 2 → Cell := twoBank p9640 ray9640
theorem signs9640 : ∀ j, Signs p9640 (bank9640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9641 := params 8
abbrev ray9641 := rays 8
def bank9641 : Fin 2 → Cell := twoBank p9641 ray9641
theorem signs9641 : ∀ j, Signs p9641 (bank9641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9642 := params 9
abbrev ray9642 := rays 9
def bank9642 : Fin 2 → Cell := twoBank p9642 ray9642
theorem signs9642 : ∀ j, Signs p9642 (bank9642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9643 := params 10
abbrev ray9643 := rays 10
def bank9643 : Fin 2 → Cell := twoBank p9643 ray9643
theorem signs9643 : ∀ j, Signs p9643 (bank9643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9644 := params 11
abbrev ray9644 := rays 11
def bank9644 : Fin 2 → Cell := twoBank p9644 ray9644
theorem signs9644 : ∀ j, Signs p9644 (bank9644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9645 := params 12
abbrev ray9645 := rays 12
def bank9645 : Fin 2 → Cell := twoBank p9645 ray9645
theorem signs9645 : ∀ j, Signs p9645 (bank9645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9646 := params 13
abbrev ray9646 := rays 13
def bank9646 : Fin 2 → Cell := twoBank p9646 ray9646
theorem signs9646 : ∀ j, Signs p9646 (bank9646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9647 := params 14
abbrev ray9647 := rays 14
def bank9647 : Fin 2 → Cell := twoBank p9647 ray9647
theorem signs9647 : ∀ j, Signs p9647 (bank9647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9648 := params 15
abbrev ray9648 := rays 15
def bank9648 : Fin 2 → Cell := twoBank p9648 ray9648
theorem signs9648 : ∀ j, Signs p9648 (bank9648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9649 := params 16
abbrev ray9649 := rays 16
def bank9649 : Fin 2 → Cell := twoBank p9649 ray9649
theorem signs9649 : ∀ j, Signs p9649 (bank9649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9650 := params 17
abbrev ray9650 := rays 17
def bank9650 : Fin 2 → Cell := twoBank p9650 ray9650
theorem signs9650 : ∀ j, Signs p9650 (bank9650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9651 := params 18
abbrev ray9651 := rays 18
def bank9651 : Fin 2 → Cell := twoBank p9651 ray9651
theorem signs9651 : ∀ j, Signs p9651 (bank9651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9652 := params 19
abbrev ray9652 := rays 19
def bank9652 : Fin 2 → Cell := twoBank p9652 ray9652
theorem signs9652 : ∀ j, Signs p9652 (bank9652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9653 := params 20
abbrev ray9653 := rays 20
def bank9653 : Fin 2 → Cell := twoBank p9653 ray9653
theorem signs9653 : ∀ j, Signs p9653 (bank9653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9654 := params 21
abbrev ray9654 := rays 21
def bank9654 : Fin 2 → Cell := twoBank p9654 ray9654
theorem signs9654 : ∀ j, Signs p9654 (bank9654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9655 := params 22
abbrev ray9655 := rays 22
def bank9655 : Fin 2 → Cell := twoBank p9655 ray9655
theorem signs9655 : ∀ j, Signs p9655 (bank9655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9656 := params 23
abbrev ray9656 := rays 23
def bank9656 : Fin 2 → Cell := twoBank p9656 ray9656
theorem signs9656 : ∀ j, Signs p9656 (bank9656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9657 := params 24
abbrev ray9657 := rays 24
def bank9657 : Fin 2 → Cell := twoBank p9657 ray9657
theorem signs9657 : ∀ j, Signs p9657 (bank9657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9658 := params 25
abbrev ray9658 := rays 25
def bank9658 : Fin 2 → Cell := twoBank p9658 ray9658
theorem signs9658 : ∀ j, Signs p9658 (bank9658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9659 := params 26
abbrev ray9659 := rays 26
def bank9659 : Fin 2 → Cell := twoBank p9659 ray9659
theorem signs9659 : ∀ j, Signs p9659 (bank9659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9660 := params 27
abbrev ray9660 := rays 27
def bank9660 : Fin 2 → Cell := twoBank p9660 ray9660
theorem signs9660 : ∀ j, Signs p9660 (bank9660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9661 := params 28
abbrev ray9661 := rays 28
def bank9661 : Fin 2 → Cell := twoBank p9661 ray9661
theorem signs9661 : ∀ j, Signs p9661 (bank9661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9662 := params 29
abbrev ray9662 := rays 29
def bank9662 : Fin 2 → Cell := twoBank p9662 ray9662
theorem signs9662 : ∀ j, Signs p9662 (bank9662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9663 := params 30
abbrev ray9663 := rays 30
def bank9663 : Fin 2 → Cell := twoBank p9663 ray9663
theorem signs9663 : ∀ j, Signs p9663 (bank9663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9664 := params 31
abbrev ray9664 := rays 31
def bank9664 : Fin 2 → Cell := twoBank p9664 ray9664
theorem signs9664 : ∀ j, Signs p9664 (bank9664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09633_09664
