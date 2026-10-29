/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09665_09696
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97591784172724,97591424401530,97591064609810,97590704797564,97590344964793,97589985111497,97589625237677,97589265343333,97588905428466,97588545493077,97588185537166,97587825560733,97587465563780,97587105546307,97586745508314,97586385449802,97586025370772,97585665271224,97585305151158,97584945010576,97584584849478,97584224667864,97583864465735,97583504243092,97583143999935,97582783736265,97582423452082,97582063147387,97581702822180,97581342476462,97580982110234,97580621723496,97580261316249]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9664+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9665 := params 0
abbrev ray9665 := rays 0
def bank9665 : Fin 2 → Cell := twoBank p9665 ray9665
theorem signs9665 : ∀ j, Signs p9665 (bank9665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9666 := params 1
abbrev ray9666 := rays 1
def bank9666 : Fin 2 → Cell := twoBank p9666 ray9666
theorem signs9666 : ∀ j, Signs p9666 (bank9666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9667 := params 2
abbrev ray9667 := rays 2
def bank9667 : Fin 2 → Cell := twoBank p9667 ray9667
theorem signs9667 : ∀ j, Signs p9667 (bank9667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9668 := params 3
abbrev ray9668 := rays 3
def bank9668 : Fin 2 → Cell := twoBank p9668 ray9668
theorem signs9668 : ∀ j, Signs p9668 (bank9668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9669 := params 4
abbrev ray9669 := rays 4
def bank9669 : Fin 2 → Cell := twoBank p9669 ray9669
theorem signs9669 : ∀ j, Signs p9669 (bank9669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9670 := params 5
abbrev ray9670 := rays 5
def bank9670 : Fin 2 → Cell := twoBank p9670 ray9670
theorem signs9670 : ∀ j, Signs p9670 (bank9670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9671 := params 6
abbrev ray9671 := rays 6
def bank9671 : Fin 2 → Cell := twoBank p9671 ray9671
theorem signs9671 : ∀ j, Signs p9671 (bank9671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9672 := params 7
abbrev ray9672 := rays 7
def bank9672 : Fin 2 → Cell := twoBank p9672 ray9672
theorem signs9672 : ∀ j, Signs p9672 (bank9672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9673 := params 8
abbrev ray9673 := rays 8
def bank9673 : Fin 2 → Cell := twoBank p9673 ray9673
theorem signs9673 : ∀ j, Signs p9673 (bank9673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9674 := params 9
abbrev ray9674 := rays 9
def bank9674 : Fin 2 → Cell := twoBank p9674 ray9674
theorem signs9674 : ∀ j, Signs p9674 (bank9674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9675 := params 10
abbrev ray9675 := rays 10
def bank9675 : Fin 2 → Cell := twoBank p9675 ray9675
theorem signs9675 : ∀ j, Signs p9675 (bank9675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9676 := params 11
abbrev ray9676 := rays 11
def bank9676 : Fin 2 → Cell := twoBank p9676 ray9676
theorem signs9676 : ∀ j, Signs p9676 (bank9676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9677 := params 12
abbrev ray9677 := rays 12
def bank9677 : Fin 2 → Cell := twoBank p9677 ray9677
theorem signs9677 : ∀ j, Signs p9677 (bank9677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9678 := params 13
abbrev ray9678 := rays 13
def bank9678 : Fin 2 → Cell := twoBank p9678 ray9678
theorem signs9678 : ∀ j, Signs p9678 (bank9678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9679 := params 14
abbrev ray9679 := rays 14
def bank9679 : Fin 2 → Cell := twoBank p9679 ray9679
theorem signs9679 : ∀ j, Signs p9679 (bank9679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9680 := params 15
abbrev ray9680 := rays 15
def bank9680 : Fin 2 → Cell := twoBank p9680 ray9680
theorem signs9680 : ∀ j, Signs p9680 (bank9680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9681 := params 16
abbrev ray9681 := rays 16
def bank9681 : Fin 2 → Cell := twoBank p9681 ray9681
theorem signs9681 : ∀ j, Signs p9681 (bank9681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9682 := params 17
abbrev ray9682 := rays 17
def bank9682 : Fin 2 → Cell := twoBank p9682 ray9682
theorem signs9682 : ∀ j, Signs p9682 (bank9682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9683 := params 18
abbrev ray9683 := rays 18
def bank9683 : Fin 2 → Cell := twoBank p9683 ray9683
theorem signs9683 : ∀ j, Signs p9683 (bank9683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9684 := params 19
abbrev ray9684 := rays 19
def bank9684 : Fin 2 → Cell := twoBank p9684 ray9684
theorem signs9684 : ∀ j, Signs p9684 (bank9684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9685 := params 20
abbrev ray9685 := rays 20
def bank9685 : Fin 2 → Cell := twoBank p9685 ray9685
theorem signs9685 : ∀ j, Signs p9685 (bank9685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9686 := params 21
abbrev ray9686 := rays 21
def bank9686 : Fin 2 → Cell := twoBank p9686 ray9686
theorem signs9686 : ∀ j, Signs p9686 (bank9686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9687 := params 22
abbrev ray9687 := rays 22
def bank9687 : Fin 2 → Cell := twoBank p9687 ray9687
theorem signs9687 : ∀ j, Signs p9687 (bank9687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9688 := params 23
abbrev ray9688 := rays 23
def bank9688 : Fin 2 → Cell := twoBank p9688 ray9688
theorem signs9688 : ∀ j, Signs p9688 (bank9688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9689 := params 24
abbrev ray9689 := rays 24
def bank9689 : Fin 2 → Cell := twoBank p9689 ray9689
theorem signs9689 : ∀ j, Signs p9689 (bank9689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9690 := params 25
abbrev ray9690 := rays 25
def bank9690 : Fin 2 → Cell := twoBank p9690 ray9690
theorem signs9690 : ∀ j, Signs p9690 (bank9690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9691 := params 26
abbrev ray9691 := rays 26
def bank9691 : Fin 2 → Cell := twoBank p9691 ray9691
theorem signs9691 : ∀ j, Signs p9691 (bank9691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9692 := params 27
abbrev ray9692 := rays 27
def bank9692 : Fin 2 → Cell := twoBank p9692 ray9692
theorem signs9692 : ∀ j, Signs p9692 (bank9692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9693 := params 28
abbrev ray9693 := rays 28
def bank9693 : Fin 2 → Cell := twoBank p9693 ray9693
theorem signs9693 : ∀ j, Signs p9693 (bank9693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9694 := params 29
abbrev ray9694 := rays 29
def bank9694 : Fin 2 → Cell := twoBank p9694 ray9694
theorem signs9694 : ∀ j, Signs p9694 (bank9694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9695 := params 30
abbrev ray9695 := rays 30
def bank9695 : Fin 2 → Cell := twoBank p9695 ray9695
theorem signs9695 : ∀ j, Signs p9695 (bank9695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9696 := params 31
abbrev ray9696 := rays 31
def bank9696 : Fin 2 → Cell := twoBank p9696 ray9696
theorem signs9696 : ∀ j, Signs p9696 (bank9696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09665_09696
