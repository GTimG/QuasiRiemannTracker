/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10625_10656
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97237037390135,97236658168849,97236278927559,97235899666266,97235520384970,97235141083671,97234761762370,97234382421068,97234003059765,97233623678461,97233244277157,97232864855854,97232485414552,97232105953252,97231726471954,97231346970658,97230967449365,97230587908076,97230208346791,97229828765511,97229449164236,97229069542967,97228689901704,97228310240448,97227930559199,97227550857958,97227171136725,97226791395501,97226411634286,97226031853081,97225652051886,97225272230702,97224892389529]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10624+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10625 := params 0
abbrev ray10625 := rays 0
def bank10625 : Fin 2 → Cell := twoBank p10625 ray10625
theorem signs10625 : ∀ j, Signs p10625 (bank10625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10626 := params 1
abbrev ray10626 := rays 1
def bank10626 : Fin 2 → Cell := twoBank p10626 ray10626
theorem signs10626 : ∀ j, Signs p10626 (bank10626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10627 := params 2
abbrev ray10627 := rays 2
def bank10627 : Fin 2 → Cell := twoBank p10627 ray10627
theorem signs10627 : ∀ j, Signs p10627 (bank10627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10628 := params 3
abbrev ray10628 := rays 3
def bank10628 : Fin 2 → Cell := twoBank p10628 ray10628
theorem signs10628 : ∀ j, Signs p10628 (bank10628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10629 := params 4
abbrev ray10629 := rays 4
def bank10629 : Fin 2 → Cell := twoBank p10629 ray10629
theorem signs10629 : ∀ j, Signs p10629 (bank10629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10630 := params 5
abbrev ray10630 := rays 5
def bank10630 : Fin 2 → Cell := twoBank p10630 ray10630
theorem signs10630 : ∀ j, Signs p10630 (bank10630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10631 := params 6
abbrev ray10631 := rays 6
def bank10631 : Fin 2 → Cell := twoBank p10631 ray10631
theorem signs10631 : ∀ j, Signs p10631 (bank10631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10632 := params 7
abbrev ray10632 := rays 7
def bank10632 : Fin 2 → Cell := twoBank p10632 ray10632
theorem signs10632 : ∀ j, Signs p10632 (bank10632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10633 := params 8
abbrev ray10633 := rays 8
def bank10633 : Fin 2 → Cell := twoBank p10633 ray10633
theorem signs10633 : ∀ j, Signs p10633 (bank10633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10634 := params 9
abbrev ray10634 := rays 9
def bank10634 : Fin 2 → Cell := twoBank p10634 ray10634
theorem signs10634 : ∀ j, Signs p10634 (bank10634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10635 := params 10
abbrev ray10635 := rays 10
def bank10635 : Fin 2 → Cell := twoBank p10635 ray10635
theorem signs10635 : ∀ j, Signs p10635 (bank10635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10636 := params 11
abbrev ray10636 := rays 11
def bank10636 : Fin 2 → Cell := twoBank p10636 ray10636
theorem signs10636 : ∀ j, Signs p10636 (bank10636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10637 := params 12
abbrev ray10637 := rays 12
def bank10637 : Fin 2 → Cell := twoBank p10637 ray10637
theorem signs10637 : ∀ j, Signs p10637 (bank10637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10638 := params 13
abbrev ray10638 := rays 13
def bank10638 : Fin 2 → Cell := twoBank p10638 ray10638
theorem signs10638 : ∀ j, Signs p10638 (bank10638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10639 := params 14
abbrev ray10639 := rays 14
def bank10639 : Fin 2 → Cell := twoBank p10639 ray10639
theorem signs10639 : ∀ j, Signs p10639 (bank10639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10640 := params 15
abbrev ray10640 := rays 15
def bank10640 : Fin 2 → Cell := twoBank p10640 ray10640
theorem signs10640 : ∀ j, Signs p10640 (bank10640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10641 := params 16
abbrev ray10641 := rays 16
def bank10641 : Fin 2 → Cell := twoBank p10641 ray10641
theorem signs10641 : ∀ j, Signs p10641 (bank10641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10642 := params 17
abbrev ray10642 := rays 17
def bank10642 : Fin 2 → Cell := twoBank p10642 ray10642
theorem signs10642 : ∀ j, Signs p10642 (bank10642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10643 := params 18
abbrev ray10643 := rays 18
def bank10643 : Fin 2 → Cell := twoBank p10643 ray10643
theorem signs10643 : ∀ j, Signs p10643 (bank10643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10644 := params 19
abbrev ray10644 := rays 19
def bank10644 : Fin 2 → Cell := twoBank p10644 ray10644
theorem signs10644 : ∀ j, Signs p10644 (bank10644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10645 := params 20
abbrev ray10645 := rays 20
def bank10645 : Fin 2 → Cell := twoBank p10645 ray10645
theorem signs10645 : ∀ j, Signs p10645 (bank10645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10646 := params 21
abbrev ray10646 := rays 21
def bank10646 : Fin 2 → Cell := twoBank p10646 ray10646
theorem signs10646 : ∀ j, Signs p10646 (bank10646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10647 := params 22
abbrev ray10647 := rays 22
def bank10647 : Fin 2 → Cell := twoBank p10647 ray10647
theorem signs10647 : ∀ j, Signs p10647 (bank10647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10648 := params 23
abbrev ray10648 := rays 23
def bank10648 : Fin 2 → Cell := twoBank p10648 ray10648
theorem signs10648 : ∀ j, Signs p10648 (bank10648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10649 := params 24
abbrev ray10649 := rays 24
def bank10649 : Fin 2 → Cell := twoBank p10649 ray10649
theorem signs10649 : ∀ j, Signs p10649 (bank10649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10650 := params 25
abbrev ray10650 := rays 25
def bank10650 : Fin 2 → Cell := twoBank p10650 ray10650
theorem signs10650 : ∀ j, Signs p10650 (bank10650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10651 := params 26
abbrev ray10651 := rays 26
def bank10651 : Fin 2 → Cell := twoBank p10651 ray10651
theorem signs10651 : ∀ j, Signs p10651 (bank10651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10652 := params 27
abbrev ray10652 := rays 27
def bank10652 : Fin 2 → Cell := twoBank p10652 ray10652
theorem signs10652 : ∀ j, Signs p10652 (bank10652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10653 := params 28
abbrev ray10653 := rays 28
def bank10653 : Fin 2 → Cell := twoBank p10653 ray10653
theorem signs10653 : ∀ j, Signs p10653 (bank10653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10654 := params 29
abbrev ray10654 := rays 29
def bank10654 : Fin 2 → Cell := twoBank p10654 ray10654
theorem signs10654 : ∀ j, Signs p10654 (bank10654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10655 := params 30
abbrev ray10655 := rays 30
def bank10655 : Fin 2 → Cell := twoBank p10655 ray10655
theorem signs10655 : ∀ j, Signs p10655 (bank10655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10656 := params 31
abbrev ray10656 := rays 31
def bank10656 : Fin 2 → Cell := twoBank p10656 ray10656
theorem signs10656 : ∀ j, Signs p10656 (bank10656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10625_10656
