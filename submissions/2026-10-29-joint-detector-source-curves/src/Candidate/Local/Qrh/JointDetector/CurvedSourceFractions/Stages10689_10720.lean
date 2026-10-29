/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10689_10720
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97212726921026,97212346420513,97211965900029,97211585359574,97211204799148,97210824218753,97210443618388,97210062998055,97209682357753,97209301697483,97208921017246,97208540317042,97208159596872,97207778856736,97207398096635,97207017316570,97206636516540,97206255696547,97205874856590,97205493996671,97205113116790,97204732216947,97204351297143,97203970357378,97203589397653,97203208417968,97202827418324,97202446398722,97202065359161,97201684299643,97201303220168,97200922120736,97200541001348]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10688+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10689 := params 0
abbrev ray10689 := rays 0
def bank10689 : Fin 2 → Cell := twoBank p10689 ray10689
theorem signs10689 : ∀ j, Signs p10689 (bank10689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10690 := params 1
abbrev ray10690 := rays 1
def bank10690 : Fin 2 → Cell := twoBank p10690 ray10690
theorem signs10690 : ∀ j, Signs p10690 (bank10690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10691 := params 2
abbrev ray10691 := rays 2
def bank10691 : Fin 2 → Cell := twoBank p10691 ray10691
theorem signs10691 : ∀ j, Signs p10691 (bank10691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10692 := params 3
abbrev ray10692 := rays 3
def bank10692 : Fin 2 → Cell := twoBank p10692 ray10692
theorem signs10692 : ∀ j, Signs p10692 (bank10692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10693 := params 4
abbrev ray10693 := rays 4
def bank10693 : Fin 2 → Cell := twoBank p10693 ray10693
theorem signs10693 : ∀ j, Signs p10693 (bank10693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10694 := params 5
abbrev ray10694 := rays 5
def bank10694 : Fin 2 → Cell := twoBank p10694 ray10694
theorem signs10694 : ∀ j, Signs p10694 (bank10694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10695 := params 6
abbrev ray10695 := rays 6
def bank10695 : Fin 2 → Cell := twoBank p10695 ray10695
theorem signs10695 : ∀ j, Signs p10695 (bank10695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10696 := params 7
abbrev ray10696 := rays 7
def bank10696 : Fin 2 → Cell := twoBank p10696 ray10696
theorem signs10696 : ∀ j, Signs p10696 (bank10696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10697 := params 8
abbrev ray10697 := rays 8
def bank10697 : Fin 2 → Cell := twoBank p10697 ray10697
theorem signs10697 : ∀ j, Signs p10697 (bank10697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10698 := params 9
abbrev ray10698 := rays 9
def bank10698 : Fin 2 → Cell := twoBank p10698 ray10698
theorem signs10698 : ∀ j, Signs p10698 (bank10698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10699 := params 10
abbrev ray10699 := rays 10
def bank10699 : Fin 2 → Cell := twoBank p10699 ray10699
theorem signs10699 : ∀ j, Signs p10699 (bank10699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10700 := params 11
abbrev ray10700 := rays 11
def bank10700 : Fin 2 → Cell := twoBank p10700 ray10700
theorem signs10700 : ∀ j, Signs p10700 (bank10700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10701 := params 12
abbrev ray10701 := rays 12
def bank10701 : Fin 2 → Cell := twoBank p10701 ray10701
theorem signs10701 : ∀ j, Signs p10701 (bank10701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10702 := params 13
abbrev ray10702 := rays 13
def bank10702 : Fin 2 → Cell := twoBank p10702 ray10702
theorem signs10702 : ∀ j, Signs p10702 (bank10702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10703 := params 14
abbrev ray10703 := rays 14
def bank10703 : Fin 2 → Cell := twoBank p10703 ray10703
theorem signs10703 : ∀ j, Signs p10703 (bank10703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10704 := params 15
abbrev ray10704 := rays 15
def bank10704 : Fin 2 → Cell := twoBank p10704 ray10704
theorem signs10704 : ∀ j, Signs p10704 (bank10704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10705 := params 16
abbrev ray10705 := rays 16
def bank10705 : Fin 2 → Cell := twoBank p10705 ray10705
theorem signs10705 : ∀ j, Signs p10705 (bank10705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10706 := params 17
abbrev ray10706 := rays 17
def bank10706 : Fin 2 → Cell := twoBank p10706 ray10706
theorem signs10706 : ∀ j, Signs p10706 (bank10706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10707 := params 18
abbrev ray10707 := rays 18
def bank10707 : Fin 2 → Cell := twoBank p10707 ray10707
theorem signs10707 : ∀ j, Signs p10707 (bank10707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10708 := params 19
abbrev ray10708 := rays 19
def bank10708 : Fin 2 → Cell := twoBank p10708 ray10708
theorem signs10708 : ∀ j, Signs p10708 (bank10708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10709 := params 20
abbrev ray10709 := rays 20
def bank10709 : Fin 2 → Cell := twoBank p10709 ray10709
theorem signs10709 : ∀ j, Signs p10709 (bank10709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10710 := params 21
abbrev ray10710 := rays 21
def bank10710 : Fin 2 → Cell := twoBank p10710 ray10710
theorem signs10710 : ∀ j, Signs p10710 (bank10710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10711 := params 22
abbrev ray10711 := rays 22
def bank10711 : Fin 2 → Cell := twoBank p10711 ray10711
theorem signs10711 : ∀ j, Signs p10711 (bank10711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10712 := params 23
abbrev ray10712 := rays 23
def bank10712 : Fin 2 → Cell := twoBank p10712 ray10712
theorem signs10712 : ∀ j, Signs p10712 (bank10712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10713 := params 24
abbrev ray10713 := rays 24
def bank10713 : Fin 2 → Cell := twoBank p10713 ray10713
theorem signs10713 : ∀ j, Signs p10713 (bank10713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10714 := params 25
abbrev ray10714 := rays 25
def bank10714 : Fin 2 → Cell := twoBank p10714 ray10714
theorem signs10714 : ∀ j, Signs p10714 (bank10714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10715 := params 26
abbrev ray10715 := rays 26
def bank10715 : Fin 2 → Cell := twoBank p10715 ray10715
theorem signs10715 : ∀ j, Signs p10715 (bank10715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10716 := params 27
abbrev ray10716 := rays 27
def bank10716 : Fin 2 → Cell := twoBank p10716 ray10716
theorem signs10716 : ∀ j, Signs p10716 (bank10716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10717 := params 28
abbrev ray10717 := rays 28
def bank10717 : Fin 2 → Cell := twoBank p10717 ray10717
theorem signs10717 : ∀ j, Signs p10717 (bank10717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10718 := params 29
abbrev ray10718 := rays 29
def bank10718 : Fin 2 → Cell := twoBank p10718 ray10718
theorem signs10718 : ∀ j, Signs p10718 (bank10718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10719 := params 30
abbrev ray10719 := rays 30
def bank10719 : Fin 2 → Cell := twoBank p10719 ray10719
theorem signs10719 : ∀ j, Signs p10719 (bank10719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10720 := params 31
abbrev ray10720 := rays 31
def bank10720 : Fin 2 → Cell := twoBank p10720 ray10720
theorem signs10720 : ∀ j, Signs p10720 (bank10720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10689_10720
