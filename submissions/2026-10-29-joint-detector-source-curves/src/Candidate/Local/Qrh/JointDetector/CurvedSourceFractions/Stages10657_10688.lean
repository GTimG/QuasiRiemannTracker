/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10657_10688
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97224892389529,97224512528368,97224132647219,97223752746083,97223372824960,97222992883851,97222612922757,97222232941678,97221852940614,97221472919566,97221092878534,97220712817519,97220332736522,97219952635543,97219572514582,97219192373640,97218812212718,97218432031816,97218051830934,97217671610073,97217291369234,97216911108417,97216530827622,97216150526850,97215770206102,97215389865378,97215009504678,97214629124004,97214248723355,97213868302732,97213487862136,97213107401567,97212726921026]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10656+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10657 := params 0
abbrev ray10657 := rays 0
def bank10657 : Fin 2 → Cell := twoBank p10657 ray10657
theorem signs10657 : ∀ j, Signs p10657 (bank10657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10658 := params 1
abbrev ray10658 := rays 1
def bank10658 : Fin 2 → Cell := twoBank p10658 ray10658
theorem signs10658 : ∀ j, Signs p10658 (bank10658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10659 := params 2
abbrev ray10659 := rays 2
def bank10659 : Fin 2 → Cell := twoBank p10659 ray10659
theorem signs10659 : ∀ j, Signs p10659 (bank10659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10660 := params 3
abbrev ray10660 := rays 3
def bank10660 : Fin 2 → Cell := twoBank p10660 ray10660
theorem signs10660 : ∀ j, Signs p10660 (bank10660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10661 := params 4
abbrev ray10661 := rays 4
def bank10661 : Fin 2 → Cell := twoBank p10661 ray10661
theorem signs10661 : ∀ j, Signs p10661 (bank10661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10662 := params 5
abbrev ray10662 := rays 5
def bank10662 : Fin 2 → Cell := twoBank p10662 ray10662
theorem signs10662 : ∀ j, Signs p10662 (bank10662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10663 := params 6
abbrev ray10663 := rays 6
def bank10663 : Fin 2 → Cell := twoBank p10663 ray10663
theorem signs10663 : ∀ j, Signs p10663 (bank10663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10664 := params 7
abbrev ray10664 := rays 7
def bank10664 : Fin 2 → Cell := twoBank p10664 ray10664
theorem signs10664 : ∀ j, Signs p10664 (bank10664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10665 := params 8
abbrev ray10665 := rays 8
def bank10665 : Fin 2 → Cell := twoBank p10665 ray10665
theorem signs10665 : ∀ j, Signs p10665 (bank10665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10666 := params 9
abbrev ray10666 := rays 9
def bank10666 : Fin 2 → Cell := twoBank p10666 ray10666
theorem signs10666 : ∀ j, Signs p10666 (bank10666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10667 := params 10
abbrev ray10667 := rays 10
def bank10667 : Fin 2 → Cell := twoBank p10667 ray10667
theorem signs10667 : ∀ j, Signs p10667 (bank10667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10668 := params 11
abbrev ray10668 := rays 11
def bank10668 : Fin 2 → Cell := twoBank p10668 ray10668
theorem signs10668 : ∀ j, Signs p10668 (bank10668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10669 := params 12
abbrev ray10669 := rays 12
def bank10669 : Fin 2 → Cell := twoBank p10669 ray10669
theorem signs10669 : ∀ j, Signs p10669 (bank10669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10670 := params 13
abbrev ray10670 := rays 13
def bank10670 : Fin 2 → Cell := twoBank p10670 ray10670
theorem signs10670 : ∀ j, Signs p10670 (bank10670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10671 := params 14
abbrev ray10671 := rays 14
def bank10671 : Fin 2 → Cell := twoBank p10671 ray10671
theorem signs10671 : ∀ j, Signs p10671 (bank10671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10672 := params 15
abbrev ray10672 := rays 15
def bank10672 : Fin 2 → Cell := twoBank p10672 ray10672
theorem signs10672 : ∀ j, Signs p10672 (bank10672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10673 := params 16
abbrev ray10673 := rays 16
def bank10673 : Fin 2 → Cell := twoBank p10673 ray10673
theorem signs10673 : ∀ j, Signs p10673 (bank10673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10674 := params 17
abbrev ray10674 := rays 17
def bank10674 : Fin 2 → Cell := twoBank p10674 ray10674
theorem signs10674 : ∀ j, Signs p10674 (bank10674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10675 := params 18
abbrev ray10675 := rays 18
def bank10675 : Fin 2 → Cell := twoBank p10675 ray10675
theorem signs10675 : ∀ j, Signs p10675 (bank10675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10676 := params 19
abbrev ray10676 := rays 19
def bank10676 : Fin 2 → Cell := twoBank p10676 ray10676
theorem signs10676 : ∀ j, Signs p10676 (bank10676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10677 := params 20
abbrev ray10677 := rays 20
def bank10677 : Fin 2 → Cell := twoBank p10677 ray10677
theorem signs10677 : ∀ j, Signs p10677 (bank10677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10678 := params 21
abbrev ray10678 := rays 21
def bank10678 : Fin 2 → Cell := twoBank p10678 ray10678
theorem signs10678 : ∀ j, Signs p10678 (bank10678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10679 := params 22
abbrev ray10679 := rays 22
def bank10679 : Fin 2 → Cell := twoBank p10679 ray10679
theorem signs10679 : ∀ j, Signs p10679 (bank10679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10680 := params 23
abbrev ray10680 := rays 23
def bank10680 : Fin 2 → Cell := twoBank p10680 ray10680
theorem signs10680 : ∀ j, Signs p10680 (bank10680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10681 := params 24
abbrev ray10681 := rays 24
def bank10681 : Fin 2 → Cell := twoBank p10681 ray10681
theorem signs10681 : ∀ j, Signs p10681 (bank10681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10682 := params 25
abbrev ray10682 := rays 25
def bank10682 : Fin 2 → Cell := twoBank p10682 ray10682
theorem signs10682 : ∀ j, Signs p10682 (bank10682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10683 := params 26
abbrev ray10683 := rays 26
def bank10683 : Fin 2 → Cell := twoBank p10683 ray10683
theorem signs10683 : ∀ j, Signs p10683 (bank10683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10684 := params 27
abbrev ray10684 := rays 27
def bank10684 : Fin 2 → Cell := twoBank p10684 ray10684
theorem signs10684 : ∀ j, Signs p10684 (bank10684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10685 := params 28
abbrev ray10685 := rays 28
def bank10685 : Fin 2 → Cell := twoBank p10685 ray10685
theorem signs10685 : ∀ j, Signs p10685 (bank10685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10686 := params 29
abbrev ray10686 := rays 29
def bank10686 : Fin 2 → Cell := twoBank p10686 ray10686
theorem signs10686 : ∀ j, Signs p10686 (bank10686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10687 := params 30
abbrev ray10687 := rays 30
def bank10687 : Fin 2 → Cell := twoBank p10687 ray10687
theorem signs10687 : ∀ j, Signs p10687 (bank10687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10688 := params 31
abbrev ray10688 := rays 31
def bank10688 : Fin 2 → Cell := twoBank p10688 ray10688
theorem signs10688 : ∀ j, Signs p10688 (bank10688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10657_10688
