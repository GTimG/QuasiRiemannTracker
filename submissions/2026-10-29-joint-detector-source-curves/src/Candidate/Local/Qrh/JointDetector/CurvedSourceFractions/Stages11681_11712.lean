/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11681_11712
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96825533919940,96825133848250,96824733757064,96824333646382,96823933516205,96823533366533,96823133197367,96822733008707,96822332800554,96821932572908,96821532325770,96821132059140,96820731773018,96820331467405,96819931142301,96819530797707,96819130433624,96818730050051,96818329646989,96817929224439,96817528782401,96817128320876,96816727839864,96816327339365,96815926819380,96815526279909,96815125720953,96814725142512,96814324544587,96813923927178,96813523290285,96813122633909,96812721958051]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11680+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11681 := params 0
abbrev ray11681 := rays 0
def bank11681 : Fin 2 → Cell := twoBank p11681 ray11681
theorem signs11681 : ∀ j, Signs p11681 (bank11681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11682 := params 1
abbrev ray11682 := rays 1
def bank11682 : Fin 2 → Cell := twoBank p11682 ray11682
theorem signs11682 : ∀ j, Signs p11682 (bank11682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11683 := params 2
abbrev ray11683 := rays 2
def bank11683 : Fin 2 → Cell := twoBank p11683 ray11683
theorem signs11683 : ∀ j, Signs p11683 (bank11683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11684 := params 3
abbrev ray11684 := rays 3
def bank11684 : Fin 2 → Cell := twoBank p11684 ray11684
theorem signs11684 : ∀ j, Signs p11684 (bank11684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11685 := params 4
abbrev ray11685 := rays 4
def bank11685 : Fin 2 → Cell := twoBank p11685 ray11685
theorem signs11685 : ∀ j, Signs p11685 (bank11685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11686 := params 5
abbrev ray11686 := rays 5
def bank11686 : Fin 2 → Cell := twoBank p11686 ray11686
theorem signs11686 : ∀ j, Signs p11686 (bank11686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11687 := params 6
abbrev ray11687 := rays 6
def bank11687 : Fin 2 → Cell := twoBank p11687 ray11687
theorem signs11687 : ∀ j, Signs p11687 (bank11687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11688 := params 7
abbrev ray11688 := rays 7
def bank11688 : Fin 2 → Cell := twoBank p11688 ray11688
theorem signs11688 : ∀ j, Signs p11688 (bank11688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11689 := params 8
abbrev ray11689 := rays 8
def bank11689 : Fin 2 → Cell := twoBank p11689 ray11689
theorem signs11689 : ∀ j, Signs p11689 (bank11689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11690 := params 9
abbrev ray11690 := rays 9
def bank11690 : Fin 2 → Cell := twoBank p11690 ray11690
theorem signs11690 : ∀ j, Signs p11690 (bank11690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11691 := params 10
abbrev ray11691 := rays 10
def bank11691 : Fin 2 → Cell := twoBank p11691 ray11691
theorem signs11691 : ∀ j, Signs p11691 (bank11691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11692 := params 11
abbrev ray11692 := rays 11
def bank11692 : Fin 2 → Cell := twoBank p11692 ray11692
theorem signs11692 : ∀ j, Signs p11692 (bank11692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11693 := params 12
abbrev ray11693 := rays 12
def bank11693 : Fin 2 → Cell := twoBank p11693 ray11693
theorem signs11693 : ∀ j, Signs p11693 (bank11693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11694 := params 13
abbrev ray11694 := rays 13
def bank11694 : Fin 2 → Cell := twoBank p11694 ray11694
theorem signs11694 : ∀ j, Signs p11694 (bank11694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11695 := params 14
abbrev ray11695 := rays 14
def bank11695 : Fin 2 → Cell := twoBank p11695 ray11695
theorem signs11695 : ∀ j, Signs p11695 (bank11695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11696 := params 15
abbrev ray11696 := rays 15
def bank11696 : Fin 2 → Cell := twoBank p11696 ray11696
theorem signs11696 : ∀ j, Signs p11696 (bank11696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11697 := params 16
abbrev ray11697 := rays 16
def bank11697 : Fin 2 → Cell := twoBank p11697 ray11697
theorem signs11697 : ∀ j, Signs p11697 (bank11697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11698 := params 17
abbrev ray11698 := rays 17
def bank11698 : Fin 2 → Cell := twoBank p11698 ray11698
theorem signs11698 : ∀ j, Signs p11698 (bank11698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11699 := params 18
abbrev ray11699 := rays 18
def bank11699 : Fin 2 → Cell := twoBank p11699 ray11699
theorem signs11699 : ∀ j, Signs p11699 (bank11699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11700 := params 19
abbrev ray11700 := rays 19
def bank11700 : Fin 2 → Cell := twoBank p11700 ray11700
theorem signs11700 : ∀ j, Signs p11700 (bank11700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11701 := params 20
abbrev ray11701 := rays 20
def bank11701 : Fin 2 → Cell := twoBank p11701 ray11701
theorem signs11701 : ∀ j, Signs p11701 (bank11701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11702 := params 21
abbrev ray11702 := rays 21
def bank11702 : Fin 2 → Cell := twoBank p11702 ray11702
theorem signs11702 : ∀ j, Signs p11702 (bank11702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11703 := params 22
abbrev ray11703 := rays 22
def bank11703 : Fin 2 → Cell := twoBank p11703 ray11703
theorem signs11703 : ∀ j, Signs p11703 (bank11703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11704 := params 23
abbrev ray11704 := rays 23
def bank11704 : Fin 2 → Cell := twoBank p11704 ray11704
theorem signs11704 : ∀ j, Signs p11704 (bank11704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11705 := params 24
abbrev ray11705 := rays 24
def bank11705 : Fin 2 → Cell := twoBank p11705 ray11705
theorem signs11705 : ∀ j, Signs p11705 (bank11705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11706 := params 25
abbrev ray11706 := rays 25
def bank11706 : Fin 2 → Cell := twoBank p11706 ray11706
theorem signs11706 : ∀ j, Signs p11706 (bank11706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11707 := params 26
abbrev ray11707 := rays 26
def bank11707 : Fin 2 → Cell := twoBank p11707 ray11707
theorem signs11707 : ∀ j, Signs p11707 (bank11707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11708 := params 27
abbrev ray11708 := rays 27
def bank11708 : Fin 2 → Cell := twoBank p11708 ray11708
theorem signs11708 : ∀ j, Signs p11708 (bank11708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11709 := params 28
abbrev ray11709 := rays 28
def bank11709 : Fin 2 → Cell := twoBank p11709 ray11709
theorem signs11709 : ∀ j, Signs p11709 (bank11709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11710 := params 29
abbrev ray11710 := rays 29
def bank11710 : Fin 2 → Cell := twoBank p11710 ray11710
theorem signs11710 : ∀ j, Signs p11710 (bank11710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11711 := params 30
abbrev ray11711 := rays 30
def bank11711 : Fin 2 → Cell := twoBank p11711 ray11711
theorem signs11711 : ∀ j, Signs p11711 (bank11711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11712 := params 31
abbrev ray11712 := rays 31
def bank11712 : Fin 2 → Cell := twoBank p11712 ray11712
theorem signs11712 : ∀ j, Signs p11712 (bank11712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11681_11712
