/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06689_06720
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98568764119611,98568468312461,98568172482733,98567876630428,98567580755546,98567284858089,98566988938057,98566692995451,98566397030272,98566101042520,98565805032197,98565508999303,98565212943839,98564916865806,98564620765205,98564324642036,98564028496300,98563732327999,98563436137133,98563139923702,98562843687708,98562547429151,98562251148032,98561954844352,98561658518112,98561362169313,98561065797955,98560769404040,98560472987568,98560176548540,98559880086956,98559583602818,98559287096126]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6688+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6689 := params 0
abbrev ray6689 := rays 0
def bank6689 : Fin 2 → Cell := twoBank p6689 ray6689
theorem signs6689 : ∀ j, Signs p6689 (bank6689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6690 := params 1
abbrev ray6690 := rays 1
def bank6690 : Fin 2 → Cell := twoBank p6690 ray6690
theorem signs6690 : ∀ j, Signs p6690 (bank6690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6691 := params 2
abbrev ray6691 := rays 2
def bank6691 : Fin 2 → Cell := twoBank p6691 ray6691
theorem signs6691 : ∀ j, Signs p6691 (bank6691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6692 := params 3
abbrev ray6692 := rays 3
def bank6692 : Fin 2 → Cell := twoBank p6692 ray6692
theorem signs6692 : ∀ j, Signs p6692 (bank6692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6693 := params 4
abbrev ray6693 := rays 4
def bank6693 : Fin 2 → Cell := twoBank p6693 ray6693
theorem signs6693 : ∀ j, Signs p6693 (bank6693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6694 := params 5
abbrev ray6694 := rays 5
def bank6694 : Fin 2 → Cell := twoBank p6694 ray6694
theorem signs6694 : ∀ j, Signs p6694 (bank6694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6695 := params 6
abbrev ray6695 := rays 6
def bank6695 : Fin 2 → Cell := twoBank p6695 ray6695
theorem signs6695 : ∀ j, Signs p6695 (bank6695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6696 := params 7
abbrev ray6696 := rays 7
def bank6696 : Fin 2 → Cell := twoBank p6696 ray6696
theorem signs6696 : ∀ j, Signs p6696 (bank6696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6697 := params 8
abbrev ray6697 := rays 8
def bank6697 : Fin 2 → Cell := twoBank p6697 ray6697
theorem signs6697 : ∀ j, Signs p6697 (bank6697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6698 := params 9
abbrev ray6698 := rays 9
def bank6698 : Fin 2 → Cell := twoBank p6698 ray6698
theorem signs6698 : ∀ j, Signs p6698 (bank6698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6699 := params 10
abbrev ray6699 := rays 10
def bank6699 : Fin 2 → Cell := twoBank p6699 ray6699
theorem signs6699 : ∀ j, Signs p6699 (bank6699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6700 := params 11
abbrev ray6700 := rays 11
def bank6700 : Fin 2 → Cell := twoBank p6700 ray6700
theorem signs6700 : ∀ j, Signs p6700 (bank6700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6701 := params 12
abbrev ray6701 := rays 12
def bank6701 : Fin 2 → Cell := twoBank p6701 ray6701
theorem signs6701 : ∀ j, Signs p6701 (bank6701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6702 := params 13
abbrev ray6702 := rays 13
def bank6702 : Fin 2 → Cell := twoBank p6702 ray6702
theorem signs6702 : ∀ j, Signs p6702 (bank6702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6703 := params 14
abbrev ray6703 := rays 14
def bank6703 : Fin 2 → Cell := twoBank p6703 ray6703
theorem signs6703 : ∀ j, Signs p6703 (bank6703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6704 := params 15
abbrev ray6704 := rays 15
def bank6704 : Fin 2 → Cell := twoBank p6704 ray6704
theorem signs6704 : ∀ j, Signs p6704 (bank6704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6705 := params 16
abbrev ray6705 := rays 16
def bank6705 : Fin 2 → Cell := twoBank p6705 ray6705
theorem signs6705 : ∀ j, Signs p6705 (bank6705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6706 := params 17
abbrev ray6706 := rays 17
def bank6706 : Fin 2 → Cell := twoBank p6706 ray6706
theorem signs6706 : ∀ j, Signs p6706 (bank6706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6707 := params 18
abbrev ray6707 := rays 18
def bank6707 : Fin 2 → Cell := twoBank p6707 ray6707
theorem signs6707 : ∀ j, Signs p6707 (bank6707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6708 := params 19
abbrev ray6708 := rays 19
def bank6708 : Fin 2 → Cell := twoBank p6708 ray6708
theorem signs6708 : ∀ j, Signs p6708 (bank6708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6709 := params 20
abbrev ray6709 := rays 20
def bank6709 : Fin 2 → Cell := twoBank p6709 ray6709
theorem signs6709 : ∀ j, Signs p6709 (bank6709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6710 := params 21
abbrev ray6710 := rays 21
def bank6710 : Fin 2 → Cell := twoBank p6710 ray6710
theorem signs6710 : ∀ j, Signs p6710 (bank6710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6711 := params 22
abbrev ray6711 := rays 22
def bank6711 : Fin 2 → Cell := twoBank p6711 ray6711
theorem signs6711 : ∀ j, Signs p6711 (bank6711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6712 := params 23
abbrev ray6712 := rays 23
def bank6712 : Fin 2 → Cell := twoBank p6712 ray6712
theorem signs6712 : ∀ j, Signs p6712 (bank6712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6713 := params 24
abbrev ray6713 := rays 24
def bank6713 : Fin 2 → Cell := twoBank p6713 ray6713
theorem signs6713 : ∀ j, Signs p6713 (bank6713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6714 := params 25
abbrev ray6714 := rays 25
def bank6714 : Fin 2 → Cell := twoBank p6714 ray6714
theorem signs6714 : ∀ j, Signs p6714 (bank6714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6715 := params 26
abbrev ray6715 := rays 26
def bank6715 : Fin 2 → Cell := twoBank p6715 ray6715
theorem signs6715 : ∀ j, Signs p6715 (bank6715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6716 := params 27
abbrev ray6716 := rays 27
def bank6716 : Fin 2 → Cell := twoBank p6716 ray6716
theorem signs6716 : ∀ j, Signs p6716 (bank6716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6717 := params 28
abbrev ray6717 := rays 28
def bank6717 : Fin 2 → Cell := twoBank p6717 ray6717
theorem signs6717 : ∀ j, Signs p6717 (bank6717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6718 := params 29
abbrev ray6718 := rays 29
def bank6718 : Fin 2 → Cell := twoBank p6718 ray6718
theorem signs6718 : ∀ j, Signs p6718 (bank6718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6719 := params 30
abbrev ray6719 := rays 30
def bank6719 : Fin 2 → Cell := twoBank p6719 ray6719
theorem signs6719 : ∀ j, Signs p6719 (bank6719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6720 := params 31
abbrev ray6720 := rays 31
def bank6720 : Fin 2 → Cell := twoBank p6720 ray6720
theorem signs6720 : ∀ j, Signs p6720 (bank6720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06689_06720
