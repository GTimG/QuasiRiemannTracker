/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15681_15712
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95083622654190,95083154397632,95082686125066,95082217836493,95081749531912,95081281211324,95080812874729,95080344522126,95079876153516,95079407768899,95078939368275,95078470951644,95078002519006,95077534070361,95077065605709,95076597125050,95076128628384,95075660115712,95075191587033,95074723042347,95074254481655,95073785904956,95073317312251,95072848703540,95072380078822,95071911438098,95071442781368,95070974108632,95070505419890,95070036715142,95069567994388,95069099257628,95068630504862]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15680+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15681 := params 0
abbrev ray15681 := rays 0
def bank15681 : Fin 1 → Cell := oneBank p15681 ray15681
theorem signs15681 : ∀ j, Signs p15681 (bank15681 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15682 := params 1
abbrev ray15682 := rays 1
def bank15682 : Fin 1 → Cell := oneBank p15682 ray15682
theorem signs15682 : ∀ j, Signs p15682 (bank15682 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15683 := params 2
abbrev ray15683 := rays 2
def bank15683 : Fin 1 → Cell := oneBank p15683 ray15683
theorem signs15683 : ∀ j, Signs p15683 (bank15683 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15684 := params 3
abbrev ray15684 := rays 3
def bank15684 : Fin 1 → Cell := oneBank p15684 ray15684
theorem signs15684 : ∀ j, Signs p15684 (bank15684 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15685 := params 4
abbrev ray15685 := rays 4
def bank15685 : Fin 1 → Cell := oneBank p15685 ray15685
theorem signs15685 : ∀ j, Signs p15685 (bank15685 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15686 := params 5
abbrev ray15686 := rays 5
def bank15686 : Fin 1 → Cell := oneBank p15686 ray15686
theorem signs15686 : ∀ j, Signs p15686 (bank15686 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15687 := params 6
abbrev ray15687 := rays 6
def bank15687 : Fin 1 → Cell := oneBank p15687 ray15687
theorem signs15687 : ∀ j, Signs p15687 (bank15687 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15688 := params 7
abbrev ray15688 := rays 7
def bank15688 : Fin 1 → Cell := oneBank p15688 ray15688
theorem signs15688 : ∀ j, Signs p15688 (bank15688 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15689 := params 8
abbrev ray15689 := rays 8
def bank15689 : Fin 1 → Cell := oneBank p15689 ray15689
theorem signs15689 : ∀ j, Signs p15689 (bank15689 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15690 := params 9
abbrev ray15690 := rays 9
def bank15690 : Fin 1 → Cell := oneBank p15690 ray15690
theorem signs15690 : ∀ j, Signs p15690 (bank15690 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15691 := params 10
abbrev ray15691 := rays 10
def bank15691 : Fin 1 → Cell := oneBank p15691 ray15691
theorem signs15691 : ∀ j, Signs p15691 (bank15691 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15692 := params 11
abbrev ray15692 := rays 11
def bank15692 : Fin 1 → Cell := oneBank p15692 ray15692
theorem signs15692 : ∀ j, Signs p15692 (bank15692 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15693 := params 12
abbrev ray15693 := rays 12
def bank15693 : Fin 1 → Cell := oneBank p15693 ray15693
theorem signs15693 : ∀ j, Signs p15693 (bank15693 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15694 := params 13
abbrev ray15694 := rays 13
def bank15694 : Fin 1 → Cell := oneBank p15694 ray15694
theorem signs15694 : ∀ j, Signs p15694 (bank15694 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15695 := params 14
abbrev ray15695 := rays 14
def bank15695 : Fin 1 → Cell := oneBank p15695 ray15695
theorem signs15695 : ∀ j, Signs p15695 (bank15695 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15696 := params 15
abbrev ray15696 := rays 15
def bank15696 : Fin 1 → Cell := oneBank p15696 ray15696
theorem signs15696 : ∀ j, Signs p15696 (bank15696 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15697 := params 16
abbrev ray15697 := rays 16
def bank15697 : Fin 1 → Cell := oneBank p15697 ray15697
theorem signs15697 : ∀ j, Signs p15697 (bank15697 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15698 := params 17
abbrev ray15698 := rays 17
def bank15698 : Fin 1 → Cell := oneBank p15698 ray15698
theorem signs15698 : ∀ j, Signs p15698 (bank15698 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15699 := params 18
abbrev ray15699 := rays 18
def bank15699 : Fin 1 → Cell := oneBank p15699 ray15699
theorem signs15699 : ∀ j, Signs p15699 (bank15699 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15700 := params 19
abbrev ray15700 := rays 19
def bank15700 : Fin 1 → Cell := oneBank p15700 ray15700
theorem signs15700 : ∀ j, Signs p15700 (bank15700 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15701 := params 20
abbrev ray15701 := rays 20
def bank15701 : Fin 1 → Cell := oneBank p15701 ray15701
theorem signs15701 : ∀ j, Signs p15701 (bank15701 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15702 := params 21
abbrev ray15702 := rays 21
def bank15702 : Fin 1 → Cell := oneBank p15702 ray15702
theorem signs15702 : ∀ j, Signs p15702 (bank15702 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15703 := params 22
abbrev ray15703 := rays 22
def bank15703 : Fin 1 → Cell := oneBank p15703 ray15703
theorem signs15703 : ∀ j, Signs p15703 (bank15703 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15704 := params 23
abbrev ray15704 := rays 23
def bank15704 : Fin 1 → Cell := oneBank p15704 ray15704
theorem signs15704 : ∀ j, Signs p15704 (bank15704 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15705 := params 24
abbrev ray15705 := rays 24
def bank15705 : Fin 1 → Cell := oneBank p15705 ray15705
theorem signs15705 : ∀ j, Signs p15705 (bank15705 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15706 := params 25
abbrev ray15706 := rays 25
def bank15706 : Fin 1 → Cell := oneBank p15706 ray15706
theorem signs15706 : ∀ j, Signs p15706 (bank15706 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15707 := params 26
abbrev ray15707 := rays 26
def bank15707 : Fin 1 → Cell := oneBank p15707 ray15707
theorem signs15707 : ∀ j, Signs p15707 (bank15707 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15708 := params 27
abbrev ray15708 := rays 27
def bank15708 : Fin 1 → Cell := oneBank p15708 ray15708
theorem signs15708 : ∀ j, Signs p15708 (bank15708 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15709 := params 28
abbrev ray15709 := rays 28
def bank15709 : Fin 1 → Cell := oneBank p15709 ray15709
theorem signs15709 : ∀ j, Signs p15709 (bank15709 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15710 := params 29
abbrev ray15710 := rays 29
def bank15710 : Fin 1 → Cell := oneBank p15710 ray15710
theorem signs15710 : ∀ j, Signs p15710 (bank15710 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15711 := params 30
abbrev ray15711 := rays 30
def bank15711 : Fin 1 → Cell := oneBank p15711 ray15711
theorem signs15711 : ∀ j, Signs p15711 (bank15711 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15712 := params 31
abbrev ray15712 := rays 31
def bank15712 : Fin 1 → Cell := oneBank p15712 ray15712
theorem signs15712 : ∀ j, Signs p15712 (bank15712 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15681_15712
