/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15777_15808
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95038597038343,95038127245320,95037657436295,95037187611268,95036717770239,95036247913208,95035778040175,95035308151140,95034838246103,95034368325064,95033898388023,95033428434981,95032958465937,95032488480892,95032018479845,95031548462797,95031078429747,95030608380696,95030138315644,95029668234590,95029198137535,95028728024479,95028257895422,95027787750364,95027317589305,95026847412245,95026377219184,95025907010122,95025436785059,95024966543996,95024496286932,95024026013867,95023555724802]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15776+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15777 := params 0
abbrev ray15777 := rays 0
def bank15777 : Fin 1 → Cell := oneBank p15777 ray15777
theorem signs15777 : ∀ j, Signs p15777 (bank15777 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15778 := params 1
abbrev ray15778 := rays 1
def bank15778 : Fin 1 → Cell := oneBank p15778 ray15778
theorem signs15778 : ∀ j, Signs p15778 (bank15778 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15779 := params 2
abbrev ray15779 := rays 2
def bank15779 : Fin 1 → Cell := oneBank p15779 ray15779
theorem signs15779 : ∀ j, Signs p15779 (bank15779 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15780 := params 3
abbrev ray15780 := rays 3
def bank15780 : Fin 1 → Cell := oneBank p15780 ray15780
theorem signs15780 : ∀ j, Signs p15780 (bank15780 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15781 := params 4
abbrev ray15781 := rays 4
def bank15781 : Fin 1 → Cell := oneBank p15781 ray15781
theorem signs15781 : ∀ j, Signs p15781 (bank15781 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15782 := params 5
abbrev ray15782 := rays 5
def bank15782 : Fin 1 → Cell := oneBank p15782 ray15782
theorem signs15782 : ∀ j, Signs p15782 (bank15782 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15783 := params 6
abbrev ray15783 := rays 6
def bank15783 : Fin 1 → Cell := oneBank p15783 ray15783
theorem signs15783 : ∀ j, Signs p15783 (bank15783 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15784 := params 7
abbrev ray15784 := rays 7
def bank15784 : Fin 1 → Cell := oneBank p15784 ray15784
theorem signs15784 : ∀ j, Signs p15784 (bank15784 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15785 := params 8
abbrev ray15785 := rays 8
def bank15785 : Fin 1 → Cell := oneBank p15785 ray15785
theorem signs15785 : ∀ j, Signs p15785 (bank15785 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15786 := params 9
abbrev ray15786 := rays 9
def bank15786 : Fin 1 → Cell := oneBank p15786 ray15786
theorem signs15786 : ∀ j, Signs p15786 (bank15786 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15787 := params 10
abbrev ray15787 := rays 10
def bank15787 : Fin 1 → Cell := oneBank p15787 ray15787
theorem signs15787 : ∀ j, Signs p15787 (bank15787 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15788 := params 11
abbrev ray15788 := rays 11
def bank15788 : Fin 1 → Cell := oneBank p15788 ray15788
theorem signs15788 : ∀ j, Signs p15788 (bank15788 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15789 := params 12
abbrev ray15789 := rays 12
def bank15789 : Fin 1 → Cell := oneBank p15789 ray15789
theorem signs15789 : ∀ j, Signs p15789 (bank15789 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15790 := params 13
abbrev ray15790 := rays 13
def bank15790 : Fin 1 → Cell := oneBank p15790 ray15790
theorem signs15790 : ∀ j, Signs p15790 (bank15790 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15791 := params 14
abbrev ray15791 := rays 14
def bank15791 : Fin 1 → Cell := oneBank p15791 ray15791
theorem signs15791 : ∀ j, Signs p15791 (bank15791 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15792 := params 15
abbrev ray15792 := rays 15
def bank15792 : Fin 1 → Cell := oneBank p15792 ray15792
theorem signs15792 : ∀ j, Signs p15792 (bank15792 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15793 := params 16
abbrev ray15793 := rays 16
def bank15793 : Fin 1 → Cell := oneBank p15793 ray15793
theorem signs15793 : ∀ j, Signs p15793 (bank15793 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15794 := params 17
abbrev ray15794 := rays 17
def bank15794 : Fin 1 → Cell := oneBank p15794 ray15794
theorem signs15794 : ∀ j, Signs p15794 (bank15794 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15795 := params 18
abbrev ray15795 := rays 18
def bank15795 : Fin 1 → Cell := oneBank p15795 ray15795
theorem signs15795 : ∀ j, Signs p15795 (bank15795 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15796 := params 19
abbrev ray15796 := rays 19
def bank15796 : Fin 1 → Cell := oneBank p15796 ray15796
theorem signs15796 : ∀ j, Signs p15796 (bank15796 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15797 := params 20
abbrev ray15797 := rays 20
def bank15797 : Fin 1 → Cell := oneBank p15797 ray15797
theorem signs15797 : ∀ j, Signs p15797 (bank15797 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15798 := params 21
abbrev ray15798 := rays 21
def bank15798 : Fin 1 → Cell := oneBank p15798 ray15798
theorem signs15798 : ∀ j, Signs p15798 (bank15798 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15799 := params 22
abbrev ray15799 := rays 22
def bank15799 : Fin 1 → Cell := oneBank p15799 ray15799
theorem signs15799 : ∀ j, Signs p15799 (bank15799 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15800 := params 23
abbrev ray15800 := rays 23
def bank15800 : Fin 1 → Cell := oneBank p15800 ray15800
theorem signs15800 : ∀ j, Signs p15800 (bank15800 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15801 := params 24
abbrev ray15801 := rays 24
def bank15801 : Fin 1 → Cell := oneBank p15801 ray15801
theorem signs15801 : ∀ j, Signs p15801 (bank15801 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15802 := params 25
abbrev ray15802 := rays 25
def bank15802 : Fin 1 → Cell := oneBank p15802 ray15802
theorem signs15802 : ∀ j, Signs p15802 (bank15802 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15803 := params 26
abbrev ray15803 := rays 26
def bank15803 : Fin 1 → Cell := oneBank p15803 ray15803
theorem signs15803 : ∀ j, Signs p15803 (bank15803 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15804 := params 27
abbrev ray15804 := rays 27
def bank15804 : Fin 1 → Cell := oneBank p15804 ray15804
theorem signs15804 : ∀ j, Signs p15804 (bank15804 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15805 := params 28
abbrev ray15805 := rays 28
def bank15805 : Fin 1 → Cell := oneBank p15805 ray15805
theorem signs15805 : ∀ j, Signs p15805 (bank15805 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15806 := params 29
abbrev ray15806 := rays 29
def bank15806 : Fin 1 → Cell := oneBank p15806 ray15806
theorem signs15806 : ∀ j, Signs p15806 (bank15806 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15807 := params 30
abbrev ray15807 := rays 30
def bank15807 : Fin 1 → Cell := oneBank p15807 ray15807
theorem signs15807 : ∀ j, Signs p15807 (bank15807 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15808 := params 31
abbrev ray15808 := rays 31
def bank15808 : Fin 1 → Cell := oneBank p15808 ray15808
theorem signs15808 : ∀ j, Signs p15808 (bank15808 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15777_15808
