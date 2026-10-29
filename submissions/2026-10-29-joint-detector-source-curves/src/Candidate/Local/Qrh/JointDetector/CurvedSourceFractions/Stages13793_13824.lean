/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13793_13824
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95939038886040,95938601042726,95938163183158,95937725307336,95937287415261,95936849506933,95936411582352,95935973641518,95935535684431,95935097711092,95934659721500,95934221715656,95933783693560,95933345655213,95932907600614,95932469529764,95932031442663,95931593339311,95931155219708,95930717083855,95930278931752,95929840763399,95929402578796,95928964377943,95928526160841,95928087927489,95927649677888,95927211412039,95926773129941,95926334831594,95925896516999,95925458186156,95925019839065]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13792+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13793 := params 0
abbrev ray13793 := rays 0
def bank13793 : Fin 1 → Cell := oneBank p13793 ray13793
theorem signs13793 : ∀ j, Signs p13793 (bank13793 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13794 := params 1
abbrev ray13794 := rays 1
def bank13794 : Fin 1 → Cell := oneBank p13794 ray13794
theorem signs13794 : ∀ j, Signs p13794 (bank13794 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13795 := params 2
abbrev ray13795 := rays 2
def bank13795 : Fin 1 → Cell := oneBank p13795 ray13795
theorem signs13795 : ∀ j, Signs p13795 (bank13795 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13796 := params 3
abbrev ray13796 := rays 3
def bank13796 : Fin 1 → Cell := oneBank p13796 ray13796
theorem signs13796 : ∀ j, Signs p13796 (bank13796 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13797 := params 4
abbrev ray13797 := rays 4
def bank13797 : Fin 1 → Cell := oneBank p13797 ray13797
theorem signs13797 : ∀ j, Signs p13797 (bank13797 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13798 := params 5
abbrev ray13798 := rays 5
def bank13798 : Fin 1 → Cell := oneBank p13798 ray13798
theorem signs13798 : ∀ j, Signs p13798 (bank13798 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13799 := params 6
abbrev ray13799 := rays 6
def bank13799 : Fin 1 → Cell := oneBank p13799 ray13799
theorem signs13799 : ∀ j, Signs p13799 (bank13799 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13800 := params 7
abbrev ray13800 := rays 7
def bank13800 : Fin 1 → Cell := oneBank p13800 ray13800
theorem signs13800 : ∀ j, Signs p13800 (bank13800 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13801 := params 8
abbrev ray13801 := rays 8
def bank13801 : Fin 1 → Cell := oneBank p13801 ray13801
theorem signs13801 : ∀ j, Signs p13801 (bank13801 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13802 := params 9
abbrev ray13802 := rays 9
def bank13802 : Fin 1 → Cell := oneBank p13802 ray13802
theorem signs13802 : ∀ j, Signs p13802 (bank13802 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13803 := params 10
abbrev ray13803 := rays 10
def bank13803 : Fin 1 → Cell := oneBank p13803 ray13803
theorem signs13803 : ∀ j, Signs p13803 (bank13803 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13804 := params 11
abbrev ray13804 := rays 11
def bank13804 : Fin 1 → Cell := oneBank p13804 ray13804
theorem signs13804 : ∀ j, Signs p13804 (bank13804 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13805 := params 12
abbrev ray13805 := rays 12
def bank13805 : Fin 1 → Cell := oneBank p13805 ray13805
theorem signs13805 : ∀ j, Signs p13805 (bank13805 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13806 := params 13
abbrev ray13806 := rays 13
def bank13806 : Fin 1 → Cell := oneBank p13806 ray13806
theorem signs13806 : ∀ j, Signs p13806 (bank13806 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13807 := params 14
abbrev ray13807 := rays 14
def bank13807 : Fin 1 → Cell := oneBank p13807 ray13807
theorem signs13807 : ∀ j, Signs p13807 (bank13807 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13808 := params 15
abbrev ray13808 := rays 15
def bank13808 : Fin 1 → Cell := oneBank p13808 ray13808
theorem signs13808 : ∀ j, Signs p13808 (bank13808 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13809 := params 16
abbrev ray13809 := rays 16
def bank13809 : Fin 1 → Cell := oneBank p13809 ray13809
theorem signs13809 : ∀ j, Signs p13809 (bank13809 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13810 := params 17
abbrev ray13810 := rays 17
def bank13810 : Fin 1 → Cell := oneBank p13810 ray13810
theorem signs13810 : ∀ j, Signs p13810 (bank13810 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13811 := params 18
abbrev ray13811 := rays 18
def bank13811 : Fin 1 → Cell := oneBank p13811 ray13811
theorem signs13811 : ∀ j, Signs p13811 (bank13811 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13812 := params 19
abbrev ray13812 := rays 19
def bank13812 : Fin 1 → Cell := oneBank p13812 ray13812
theorem signs13812 : ∀ j, Signs p13812 (bank13812 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13813 := params 20
abbrev ray13813 := rays 20
def bank13813 : Fin 1 → Cell := oneBank p13813 ray13813
theorem signs13813 : ∀ j, Signs p13813 (bank13813 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13814 := params 21
abbrev ray13814 := rays 21
def bank13814 : Fin 1 → Cell := oneBank p13814 ray13814
theorem signs13814 : ∀ j, Signs p13814 (bank13814 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13815 := params 22
abbrev ray13815 := rays 22
def bank13815 : Fin 1 → Cell := oneBank p13815 ray13815
theorem signs13815 : ∀ j, Signs p13815 (bank13815 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13816 := params 23
abbrev ray13816 := rays 23
def bank13816 : Fin 1 → Cell := oneBank p13816 ray13816
theorem signs13816 : ∀ j, Signs p13816 (bank13816 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13817 := params 24
abbrev ray13817 := rays 24
def bank13817 : Fin 1 → Cell := oneBank p13817 ray13817
theorem signs13817 : ∀ j, Signs p13817 (bank13817 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13818 := params 25
abbrev ray13818 := rays 25
def bank13818 : Fin 1 → Cell := oneBank p13818 ray13818
theorem signs13818 : ∀ j, Signs p13818 (bank13818 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13819 := params 26
abbrev ray13819 := rays 26
def bank13819 : Fin 1 → Cell := oneBank p13819 ray13819
theorem signs13819 : ∀ j, Signs p13819 (bank13819 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13820 := params 27
abbrev ray13820 := rays 27
def bank13820 : Fin 1 → Cell := oneBank p13820 ray13820
theorem signs13820 : ∀ j, Signs p13820 (bank13820 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13821 := params 28
abbrev ray13821 := rays 28
def bank13821 : Fin 1 → Cell := oneBank p13821 ray13821
theorem signs13821 : ∀ j, Signs p13821 (bank13821 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13822 := params 29
abbrev ray13822 := rays 29
def bank13822 : Fin 1 → Cell := oneBank p13822 ray13822
theorem signs13822 : ∀ j, Signs p13822 (bank13822 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13823 := params 30
abbrev ray13823 := rays 30
def bank13823 : Fin 1 → Cell := oneBank p13823 ray13823
theorem signs13823 : ∀ j, Signs p13823 (bank13823 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13824 := params 31
abbrev ray13824 := rays 31
def bank13824 : Fin 1 → Cell := oneBank p13824 ray13824
theorem signs13824 : ∀ j, Signs p13824 (bank13824 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13793_13824
