/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12769_12800
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96378820346203,96378399316651,96377978268059,96377557200428,96377136113757,96376715008047,96376293883299,96375872739513,96375451576689,96375030394828,96374609193930,96374187973995,96373766735024,96373345477017,96372924199975,96372502903898,96372081588787,96371660254641,96371238901462,96370817529249,96370396135471,96369974725198,96369553298431,96369131855171,96368710395417,96368288919170,96367867426431,96367445917199,96367024391475,96366602849259,96366181290551,96365759715352,96365338123661]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12768+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12769 := params 0
abbrev ray12769 := rays 0
def bank12769 : Fin 2 → Cell := twoBank p12769 ray12769
theorem signs12769 : ∀ j, Signs p12769 (bank12769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12770 := params 1
abbrev ray12770 := rays 1
def bank12770 : Fin 2 → Cell := twoBank p12770 ray12770
theorem signs12770 : ∀ j, Signs p12770 (bank12770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12771 := params 2
abbrev ray12771 := rays 2
def bank12771 : Fin 2 → Cell := twoBank p12771 ray12771
theorem signs12771 : ∀ j, Signs p12771 (bank12771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12772 := params 3
abbrev ray12772 := rays 3
def bank12772 : Fin 2 → Cell := twoBank p12772 ray12772
theorem signs12772 : ∀ j, Signs p12772 (bank12772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12773 := params 4
abbrev ray12773 := rays 4
def bank12773 : Fin 2 → Cell := twoBank p12773 ray12773
theorem signs12773 : ∀ j, Signs p12773 (bank12773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12774 := params 5
abbrev ray12774 := rays 5
def bank12774 : Fin 2 → Cell := twoBank p12774 ray12774
theorem signs12774 : ∀ j, Signs p12774 (bank12774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12775 := params 6
abbrev ray12775 := rays 6
def bank12775 : Fin 2 → Cell := twoBank p12775 ray12775
theorem signs12775 : ∀ j, Signs p12775 (bank12775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12776 := params 7
abbrev ray12776 := rays 7
def bank12776 : Fin 2 → Cell := twoBank p12776 ray12776
theorem signs12776 : ∀ j, Signs p12776 (bank12776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12777 := params 8
abbrev ray12777 := rays 8
def bank12777 : Fin 2 → Cell := twoBank p12777 ray12777
theorem signs12777 : ∀ j, Signs p12777 (bank12777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12778 := params 9
abbrev ray12778 := rays 9
def bank12778 : Fin 2 → Cell := twoBank p12778 ray12778
theorem signs12778 : ∀ j, Signs p12778 (bank12778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12779 := params 10
abbrev ray12779 := rays 10
def bank12779 : Fin 2 → Cell := twoBank p12779 ray12779
theorem signs12779 : ∀ j, Signs p12779 (bank12779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12780 := params 11
abbrev ray12780 := rays 11
def bank12780 : Fin 2 → Cell := twoBank p12780 ray12780
theorem signs12780 : ∀ j, Signs p12780 (bank12780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12781 := params 12
abbrev ray12781 := rays 12
def bank12781 : Fin 2 → Cell := twoBank p12781 ray12781
theorem signs12781 : ∀ j, Signs p12781 (bank12781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12782 := params 13
abbrev ray12782 := rays 13
def bank12782 : Fin 2 → Cell := twoBank p12782 ray12782
theorem signs12782 : ∀ j, Signs p12782 (bank12782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12783 := params 14
abbrev ray12783 := rays 14
def bank12783 : Fin 2 → Cell := twoBank p12783 ray12783
theorem signs12783 : ∀ j, Signs p12783 (bank12783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12784 := params 15
abbrev ray12784 := rays 15
def bank12784 : Fin 2 → Cell := twoBank p12784 ray12784
theorem signs12784 : ∀ j, Signs p12784 (bank12784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12785 := params 16
abbrev ray12785 := rays 16
def bank12785 : Fin 2 → Cell := twoBank p12785 ray12785
theorem signs12785 : ∀ j, Signs p12785 (bank12785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12786 := params 17
abbrev ray12786 := rays 17
def bank12786 : Fin 2 → Cell := twoBank p12786 ray12786
theorem signs12786 : ∀ j, Signs p12786 (bank12786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12787 := params 18
abbrev ray12787 := rays 18
def bank12787 : Fin 2 → Cell := twoBank p12787 ray12787
theorem signs12787 : ∀ j, Signs p12787 (bank12787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12788 := params 19
abbrev ray12788 := rays 19
def bank12788 : Fin 1 → Cell := oneBank p12788 ray12788
theorem signs12788 : ∀ j, Signs p12788 (bank12788 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12789 := params 20
abbrev ray12789 := rays 20
def bank12789 : Fin 1 → Cell := oneBank p12789 ray12789
theorem signs12789 : ∀ j, Signs p12789 (bank12789 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12790 := params 21
abbrev ray12790 := rays 21
def bank12790 : Fin 1 → Cell := oneBank p12790 ray12790
theorem signs12790 : ∀ j, Signs p12790 (bank12790 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12791 := params 22
abbrev ray12791 := rays 22
def bank12791 : Fin 1 → Cell := oneBank p12791 ray12791
theorem signs12791 : ∀ j, Signs p12791 (bank12791 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12792 := params 23
abbrev ray12792 := rays 23
def bank12792 : Fin 1 → Cell := oneBank p12792 ray12792
theorem signs12792 : ∀ j, Signs p12792 (bank12792 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12793 := params 24
abbrev ray12793 := rays 24
def bank12793 : Fin 1 → Cell := oneBank p12793 ray12793
theorem signs12793 : ∀ j, Signs p12793 (bank12793 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12794 := params 25
abbrev ray12794 := rays 25
def bank12794 : Fin 1 → Cell := oneBank p12794 ray12794
theorem signs12794 : ∀ j, Signs p12794 (bank12794 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12795 := params 26
abbrev ray12795 := rays 26
def bank12795 : Fin 1 → Cell := oneBank p12795 ray12795
theorem signs12795 : ∀ j, Signs p12795 (bank12795 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12796 := params 27
abbrev ray12796 := rays 27
def bank12796 : Fin 1 → Cell := oneBank p12796 ray12796
theorem signs12796 : ∀ j, Signs p12796 (bank12796 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12797 := params 28
abbrev ray12797 := rays 28
def bank12797 : Fin 1 → Cell := oneBank p12797 ray12797
theorem signs12797 : ∀ j, Signs p12797 (bank12797 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12798 := params 29
abbrev ray12798 := rays 29
def bank12798 : Fin 1 → Cell := oneBank p12798 ray12798
theorem signs12798 : ∀ j, Signs p12798 (bank12798 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12799 := params 30
abbrev ray12799 := rays 30
def bank12799 : Fin 1 → Cell := oneBank p12799 ray12799
theorem signs12799 : ∀ j, Signs p12799 (bank12799 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12800 := params 31
abbrev ray12800 := rays 31
def bank12800 : Fin 1 → Cell := oneBank p12800 ray12800
theorem signs12800 : ∀ j, Signs p12800 (bank12800 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12769_12800
