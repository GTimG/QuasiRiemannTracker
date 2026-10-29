/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06785_06816
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98540263793380,98539965822440,98539667829000,98539369813061,98539071774623,98538773713687,98538475630254,98538177524325,98537879395901,98537581244982,98537283071569,98536984875664,98536686657266,98536388416377,98536090152998,98535791867129,98535493558771,98535195227925,98534896874592,98534598498772,98534300100466,98534001679676,98533703236401,98533404770643,98533106282403,98532807771681,98532509238478,98532210682795,98531912104633,98531613503992,98531314880874,98531016235279,98530717567208]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6784+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6785 := params 0
abbrev ray6785 := rays 0
def bank6785 : Fin 2 → Cell := twoBank p6785 ray6785
theorem signs6785 : ∀ j, Signs p6785 (bank6785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6786 := params 1
abbrev ray6786 := rays 1
def bank6786 : Fin 2 → Cell := twoBank p6786 ray6786
theorem signs6786 : ∀ j, Signs p6786 (bank6786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6787 := params 2
abbrev ray6787 := rays 2
def bank6787 : Fin 2 → Cell := twoBank p6787 ray6787
theorem signs6787 : ∀ j, Signs p6787 (bank6787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6788 := params 3
abbrev ray6788 := rays 3
def bank6788 : Fin 2 → Cell := twoBank p6788 ray6788
theorem signs6788 : ∀ j, Signs p6788 (bank6788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6789 := params 4
abbrev ray6789 := rays 4
def bank6789 : Fin 2 → Cell := twoBank p6789 ray6789
theorem signs6789 : ∀ j, Signs p6789 (bank6789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6790 := params 5
abbrev ray6790 := rays 5
def bank6790 : Fin 2 → Cell := twoBank p6790 ray6790
theorem signs6790 : ∀ j, Signs p6790 (bank6790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6791 := params 6
abbrev ray6791 := rays 6
def bank6791 : Fin 2 → Cell := twoBank p6791 ray6791
theorem signs6791 : ∀ j, Signs p6791 (bank6791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6792 := params 7
abbrev ray6792 := rays 7
def bank6792 : Fin 2 → Cell := twoBank p6792 ray6792
theorem signs6792 : ∀ j, Signs p6792 (bank6792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6793 := params 8
abbrev ray6793 := rays 8
def bank6793 : Fin 2 → Cell := twoBank p6793 ray6793
theorem signs6793 : ∀ j, Signs p6793 (bank6793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6794 := params 9
abbrev ray6794 := rays 9
def bank6794 : Fin 2 → Cell := twoBank p6794 ray6794
theorem signs6794 : ∀ j, Signs p6794 (bank6794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6795 := params 10
abbrev ray6795 := rays 10
def bank6795 : Fin 2 → Cell := twoBank p6795 ray6795
theorem signs6795 : ∀ j, Signs p6795 (bank6795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6796 := params 11
abbrev ray6796 := rays 11
def bank6796 : Fin 2 → Cell := twoBank p6796 ray6796
theorem signs6796 : ∀ j, Signs p6796 (bank6796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6797 := params 12
abbrev ray6797 := rays 12
def bank6797 : Fin 2 → Cell := twoBank p6797 ray6797
theorem signs6797 : ∀ j, Signs p6797 (bank6797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6798 := params 13
abbrev ray6798 := rays 13
def bank6798 : Fin 2 → Cell := twoBank p6798 ray6798
theorem signs6798 : ∀ j, Signs p6798 (bank6798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6799 := params 14
abbrev ray6799 := rays 14
def bank6799 : Fin 2 → Cell := twoBank p6799 ray6799
theorem signs6799 : ∀ j, Signs p6799 (bank6799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6800 := params 15
abbrev ray6800 := rays 15
def bank6800 : Fin 2 → Cell := twoBank p6800 ray6800
theorem signs6800 : ∀ j, Signs p6800 (bank6800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6801 := params 16
abbrev ray6801 := rays 16
def bank6801 : Fin 2 → Cell := twoBank p6801 ray6801
theorem signs6801 : ∀ j, Signs p6801 (bank6801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6802 := params 17
abbrev ray6802 := rays 17
def bank6802 : Fin 2 → Cell := twoBank p6802 ray6802
theorem signs6802 : ∀ j, Signs p6802 (bank6802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6803 := params 18
abbrev ray6803 := rays 18
def bank6803 : Fin 2 → Cell := twoBank p6803 ray6803
theorem signs6803 : ∀ j, Signs p6803 (bank6803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6804 := params 19
abbrev ray6804 := rays 19
def bank6804 : Fin 2 → Cell := twoBank p6804 ray6804
theorem signs6804 : ∀ j, Signs p6804 (bank6804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6805 := params 20
abbrev ray6805 := rays 20
def bank6805 : Fin 2 → Cell := twoBank p6805 ray6805
theorem signs6805 : ∀ j, Signs p6805 (bank6805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6806 := params 21
abbrev ray6806 := rays 21
def bank6806 : Fin 2 → Cell := twoBank p6806 ray6806
theorem signs6806 : ∀ j, Signs p6806 (bank6806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6807 := params 22
abbrev ray6807 := rays 22
def bank6807 : Fin 2 → Cell := twoBank p6807 ray6807
theorem signs6807 : ∀ j, Signs p6807 (bank6807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6808 := params 23
abbrev ray6808 := rays 23
def bank6808 : Fin 2 → Cell := twoBank p6808 ray6808
theorem signs6808 : ∀ j, Signs p6808 (bank6808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6809 := params 24
abbrev ray6809 := rays 24
def bank6809 : Fin 2 → Cell := twoBank p6809 ray6809
theorem signs6809 : ∀ j, Signs p6809 (bank6809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6810 := params 25
abbrev ray6810 := rays 25
def bank6810 : Fin 2 → Cell := twoBank p6810 ray6810
theorem signs6810 : ∀ j, Signs p6810 (bank6810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6811 := params 26
abbrev ray6811 := rays 26
def bank6811 : Fin 2 → Cell := twoBank p6811 ray6811
theorem signs6811 : ∀ j, Signs p6811 (bank6811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6812 := params 27
abbrev ray6812 := rays 27
def bank6812 : Fin 2 → Cell := twoBank p6812 ray6812
theorem signs6812 : ∀ j, Signs p6812 (bank6812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6813 := params 28
abbrev ray6813 := rays 28
def bank6813 : Fin 2 → Cell := twoBank p6813 ray6813
theorem signs6813 : ∀ j, Signs p6813 (bank6813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6814 := params 29
abbrev ray6814 := rays 29
def bank6814 : Fin 2 → Cell := twoBank p6814 ray6814
theorem signs6814 : ∀ j, Signs p6814 (bank6814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6815 := params 30
abbrev ray6815 := rays 30
def bank6815 : Fin 2 → Cell := twoBank p6815 ray6815
theorem signs6815 : ∀ j, Signs p6815 (bank6815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6816 := params 31
abbrev ray6816 := rays 31
def bank6816 : Fin 2 → Cell := twoBank p6816 ray6816
theorem signs6816 : ∀ j, Signs p6816 (bank6816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06785_06816
