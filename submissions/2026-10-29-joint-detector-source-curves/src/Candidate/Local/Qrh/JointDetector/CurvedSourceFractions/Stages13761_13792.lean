/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13761_13792
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95953041288852,95952603965768,95952166626423,95951729270818,95951291898953,95950854510829,95950417106445,95949979685802,95949542248900,95949104795739,95948667326319,95948229840641,95947792338704,95947354820509,95946917286056,95946479735346,95946042168378,95945604585153,95945166985671,95944729369932,95944291737936,95943854089684,95943416425176,95942978744411,95942541047391,95942103334115,95941665604583,95941227858796,95940790096754,95940352318457,95939914523906,95939476713100,95939038886040]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13760+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13761 := params 0
abbrev ray13761 := rays 0
def bank13761 : Fin 1 → Cell := oneBank p13761 ray13761
theorem signs13761 : ∀ j, Signs p13761 (bank13761 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13762 := params 1
abbrev ray13762 := rays 1
def bank13762 : Fin 1 → Cell := oneBank p13762 ray13762
theorem signs13762 : ∀ j, Signs p13762 (bank13762 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13763 := params 2
abbrev ray13763 := rays 2
def bank13763 : Fin 1 → Cell := oneBank p13763 ray13763
theorem signs13763 : ∀ j, Signs p13763 (bank13763 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13764 := params 3
abbrev ray13764 := rays 3
def bank13764 : Fin 1 → Cell := oneBank p13764 ray13764
theorem signs13764 : ∀ j, Signs p13764 (bank13764 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13765 := params 4
abbrev ray13765 := rays 4
def bank13765 : Fin 1 → Cell := oneBank p13765 ray13765
theorem signs13765 : ∀ j, Signs p13765 (bank13765 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13766 := params 5
abbrev ray13766 := rays 5
def bank13766 : Fin 1 → Cell := oneBank p13766 ray13766
theorem signs13766 : ∀ j, Signs p13766 (bank13766 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13767 := params 6
abbrev ray13767 := rays 6
def bank13767 : Fin 1 → Cell := oneBank p13767 ray13767
theorem signs13767 : ∀ j, Signs p13767 (bank13767 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13768 := params 7
abbrev ray13768 := rays 7
def bank13768 : Fin 1 → Cell := oneBank p13768 ray13768
theorem signs13768 : ∀ j, Signs p13768 (bank13768 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13769 := params 8
abbrev ray13769 := rays 8
def bank13769 : Fin 1 → Cell := oneBank p13769 ray13769
theorem signs13769 : ∀ j, Signs p13769 (bank13769 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13770 := params 9
abbrev ray13770 := rays 9
def bank13770 : Fin 1 → Cell := oneBank p13770 ray13770
theorem signs13770 : ∀ j, Signs p13770 (bank13770 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13771 := params 10
abbrev ray13771 := rays 10
def bank13771 : Fin 1 → Cell := oneBank p13771 ray13771
theorem signs13771 : ∀ j, Signs p13771 (bank13771 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13772 := params 11
abbrev ray13772 := rays 11
def bank13772 : Fin 1 → Cell := oneBank p13772 ray13772
theorem signs13772 : ∀ j, Signs p13772 (bank13772 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13773 := params 12
abbrev ray13773 := rays 12
def bank13773 : Fin 1 → Cell := oneBank p13773 ray13773
theorem signs13773 : ∀ j, Signs p13773 (bank13773 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13774 := params 13
abbrev ray13774 := rays 13
def bank13774 : Fin 1 → Cell := oneBank p13774 ray13774
theorem signs13774 : ∀ j, Signs p13774 (bank13774 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13775 := params 14
abbrev ray13775 := rays 14
def bank13775 : Fin 1 → Cell := oneBank p13775 ray13775
theorem signs13775 : ∀ j, Signs p13775 (bank13775 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13776 := params 15
abbrev ray13776 := rays 15
def bank13776 : Fin 1 → Cell := oneBank p13776 ray13776
theorem signs13776 : ∀ j, Signs p13776 (bank13776 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13777 := params 16
abbrev ray13777 := rays 16
def bank13777 : Fin 1 → Cell := oneBank p13777 ray13777
theorem signs13777 : ∀ j, Signs p13777 (bank13777 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13778 := params 17
abbrev ray13778 := rays 17
def bank13778 : Fin 1 → Cell := oneBank p13778 ray13778
theorem signs13778 : ∀ j, Signs p13778 (bank13778 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13779 := params 18
abbrev ray13779 := rays 18
def bank13779 : Fin 1 → Cell := oneBank p13779 ray13779
theorem signs13779 : ∀ j, Signs p13779 (bank13779 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13780 := params 19
abbrev ray13780 := rays 19
def bank13780 : Fin 1 → Cell := oneBank p13780 ray13780
theorem signs13780 : ∀ j, Signs p13780 (bank13780 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13781 := params 20
abbrev ray13781 := rays 20
def bank13781 : Fin 1 → Cell := oneBank p13781 ray13781
theorem signs13781 : ∀ j, Signs p13781 (bank13781 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13782 := params 21
abbrev ray13782 := rays 21
def bank13782 : Fin 1 → Cell := oneBank p13782 ray13782
theorem signs13782 : ∀ j, Signs p13782 (bank13782 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13783 := params 22
abbrev ray13783 := rays 22
def bank13783 : Fin 1 → Cell := oneBank p13783 ray13783
theorem signs13783 : ∀ j, Signs p13783 (bank13783 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13784 := params 23
abbrev ray13784 := rays 23
def bank13784 : Fin 1 → Cell := oneBank p13784 ray13784
theorem signs13784 : ∀ j, Signs p13784 (bank13784 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13785 := params 24
abbrev ray13785 := rays 24
def bank13785 : Fin 1 → Cell := oneBank p13785 ray13785
theorem signs13785 : ∀ j, Signs p13785 (bank13785 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13786 := params 25
abbrev ray13786 := rays 25
def bank13786 : Fin 1 → Cell := oneBank p13786 ray13786
theorem signs13786 : ∀ j, Signs p13786 (bank13786 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13787 := params 26
abbrev ray13787 := rays 26
def bank13787 : Fin 1 → Cell := oneBank p13787 ray13787
theorem signs13787 : ∀ j, Signs p13787 (bank13787 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13788 := params 27
abbrev ray13788 := rays 27
def bank13788 : Fin 1 → Cell := oneBank p13788 ray13788
theorem signs13788 : ∀ j, Signs p13788 (bank13788 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13789 := params 28
abbrev ray13789 := rays 28
def bank13789 : Fin 1 → Cell := oneBank p13789 ray13789
theorem signs13789 : ∀ j, Signs p13789 (bank13789 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13790 := params 29
abbrev ray13790 := rays 29
def bank13790 : Fin 1 → Cell := oneBank p13790 ray13790
theorem signs13790 : ∀ j, Signs p13790 (bank13790 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13791 := params 30
abbrev ray13791 := rays 30
def bank13791 : Fin 1 → Cell := oneBank p13791 ray13791
theorem signs13791 : ∀ j, Signs p13791 (bank13791 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13792 := params 31
abbrev ray13792 := rays 31
def bank13792 : Fin 1 → Cell := oneBank p13792 ray13792
theorem signs13792 : ∀ j, Signs p13792 (bank13792 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13761_13792
