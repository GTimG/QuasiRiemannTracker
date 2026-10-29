/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16705_16736
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94595750882072,94595266251904,94594781605750,94594296943611,94593812265487,94593327571377,94592842861282,94592358135202,94591873393136,94591388635085,94590903861048,94590419071026,94589934265018,94589449443025,94588964605046,94588479751082,94587994881132,94587509995197,94587025093276,94586540175370,94586055241478,94585570291600,94585085325737,94584600343888,94584115346053,94583630332233,94583145302427,94582660256635,94582175194857,94581690117093,94581205023344,94580719913609,94580234787888]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16704+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16705 := params 0
abbrev ray16705 := rays 0
def bank16705 : Fin 1 → Cell := oneBank p16705 ray16705
theorem signs16705 : ∀ j, Signs p16705 (bank16705 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16706 := params 1
abbrev ray16706 := rays 1
def bank16706 : Fin 1 → Cell := oneBank p16706 ray16706
theorem signs16706 : ∀ j, Signs p16706 (bank16706 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16707 := params 2
abbrev ray16707 := rays 2
def bank16707 : Fin 1 → Cell := oneBank p16707 ray16707
theorem signs16707 : ∀ j, Signs p16707 (bank16707 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16708 := params 3
abbrev ray16708 := rays 3
def bank16708 : Fin 1 → Cell := oneBank p16708 ray16708
theorem signs16708 : ∀ j, Signs p16708 (bank16708 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16709 := params 4
abbrev ray16709 := rays 4
def bank16709 : Fin 1 → Cell := oneBank p16709 ray16709
theorem signs16709 : ∀ j, Signs p16709 (bank16709 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16710 := params 5
abbrev ray16710 := rays 5
def bank16710 : Fin 1 → Cell := oneBank p16710 ray16710
theorem signs16710 : ∀ j, Signs p16710 (bank16710 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16711 := params 6
abbrev ray16711 := rays 6
def bank16711 : Fin 1 → Cell := oneBank p16711 ray16711
theorem signs16711 : ∀ j, Signs p16711 (bank16711 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16712 := params 7
abbrev ray16712 := rays 7
def bank16712 : Fin 1 → Cell := oneBank p16712 ray16712
theorem signs16712 : ∀ j, Signs p16712 (bank16712 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16713 := params 8
abbrev ray16713 := rays 8
def bank16713 : Fin 1 → Cell := oneBank p16713 ray16713
theorem signs16713 : ∀ j, Signs p16713 (bank16713 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16714 := params 9
abbrev ray16714 := rays 9
def bank16714 : Fin 1 → Cell := oneBank p16714 ray16714
theorem signs16714 : ∀ j, Signs p16714 (bank16714 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16715 := params 10
abbrev ray16715 := rays 10
def bank16715 : Fin 1 → Cell := oneBank p16715 ray16715
theorem signs16715 : ∀ j, Signs p16715 (bank16715 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16716 := params 11
abbrev ray16716 := rays 11
def bank16716 : Fin 1 → Cell := oneBank p16716 ray16716
theorem signs16716 : ∀ j, Signs p16716 (bank16716 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16717 := params 12
abbrev ray16717 := rays 12
def bank16717 : Fin 1 → Cell := oneBank p16717 ray16717
theorem signs16717 : ∀ j, Signs p16717 (bank16717 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16718 := params 13
abbrev ray16718 := rays 13
def bank16718 : Fin 1 → Cell := oneBank p16718 ray16718
theorem signs16718 : ∀ j, Signs p16718 (bank16718 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16719 := params 14
abbrev ray16719 := rays 14
def bank16719 : Fin 1 → Cell := oneBank p16719 ray16719
theorem signs16719 : ∀ j, Signs p16719 (bank16719 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16720 := params 15
abbrev ray16720 := rays 15
def bank16720 : Fin 1 → Cell := oneBank p16720 ray16720
theorem signs16720 : ∀ j, Signs p16720 (bank16720 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16721 := params 16
abbrev ray16721 := rays 16
def bank16721 : Fin 1 → Cell := oneBank p16721 ray16721
theorem signs16721 : ∀ j, Signs p16721 (bank16721 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16722 := params 17
abbrev ray16722 := rays 17
def bank16722 : Fin 1 → Cell := oneBank p16722 ray16722
theorem signs16722 : ∀ j, Signs p16722 (bank16722 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16723 := params 18
abbrev ray16723 := rays 18
def bank16723 : Fin 1 → Cell := oneBank p16723 ray16723
theorem signs16723 : ∀ j, Signs p16723 (bank16723 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16724 := params 19
abbrev ray16724 := rays 19
def bank16724 : Fin 1 → Cell := oneBank p16724 ray16724
theorem signs16724 : ∀ j, Signs p16724 (bank16724 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16725 := params 20
abbrev ray16725 := rays 20
def bank16725 : Fin 1 → Cell := oneBank p16725 ray16725
theorem signs16725 : ∀ j, Signs p16725 (bank16725 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16726 := params 21
abbrev ray16726 := rays 21
def bank16726 : Fin 1 → Cell := oneBank p16726 ray16726
theorem signs16726 : ∀ j, Signs p16726 (bank16726 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16727 := params 22
abbrev ray16727 := rays 22
def bank16727 : Fin 1 → Cell := oneBank p16727 ray16727
theorem signs16727 : ∀ j, Signs p16727 (bank16727 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16728 := params 23
abbrev ray16728 := rays 23
def bank16728 : Fin 1 → Cell := oneBank p16728 ray16728
theorem signs16728 : ∀ j, Signs p16728 (bank16728 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16729 := params 24
abbrev ray16729 := rays 24
def bank16729 : Fin 1 → Cell := oneBank p16729 ray16729
theorem signs16729 : ∀ j, Signs p16729 (bank16729 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16730 := params 25
abbrev ray16730 := rays 25
def bank16730 : Fin 1 → Cell := oneBank p16730 ray16730
theorem signs16730 : ∀ j, Signs p16730 (bank16730 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16731 := params 26
abbrev ray16731 := rays 26
def bank16731 : Fin 1 → Cell := oneBank p16731 ray16731
theorem signs16731 : ∀ j, Signs p16731 (bank16731 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16732 := params 27
abbrev ray16732 := rays 27
def bank16732 : Fin 1 → Cell := oneBank p16732 ray16732
theorem signs16732 : ∀ j, Signs p16732 (bank16732 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16733 := params 28
abbrev ray16733 := rays 28
def bank16733 : Fin 1 → Cell := oneBank p16733 ray16733
theorem signs16733 : ∀ j, Signs p16733 (bank16733 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16734 := params 29
abbrev ray16734 := rays 29
def bank16734 : Fin 1 → Cell := oneBank p16734 ray16734
theorem signs16734 : ∀ j, Signs p16734 (bank16734 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16735 := params 30
abbrev ray16735 := rays 30
def bank16735 : Fin 1 → Cell := oneBank p16735 ray16735
theorem signs16735 : ∀ j, Signs p16735 (bank16735 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16736 := params 31
abbrev ray16736 := rays 31
def bank16736 : Fin 1 → Cell := oneBank p16736 ray16736
theorem signs16736 : ∀ j, Signs p16736 (bank16736 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16705_16736
