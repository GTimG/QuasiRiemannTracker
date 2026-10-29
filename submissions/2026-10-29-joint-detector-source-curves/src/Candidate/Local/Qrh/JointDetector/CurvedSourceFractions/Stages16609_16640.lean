/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16609_16640
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94642200952997,94641717857349,94641234745717,94640751618101,94640268474501,94639785314917,94639302139349,94638818947797,94638335740261,94637852516741,94637369277237,94636886021749,94636402750277,94635919462820,94635436159379,94634952839954,94634469504545,94633986153152,94633502785775,94633019402414,94632536003068,94632052587738,94631569156424,94631085709126,94630602245843,94630118766576,94629635271325,94629151760090,94628668232870,94628184689666,94627701130478,94627217555305,94626733964148]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16608+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16609 := params 0
abbrev ray16609 := rays 0
def bank16609 : Fin 1 → Cell := oneBank p16609 ray16609
theorem signs16609 : ∀ j, Signs p16609 (bank16609 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16610 := params 1
abbrev ray16610 := rays 1
def bank16610 : Fin 1 → Cell := oneBank p16610 ray16610
theorem signs16610 : ∀ j, Signs p16610 (bank16610 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16611 := params 2
abbrev ray16611 := rays 2
def bank16611 : Fin 1 → Cell := oneBank p16611 ray16611
theorem signs16611 : ∀ j, Signs p16611 (bank16611 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16612 := params 3
abbrev ray16612 := rays 3
def bank16612 : Fin 1 → Cell := oneBank p16612 ray16612
theorem signs16612 : ∀ j, Signs p16612 (bank16612 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16613 := params 4
abbrev ray16613 := rays 4
def bank16613 : Fin 1 → Cell := oneBank p16613 ray16613
theorem signs16613 : ∀ j, Signs p16613 (bank16613 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16614 := params 5
abbrev ray16614 := rays 5
def bank16614 : Fin 1 → Cell := oneBank p16614 ray16614
theorem signs16614 : ∀ j, Signs p16614 (bank16614 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16615 := params 6
abbrev ray16615 := rays 6
def bank16615 : Fin 1 → Cell := oneBank p16615 ray16615
theorem signs16615 : ∀ j, Signs p16615 (bank16615 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16616 := params 7
abbrev ray16616 := rays 7
def bank16616 : Fin 1 → Cell := oneBank p16616 ray16616
theorem signs16616 : ∀ j, Signs p16616 (bank16616 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16617 := params 8
abbrev ray16617 := rays 8
def bank16617 : Fin 1 → Cell := oneBank p16617 ray16617
theorem signs16617 : ∀ j, Signs p16617 (bank16617 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16618 := params 9
abbrev ray16618 := rays 9
def bank16618 : Fin 1 → Cell := oneBank p16618 ray16618
theorem signs16618 : ∀ j, Signs p16618 (bank16618 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16619 := params 10
abbrev ray16619 := rays 10
def bank16619 : Fin 1 → Cell := oneBank p16619 ray16619
theorem signs16619 : ∀ j, Signs p16619 (bank16619 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16620 := params 11
abbrev ray16620 := rays 11
def bank16620 : Fin 1 → Cell := oneBank p16620 ray16620
theorem signs16620 : ∀ j, Signs p16620 (bank16620 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16621 := params 12
abbrev ray16621 := rays 12
def bank16621 : Fin 1 → Cell := oneBank p16621 ray16621
theorem signs16621 : ∀ j, Signs p16621 (bank16621 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16622 := params 13
abbrev ray16622 := rays 13
def bank16622 : Fin 1 → Cell := oneBank p16622 ray16622
theorem signs16622 : ∀ j, Signs p16622 (bank16622 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16623 := params 14
abbrev ray16623 := rays 14
def bank16623 : Fin 1 → Cell := oneBank p16623 ray16623
theorem signs16623 : ∀ j, Signs p16623 (bank16623 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16624 := params 15
abbrev ray16624 := rays 15
def bank16624 : Fin 1 → Cell := oneBank p16624 ray16624
theorem signs16624 : ∀ j, Signs p16624 (bank16624 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16625 := params 16
abbrev ray16625 := rays 16
def bank16625 : Fin 1 → Cell := oneBank p16625 ray16625
theorem signs16625 : ∀ j, Signs p16625 (bank16625 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16626 := params 17
abbrev ray16626 := rays 17
def bank16626 : Fin 1 → Cell := oneBank p16626 ray16626
theorem signs16626 : ∀ j, Signs p16626 (bank16626 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16627 := params 18
abbrev ray16627 := rays 18
def bank16627 : Fin 1 → Cell := oneBank p16627 ray16627
theorem signs16627 : ∀ j, Signs p16627 (bank16627 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16628 := params 19
abbrev ray16628 := rays 19
def bank16628 : Fin 1 → Cell := oneBank p16628 ray16628
theorem signs16628 : ∀ j, Signs p16628 (bank16628 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16629 := params 20
abbrev ray16629 := rays 20
def bank16629 : Fin 1 → Cell := oneBank p16629 ray16629
theorem signs16629 : ∀ j, Signs p16629 (bank16629 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16630 := params 21
abbrev ray16630 := rays 21
def bank16630 : Fin 1 → Cell := oneBank p16630 ray16630
theorem signs16630 : ∀ j, Signs p16630 (bank16630 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16631 := params 22
abbrev ray16631 := rays 22
def bank16631 : Fin 1 → Cell := oneBank p16631 ray16631
theorem signs16631 : ∀ j, Signs p16631 (bank16631 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16632 := params 23
abbrev ray16632 := rays 23
def bank16632 : Fin 1 → Cell := oneBank p16632 ray16632
theorem signs16632 : ∀ j, Signs p16632 (bank16632 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16633 := params 24
abbrev ray16633 := rays 24
def bank16633 : Fin 1 → Cell := oneBank p16633 ray16633
theorem signs16633 : ∀ j, Signs p16633 (bank16633 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16634 := params 25
abbrev ray16634 := rays 25
def bank16634 : Fin 1 → Cell := oneBank p16634 ray16634
theorem signs16634 : ∀ j, Signs p16634 (bank16634 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16635 := params 26
abbrev ray16635 := rays 26
def bank16635 : Fin 1 → Cell := oneBank p16635 ray16635
theorem signs16635 : ∀ j, Signs p16635 (bank16635 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16636 := params 27
abbrev ray16636 := rays 27
def bank16636 : Fin 1 → Cell := oneBank p16636 ray16636
theorem signs16636 : ∀ j, Signs p16636 (bank16636 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16637 := params 28
abbrev ray16637 := rays 28
def bank16637 : Fin 1 → Cell := oneBank p16637 ray16637
theorem signs16637 : ∀ j, Signs p16637 (bank16637 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16638 := params 29
abbrev ray16638 := rays 29
def bank16638 : Fin 1 → Cell := oneBank p16638 ray16638
theorem signs16638 : ∀ j, Signs p16638 (bank16638 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16639 := params 30
abbrev ray16639 := rays 30
def bank16639 : Fin 1 → Cell := oneBank p16639 ray16639
theorem signs16639 : ∀ j, Signs p16639 (bank16639 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16640 := params 31
abbrev ray16640 := rays 31
def bank16640 : Fin 1 → Cell := oneBank p16640 ray16640
theorem signs16640 : ∀ j, Signs p16640 (bank16640 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16609_16640
