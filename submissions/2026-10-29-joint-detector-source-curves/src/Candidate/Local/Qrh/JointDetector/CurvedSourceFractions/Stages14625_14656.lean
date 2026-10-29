/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14625_14656
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95569152071611,95568700767329,95568249446934,95567798110427,95567346757807,95566895389075,95566444004231,95565992603275,95565541186207,95565089753027,95564638303736,95564186838333,95563735356819,95563283859194,95562832345458,95562380815611,95561929269653,95561477707585,95561026129406,95560574535117,95560122924718,95559671298209,95559219655590,95558767996861,95558316322022,95557864631074,95557412924016,95556961200849,95556509461573,95556057706188,95555605934694,95555154147091,95554702343380]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14624+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14625 := params 0
abbrev ray14625 := rays 0
def bank14625 : Fin 1 → Cell := oneBank p14625 ray14625
theorem signs14625 : ∀ j, Signs p14625 (bank14625 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14626 := params 1
abbrev ray14626 := rays 1
def bank14626 : Fin 1 → Cell := oneBank p14626 ray14626
theorem signs14626 : ∀ j, Signs p14626 (bank14626 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14627 := params 2
abbrev ray14627 := rays 2
def bank14627 : Fin 1 → Cell := oneBank p14627 ray14627
theorem signs14627 : ∀ j, Signs p14627 (bank14627 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14628 := params 3
abbrev ray14628 := rays 3
def bank14628 : Fin 1 → Cell := oneBank p14628 ray14628
theorem signs14628 : ∀ j, Signs p14628 (bank14628 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14629 := params 4
abbrev ray14629 := rays 4
def bank14629 : Fin 1 → Cell := oneBank p14629 ray14629
theorem signs14629 : ∀ j, Signs p14629 (bank14629 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14630 := params 5
abbrev ray14630 := rays 5
def bank14630 : Fin 1 → Cell := oneBank p14630 ray14630
theorem signs14630 : ∀ j, Signs p14630 (bank14630 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14631 := params 6
abbrev ray14631 := rays 6
def bank14631 : Fin 1 → Cell := oneBank p14631 ray14631
theorem signs14631 : ∀ j, Signs p14631 (bank14631 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14632 := params 7
abbrev ray14632 := rays 7
def bank14632 : Fin 1 → Cell := oneBank p14632 ray14632
theorem signs14632 : ∀ j, Signs p14632 (bank14632 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14633 := params 8
abbrev ray14633 := rays 8
def bank14633 : Fin 1 → Cell := oneBank p14633 ray14633
theorem signs14633 : ∀ j, Signs p14633 (bank14633 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14634 := params 9
abbrev ray14634 := rays 9
def bank14634 : Fin 1 → Cell := oneBank p14634 ray14634
theorem signs14634 : ∀ j, Signs p14634 (bank14634 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14635 := params 10
abbrev ray14635 := rays 10
def bank14635 : Fin 1 → Cell := oneBank p14635 ray14635
theorem signs14635 : ∀ j, Signs p14635 (bank14635 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14636 := params 11
abbrev ray14636 := rays 11
def bank14636 : Fin 1 → Cell := oneBank p14636 ray14636
theorem signs14636 : ∀ j, Signs p14636 (bank14636 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14637 := params 12
abbrev ray14637 := rays 12
def bank14637 : Fin 1 → Cell := oneBank p14637 ray14637
theorem signs14637 : ∀ j, Signs p14637 (bank14637 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14638 := params 13
abbrev ray14638 := rays 13
def bank14638 : Fin 1 → Cell := oneBank p14638 ray14638
theorem signs14638 : ∀ j, Signs p14638 (bank14638 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14639 := params 14
abbrev ray14639 := rays 14
def bank14639 : Fin 1 → Cell := oneBank p14639 ray14639
theorem signs14639 : ∀ j, Signs p14639 (bank14639 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14640 := params 15
abbrev ray14640 := rays 15
def bank14640 : Fin 1 → Cell := oneBank p14640 ray14640
theorem signs14640 : ∀ j, Signs p14640 (bank14640 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14641 := params 16
abbrev ray14641 := rays 16
def bank14641 : Fin 1 → Cell := oneBank p14641 ray14641
theorem signs14641 : ∀ j, Signs p14641 (bank14641 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14642 := params 17
abbrev ray14642 := rays 17
def bank14642 : Fin 1 → Cell := oneBank p14642 ray14642
theorem signs14642 : ∀ j, Signs p14642 (bank14642 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14643 := params 18
abbrev ray14643 := rays 18
def bank14643 : Fin 1 → Cell := oneBank p14643 ray14643
theorem signs14643 : ∀ j, Signs p14643 (bank14643 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14644 := params 19
abbrev ray14644 := rays 19
def bank14644 : Fin 1 → Cell := oneBank p14644 ray14644
theorem signs14644 : ∀ j, Signs p14644 (bank14644 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14645 := params 20
abbrev ray14645 := rays 20
def bank14645 : Fin 1 → Cell := oneBank p14645 ray14645
theorem signs14645 : ∀ j, Signs p14645 (bank14645 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14646 := params 21
abbrev ray14646 := rays 21
def bank14646 : Fin 1 → Cell := oneBank p14646 ray14646
theorem signs14646 : ∀ j, Signs p14646 (bank14646 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14647 := params 22
abbrev ray14647 := rays 22
def bank14647 : Fin 1 → Cell := oneBank p14647 ray14647
theorem signs14647 : ∀ j, Signs p14647 (bank14647 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14648 := params 23
abbrev ray14648 := rays 23
def bank14648 : Fin 1 → Cell := oneBank p14648 ray14648
theorem signs14648 : ∀ j, Signs p14648 (bank14648 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14649 := params 24
abbrev ray14649 := rays 24
def bank14649 : Fin 1 → Cell := oneBank p14649 ray14649
theorem signs14649 : ∀ j, Signs p14649 (bank14649 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14650 := params 25
abbrev ray14650 := rays 25
def bank14650 : Fin 1 → Cell := oneBank p14650 ray14650
theorem signs14650 : ∀ j, Signs p14650 (bank14650 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14651 := params 26
abbrev ray14651 := rays 26
def bank14651 : Fin 1 → Cell := oneBank p14651 ray14651
theorem signs14651 : ∀ j, Signs p14651 (bank14651 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14652 := params 27
abbrev ray14652 := rays 27
def bank14652 : Fin 1 → Cell := oneBank p14652 ray14652
theorem signs14652 : ∀ j, Signs p14652 (bank14652 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14653 := params 28
abbrev ray14653 := rays 28
def bank14653 : Fin 1 → Cell := oneBank p14653 ray14653
theorem signs14653 : ∀ j, Signs p14653 (bank14653 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14654 := params 29
abbrev ray14654 := rays 29
def bank14654 : Fin 1 → Cell := oneBank p14654 ray14654
theorem signs14654 : ∀ j, Signs p14654 (bank14654 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14655 := params 30
abbrev ray14655 := rays 30
def bank14655 : Fin 1 → Cell := oneBank p14655 ray14655
theorem signs14655 : ∀ j, Signs p14655 (bank14655 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14656 := params 31
abbrev ray14656 := rays 31
def bank14656 : Fin 1 → Cell := oneBank p14656 ray14656
theorem signs14656 : ∀ j, Signs p14656 (bank14656 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14625_14656
