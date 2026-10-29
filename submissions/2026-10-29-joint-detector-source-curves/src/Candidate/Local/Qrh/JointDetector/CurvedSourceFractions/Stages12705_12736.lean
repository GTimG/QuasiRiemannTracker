/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12705_12736
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96405726616375,96405306806198,96404886976956,96404467128649,96404047261278,96403627374843,96403207469344,96402787544782,96402367601158,96401947638471,96401527656722,96401107655912,96400687636041,96400267597109,96399847539117,96399427462065,96399007365953,96398587250782,96398167116552,96397746963264,96397326790918,96396906599514,96396486389053,96396066159535,96395645910961,96395225643331,96394805356645,96394385050904,96393964726108,96393544382257,96393124019352,96392703637394,96392283236382]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12704+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12705 := params 0
abbrev ray12705 := rays 0
def bank12705 : Fin 2 → Cell := twoBank p12705 ray12705
theorem signs12705 : ∀ j, Signs p12705 (bank12705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12706 := params 1
abbrev ray12706 := rays 1
def bank12706 : Fin 2 → Cell := twoBank p12706 ray12706
theorem signs12706 : ∀ j, Signs p12706 (bank12706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12707 := params 2
abbrev ray12707 := rays 2
def bank12707 : Fin 2 → Cell := twoBank p12707 ray12707
theorem signs12707 : ∀ j, Signs p12707 (bank12707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12708 := params 3
abbrev ray12708 := rays 3
def bank12708 : Fin 2 → Cell := twoBank p12708 ray12708
theorem signs12708 : ∀ j, Signs p12708 (bank12708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12709 := params 4
abbrev ray12709 := rays 4
def bank12709 : Fin 2 → Cell := twoBank p12709 ray12709
theorem signs12709 : ∀ j, Signs p12709 (bank12709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12710 := params 5
abbrev ray12710 := rays 5
def bank12710 : Fin 2 → Cell := twoBank p12710 ray12710
theorem signs12710 : ∀ j, Signs p12710 (bank12710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12711 := params 6
abbrev ray12711 := rays 6
def bank12711 : Fin 2 → Cell := twoBank p12711 ray12711
theorem signs12711 : ∀ j, Signs p12711 (bank12711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12712 := params 7
abbrev ray12712 := rays 7
def bank12712 : Fin 2 → Cell := twoBank p12712 ray12712
theorem signs12712 : ∀ j, Signs p12712 (bank12712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12713 := params 8
abbrev ray12713 := rays 8
def bank12713 : Fin 2 → Cell := twoBank p12713 ray12713
theorem signs12713 : ∀ j, Signs p12713 (bank12713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12714 := params 9
abbrev ray12714 := rays 9
def bank12714 : Fin 2 → Cell := twoBank p12714 ray12714
theorem signs12714 : ∀ j, Signs p12714 (bank12714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12715 := params 10
abbrev ray12715 := rays 10
def bank12715 : Fin 2 → Cell := twoBank p12715 ray12715
theorem signs12715 : ∀ j, Signs p12715 (bank12715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12716 := params 11
abbrev ray12716 := rays 11
def bank12716 : Fin 2 → Cell := twoBank p12716 ray12716
theorem signs12716 : ∀ j, Signs p12716 (bank12716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12717 := params 12
abbrev ray12717 := rays 12
def bank12717 : Fin 2 → Cell := twoBank p12717 ray12717
theorem signs12717 : ∀ j, Signs p12717 (bank12717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12718 := params 13
abbrev ray12718 := rays 13
def bank12718 : Fin 2 → Cell := twoBank p12718 ray12718
theorem signs12718 : ∀ j, Signs p12718 (bank12718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12719 := params 14
abbrev ray12719 := rays 14
def bank12719 : Fin 2 → Cell := twoBank p12719 ray12719
theorem signs12719 : ∀ j, Signs p12719 (bank12719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12720 := params 15
abbrev ray12720 := rays 15
def bank12720 : Fin 2 → Cell := twoBank p12720 ray12720
theorem signs12720 : ∀ j, Signs p12720 (bank12720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12721 := params 16
abbrev ray12721 := rays 16
def bank12721 : Fin 2 → Cell := twoBank p12721 ray12721
theorem signs12721 : ∀ j, Signs p12721 (bank12721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12722 := params 17
abbrev ray12722 := rays 17
def bank12722 : Fin 2 → Cell := twoBank p12722 ray12722
theorem signs12722 : ∀ j, Signs p12722 (bank12722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12723 := params 18
abbrev ray12723 := rays 18
def bank12723 : Fin 2 → Cell := twoBank p12723 ray12723
theorem signs12723 : ∀ j, Signs p12723 (bank12723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12724 := params 19
abbrev ray12724 := rays 19
def bank12724 : Fin 2 → Cell := twoBank p12724 ray12724
theorem signs12724 : ∀ j, Signs p12724 (bank12724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12725 := params 20
abbrev ray12725 := rays 20
def bank12725 : Fin 2 → Cell := twoBank p12725 ray12725
theorem signs12725 : ∀ j, Signs p12725 (bank12725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12726 := params 21
abbrev ray12726 := rays 21
def bank12726 : Fin 2 → Cell := twoBank p12726 ray12726
theorem signs12726 : ∀ j, Signs p12726 (bank12726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12727 := params 22
abbrev ray12727 := rays 22
def bank12727 : Fin 2 → Cell := twoBank p12727 ray12727
theorem signs12727 : ∀ j, Signs p12727 (bank12727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12728 := params 23
abbrev ray12728 := rays 23
def bank12728 : Fin 2 → Cell := twoBank p12728 ray12728
theorem signs12728 : ∀ j, Signs p12728 (bank12728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12729 := params 24
abbrev ray12729 := rays 24
def bank12729 : Fin 2 → Cell := twoBank p12729 ray12729
theorem signs12729 : ∀ j, Signs p12729 (bank12729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12730 := params 25
abbrev ray12730 := rays 25
def bank12730 : Fin 2 → Cell := twoBank p12730 ray12730
theorem signs12730 : ∀ j, Signs p12730 (bank12730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12731 := params 26
abbrev ray12731 := rays 26
def bank12731 : Fin 2 → Cell := twoBank p12731 ray12731
theorem signs12731 : ∀ j, Signs p12731 (bank12731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12732 := params 27
abbrev ray12732 := rays 27
def bank12732 : Fin 2 → Cell := twoBank p12732 ray12732
theorem signs12732 : ∀ j, Signs p12732 (bank12732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12733 := params 28
abbrev ray12733 := rays 28
def bank12733 : Fin 2 → Cell := twoBank p12733 ray12733
theorem signs12733 : ∀ j, Signs p12733 (bank12733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12734 := params 29
abbrev ray12734 := rays 29
def bank12734 : Fin 2 → Cell := twoBank p12734 ray12734
theorem signs12734 : ∀ j, Signs p12734 (bank12734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12735 := params 30
abbrev ray12735 := rays 30
def bank12735 : Fin 2 → Cell := twoBank p12735 ray12735
theorem signs12735 : ∀ j, Signs p12735 (bank12735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12736 := params 31
abbrev ray12736 := rays 31
def bank12736 : Fin 2 → Cell := twoBank p12736 ray12736
theorem signs12736 : ∀ j, Signs p12736 (bank12736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12705_12736
