/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08641_08672
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97949310977436,97948972540249,97948634081909,97948295602416,97947957101771,97947618579974,97947280037026,97946941472928,97946602887680,97946264281283,97945925653738,97945587005046,97945248335207,97944909644221,97944570932089,97944232198812,97943893444391,97943554668826,97943215872118,97942877054268,97942538215276,97942199355143,97941860473869,97941521571455,97941182647902,97940843703211,97940504737382,97940165750415,97939826742312,97939487713073,97939148662699,97938809591190,97938470498547]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8640+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8641 := params 0
abbrev ray8641 := rays 0
def bank8641 : Fin 2 → Cell := twoBank p8641 ray8641
theorem signs8641 : ∀ j, Signs p8641 (bank8641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8642 := params 1
abbrev ray8642 := rays 1
def bank8642 : Fin 2 → Cell := twoBank p8642 ray8642
theorem signs8642 : ∀ j, Signs p8642 (bank8642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8643 := params 2
abbrev ray8643 := rays 2
def bank8643 : Fin 2 → Cell := twoBank p8643 ray8643
theorem signs8643 : ∀ j, Signs p8643 (bank8643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8644 := params 3
abbrev ray8644 := rays 3
def bank8644 : Fin 2 → Cell := twoBank p8644 ray8644
theorem signs8644 : ∀ j, Signs p8644 (bank8644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8645 := params 4
abbrev ray8645 := rays 4
def bank8645 : Fin 2 → Cell := twoBank p8645 ray8645
theorem signs8645 : ∀ j, Signs p8645 (bank8645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8646 := params 5
abbrev ray8646 := rays 5
def bank8646 : Fin 2 → Cell := twoBank p8646 ray8646
theorem signs8646 : ∀ j, Signs p8646 (bank8646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8647 := params 6
abbrev ray8647 := rays 6
def bank8647 : Fin 2 → Cell := twoBank p8647 ray8647
theorem signs8647 : ∀ j, Signs p8647 (bank8647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8648 := params 7
abbrev ray8648 := rays 7
def bank8648 : Fin 2 → Cell := twoBank p8648 ray8648
theorem signs8648 : ∀ j, Signs p8648 (bank8648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8649 := params 8
abbrev ray8649 := rays 8
def bank8649 : Fin 2 → Cell := twoBank p8649 ray8649
theorem signs8649 : ∀ j, Signs p8649 (bank8649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8650 := params 9
abbrev ray8650 := rays 9
def bank8650 : Fin 2 → Cell := twoBank p8650 ray8650
theorem signs8650 : ∀ j, Signs p8650 (bank8650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8651 := params 10
abbrev ray8651 := rays 10
def bank8651 : Fin 2 → Cell := twoBank p8651 ray8651
theorem signs8651 : ∀ j, Signs p8651 (bank8651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8652 := params 11
abbrev ray8652 := rays 11
def bank8652 : Fin 2 → Cell := twoBank p8652 ray8652
theorem signs8652 : ∀ j, Signs p8652 (bank8652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8653 := params 12
abbrev ray8653 := rays 12
def bank8653 : Fin 2 → Cell := twoBank p8653 ray8653
theorem signs8653 : ∀ j, Signs p8653 (bank8653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8654 := params 13
abbrev ray8654 := rays 13
def bank8654 : Fin 2 → Cell := twoBank p8654 ray8654
theorem signs8654 : ∀ j, Signs p8654 (bank8654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8655 := params 14
abbrev ray8655 := rays 14
def bank8655 : Fin 2 → Cell := twoBank p8655 ray8655
theorem signs8655 : ∀ j, Signs p8655 (bank8655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8656 := params 15
abbrev ray8656 := rays 15
def bank8656 : Fin 2 → Cell := twoBank p8656 ray8656
theorem signs8656 : ∀ j, Signs p8656 (bank8656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8657 := params 16
abbrev ray8657 := rays 16
def bank8657 : Fin 2 → Cell := twoBank p8657 ray8657
theorem signs8657 : ∀ j, Signs p8657 (bank8657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8658 := params 17
abbrev ray8658 := rays 17
def bank8658 : Fin 2 → Cell := twoBank p8658 ray8658
theorem signs8658 : ∀ j, Signs p8658 (bank8658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8659 := params 18
abbrev ray8659 := rays 18
def bank8659 : Fin 2 → Cell := twoBank p8659 ray8659
theorem signs8659 : ∀ j, Signs p8659 (bank8659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8660 := params 19
abbrev ray8660 := rays 19
def bank8660 : Fin 2 → Cell := twoBank p8660 ray8660
theorem signs8660 : ∀ j, Signs p8660 (bank8660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8661 := params 20
abbrev ray8661 := rays 20
def bank8661 : Fin 2 → Cell := twoBank p8661 ray8661
theorem signs8661 : ∀ j, Signs p8661 (bank8661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8662 := params 21
abbrev ray8662 := rays 21
def bank8662 : Fin 2 → Cell := twoBank p8662 ray8662
theorem signs8662 : ∀ j, Signs p8662 (bank8662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8663 := params 22
abbrev ray8663 := rays 22
def bank8663 : Fin 2 → Cell := twoBank p8663 ray8663
theorem signs8663 : ∀ j, Signs p8663 (bank8663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8664 := params 23
abbrev ray8664 := rays 23
def bank8664 : Fin 2 → Cell := twoBank p8664 ray8664
theorem signs8664 : ∀ j, Signs p8664 (bank8664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8665 := params 24
abbrev ray8665 := rays 24
def bank8665 : Fin 2 → Cell := twoBank p8665 ray8665
theorem signs8665 : ∀ j, Signs p8665 (bank8665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8666 := params 25
abbrev ray8666 := rays 25
def bank8666 : Fin 2 → Cell := twoBank p8666 ray8666
theorem signs8666 : ∀ j, Signs p8666 (bank8666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8667 := params 26
abbrev ray8667 := rays 26
def bank8667 : Fin 2 → Cell := twoBank p8667 ray8667
theorem signs8667 : ∀ j, Signs p8667 (bank8667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8668 := params 27
abbrev ray8668 := rays 27
def bank8668 : Fin 2 → Cell := twoBank p8668 ray8668
theorem signs8668 : ∀ j, Signs p8668 (bank8668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8669 := params 28
abbrev ray8669 := rays 28
def bank8669 : Fin 2 → Cell := twoBank p8669 ray8669
theorem signs8669 : ∀ j, Signs p8669 (bank8669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8670 := params 29
abbrev ray8670 := rays 29
def bank8670 : Fin 2 → Cell := twoBank p8670 ray8670
theorem signs8670 : ∀ j, Signs p8670 (bank8670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8671 := params 30
abbrev ray8671 := rays 30
def bank8671 : Fin 2 → Cell := twoBank p8671 ray8671
theorem signs8671 : ∀ j, Signs p8671 (bank8671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8672 := params 31
abbrev ray8672 := rays 31
def bank8672 : Fin 2 → Cell := twoBank p8672 ray8672
theorem signs8672 : ∀ j, Signs p8672 (bank8672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08641_08672
