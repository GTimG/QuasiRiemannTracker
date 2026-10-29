/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08609_08640
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97960129794481,97959792034549,97959454253443,97959116451163,97958778627710,97958440783085,97958102917288,97957765030320,97957427122182,97957089192874,97956751242397,97956413270751,97956075277938,97955737263958,97955399228811,97955061172498,97954723095020,97954384996377,97954046876571,97953708735601,97953370573469,97953032390175,97952694185719,97952355960103,97952017713327,97951679445391,97951341156297,97951002846045,97950664514635,97950326162069,97949987788347,97949649393469,97949310977436]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8608+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8609 := params 0
abbrev ray8609 := rays 0
def bank8609 : Fin 2 → Cell := twoBank p8609 ray8609
theorem signs8609 : ∀ j, Signs p8609 (bank8609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8610 := params 1
abbrev ray8610 := rays 1
def bank8610 : Fin 2 → Cell := twoBank p8610 ray8610
theorem signs8610 : ∀ j, Signs p8610 (bank8610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8611 := params 2
abbrev ray8611 := rays 2
def bank8611 : Fin 2 → Cell := twoBank p8611 ray8611
theorem signs8611 : ∀ j, Signs p8611 (bank8611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8612 := params 3
abbrev ray8612 := rays 3
def bank8612 : Fin 2 → Cell := twoBank p8612 ray8612
theorem signs8612 : ∀ j, Signs p8612 (bank8612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8613 := params 4
abbrev ray8613 := rays 4
def bank8613 : Fin 2 → Cell := twoBank p8613 ray8613
theorem signs8613 : ∀ j, Signs p8613 (bank8613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8614 := params 5
abbrev ray8614 := rays 5
def bank8614 : Fin 2 → Cell := twoBank p8614 ray8614
theorem signs8614 : ∀ j, Signs p8614 (bank8614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8615 := params 6
abbrev ray8615 := rays 6
def bank8615 : Fin 2 → Cell := twoBank p8615 ray8615
theorem signs8615 : ∀ j, Signs p8615 (bank8615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8616 := params 7
abbrev ray8616 := rays 7
def bank8616 : Fin 2 → Cell := twoBank p8616 ray8616
theorem signs8616 : ∀ j, Signs p8616 (bank8616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8617 := params 8
abbrev ray8617 := rays 8
def bank8617 : Fin 2 → Cell := twoBank p8617 ray8617
theorem signs8617 : ∀ j, Signs p8617 (bank8617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8618 := params 9
abbrev ray8618 := rays 9
def bank8618 : Fin 2 → Cell := twoBank p8618 ray8618
theorem signs8618 : ∀ j, Signs p8618 (bank8618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8619 := params 10
abbrev ray8619 := rays 10
def bank8619 : Fin 2 → Cell := twoBank p8619 ray8619
theorem signs8619 : ∀ j, Signs p8619 (bank8619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8620 := params 11
abbrev ray8620 := rays 11
def bank8620 : Fin 2 → Cell := twoBank p8620 ray8620
theorem signs8620 : ∀ j, Signs p8620 (bank8620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8621 := params 12
abbrev ray8621 := rays 12
def bank8621 : Fin 2 → Cell := twoBank p8621 ray8621
theorem signs8621 : ∀ j, Signs p8621 (bank8621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8622 := params 13
abbrev ray8622 := rays 13
def bank8622 : Fin 2 → Cell := twoBank p8622 ray8622
theorem signs8622 : ∀ j, Signs p8622 (bank8622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8623 := params 14
abbrev ray8623 := rays 14
def bank8623 : Fin 2 → Cell := twoBank p8623 ray8623
theorem signs8623 : ∀ j, Signs p8623 (bank8623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8624 := params 15
abbrev ray8624 := rays 15
def bank8624 : Fin 2 → Cell := twoBank p8624 ray8624
theorem signs8624 : ∀ j, Signs p8624 (bank8624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8625 := params 16
abbrev ray8625 := rays 16
def bank8625 : Fin 2 → Cell := twoBank p8625 ray8625
theorem signs8625 : ∀ j, Signs p8625 (bank8625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8626 := params 17
abbrev ray8626 := rays 17
def bank8626 : Fin 2 → Cell := twoBank p8626 ray8626
theorem signs8626 : ∀ j, Signs p8626 (bank8626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8627 := params 18
abbrev ray8627 := rays 18
def bank8627 : Fin 2 → Cell := twoBank p8627 ray8627
theorem signs8627 : ∀ j, Signs p8627 (bank8627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8628 := params 19
abbrev ray8628 := rays 19
def bank8628 : Fin 2 → Cell := twoBank p8628 ray8628
theorem signs8628 : ∀ j, Signs p8628 (bank8628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8629 := params 20
abbrev ray8629 := rays 20
def bank8629 : Fin 2 → Cell := twoBank p8629 ray8629
theorem signs8629 : ∀ j, Signs p8629 (bank8629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8630 := params 21
abbrev ray8630 := rays 21
def bank8630 : Fin 2 → Cell := twoBank p8630 ray8630
theorem signs8630 : ∀ j, Signs p8630 (bank8630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8631 := params 22
abbrev ray8631 := rays 22
def bank8631 : Fin 2 → Cell := twoBank p8631 ray8631
theorem signs8631 : ∀ j, Signs p8631 (bank8631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8632 := params 23
abbrev ray8632 := rays 23
def bank8632 : Fin 2 → Cell := twoBank p8632 ray8632
theorem signs8632 : ∀ j, Signs p8632 (bank8632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8633 := params 24
abbrev ray8633 := rays 24
def bank8633 : Fin 2 → Cell := twoBank p8633 ray8633
theorem signs8633 : ∀ j, Signs p8633 (bank8633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8634 := params 25
abbrev ray8634 := rays 25
def bank8634 : Fin 2 → Cell := twoBank p8634 ray8634
theorem signs8634 : ∀ j, Signs p8634 (bank8634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8635 := params 26
abbrev ray8635 := rays 26
def bank8635 : Fin 2 → Cell := twoBank p8635 ray8635
theorem signs8635 : ∀ j, Signs p8635 (bank8635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8636 := params 27
abbrev ray8636 := rays 27
def bank8636 : Fin 2 → Cell := twoBank p8636 ray8636
theorem signs8636 : ∀ j, Signs p8636 (bank8636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8637 := params 28
abbrev ray8637 := rays 28
def bank8637 : Fin 2 → Cell := twoBank p8637 ray8637
theorem signs8637 : ∀ j, Signs p8637 (bank8637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8638 := params 29
abbrev ray8638 := rays 29
def bank8638 : Fin 2 → Cell := twoBank p8638 ray8638
theorem signs8638 : ∀ j, Signs p8638 (bank8638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8639 := params 30
abbrev ray8639 := rays 30
def bank8639 : Fin 2 → Cell := twoBank p8639 ray8639
theorem signs8639 : ∀ j, Signs p8639 (bank8639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8640 := params 31
abbrev ray8640 := rays 31
def bank8640 : Fin 2 → Cell := twoBank p8640 ray8640
theorem signs8640 : ∀ j, Signs p8640 (bank8640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08609_08640
