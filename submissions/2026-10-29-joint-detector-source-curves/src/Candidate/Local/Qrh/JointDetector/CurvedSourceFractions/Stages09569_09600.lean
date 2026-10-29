/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09569_09600
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97626226548183,97625868750223,97625510931681,97625153092558,97624795232854,97624437352569,97624079451705,97623721530261,97623363588239,97623005625639,97622647642461,97622289638707,97621931614376,97621573569470,97621215503988,97620857417932,97620499311302,97620141184099,97619783036323,97619424867975,97619066679055,97618708469564,97618350239503,97617991988872,97617633717671,97617275425902,97616917113565,97616558780660,97616200427188,97615842053150,97615483658546,97615125243377,97614766807643]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9568+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9569 := params 0
abbrev ray9569 := rays 0
def bank9569 : Fin 2 → Cell := twoBank p9569 ray9569
theorem signs9569 : ∀ j, Signs p9569 (bank9569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9570 := params 1
abbrev ray9570 := rays 1
def bank9570 : Fin 2 → Cell := twoBank p9570 ray9570
theorem signs9570 : ∀ j, Signs p9570 (bank9570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9571 := params 2
abbrev ray9571 := rays 2
def bank9571 : Fin 2 → Cell := twoBank p9571 ray9571
theorem signs9571 : ∀ j, Signs p9571 (bank9571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9572 := params 3
abbrev ray9572 := rays 3
def bank9572 : Fin 2 → Cell := twoBank p9572 ray9572
theorem signs9572 : ∀ j, Signs p9572 (bank9572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9573 := params 4
abbrev ray9573 := rays 4
def bank9573 : Fin 2 → Cell := twoBank p9573 ray9573
theorem signs9573 : ∀ j, Signs p9573 (bank9573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9574 := params 5
abbrev ray9574 := rays 5
def bank9574 : Fin 2 → Cell := twoBank p9574 ray9574
theorem signs9574 : ∀ j, Signs p9574 (bank9574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9575 := params 6
abbrev ray9575 := rays 6
def bank9575 : Fin 2 → Cell := twoBank p9575 ray9575
theorem signs9575 : ∀ j, Signs p9575 (bank9575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9576 := params 7
abbrev ray9576 := rays 7
def bank9576 : Fin 2 → Cell := twoBank p9576 ray9576
theorem signs9576 : ∀ j, Signs p9576 (bank9576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9577 := params 8
abbrev ray9577 := rays 8
def bank9577 : Fin 2 → Cell := twoBank p9577 ray9577
theorem signs9577 : ∀ j, Signs p9577 (bank9577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9578 := params 9
abbrev ray9578 := rays 9
def bank9578 : Fin 2 → Cell := twoBank p9578 ray9578
theorem signs9578 : ∀ j, Signs p9578 (bank9578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9579 := params 10
abbrev ray9579 := rays 10
def bank9579 : Fin 2 → Cell := twoBank p9579 ray9579
theorem signs9579 : ∀ j, Signs p9579 (bank9579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9580 := params 11
abbrev ray9580 := rays 11
def bank9580 : Fin 2 → Cell := twoBank p9580 ray9580
theorem signs9580 : ∀ j, Signs p9580 (bank9580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9581 := params 12
abbrev ray9581 := rays 12
def bank9581 : Fin 2 → Cell := twoBank p9581 ray9581
theorem signs9581 : ∀ j, Signs p9581 (bank9581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9582 := params 13
abbrev ray9582 := rays 13
def bank9582 : Fin 2 → Cell := twoBank p9582 ray9582
theorem signs9582 : ∀ j, Signs p9582 (bank9582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9583 := params 14
abbrev ray9583 := rays 14
def bank9583 : Fin 2 → Cell := twoBank p9583 ray9583
theorem signs9583 : ∀ j, Signs p9583 (bank9583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9584 := params 15
abbrev ray9584 := rays 15
def bank9584 : Fin 2 → Cell := twoBank p9584 ray9584
theorem signs9584 : ∀ j, Signs p9584 (bank9584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9585 := params 16
abbrev ray9585 := rays 16
def bank9585 : Fin 2 → Cell := twoBank p9585 ray9585
theorem signs9585 : ∀ j, Signs p9585 (bank9585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9586 := params 17
abbrev ray9586 := rays 17
def bank9586 : Fin 2 → Cell := twoBank p9586 ray9586
theorem signs9586 : ∀ j, Signs p9586 (bank9586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9587 := params 18
abbrev ray9587 := rays 18
def bank9587 : Fin 2 → Cell := twoBank p9587 ray9587
theorem signs9587 : ∀ j, Signs p9587 (bank9587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9588 := params 19
abbrev ray9588 := rays 19
def bank9588 : Fin 2 → Cell := twoBank p9588 ray9588
theorem signs9588 : ∀ j, Signs p9588 (bank9588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9589 := params 20
abbrev ray9589 := rays 20
def bank9589 : Fin 2 → Cell := twoBank p9589 ray9589
theorem signs9589 : ∀ j, Signs p9589 (bank9589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9590 := params 21
abbrev ray9590 := rays 21
def bank9590 : Fin 2 → Cell := twoBank p9590 ray9590
theorem signs9590 : ∀ j, Signs p9590 (bank9590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9591 := params 22
abbrev ray9591 := rays 22
def bank9591 : Fin 2 → Cell := twoBank p9591 ray9591
theorem signs9591 : ∀ j, Signs p9591 (bank9591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9592 := params 23
abbrev ray9592 := rays 23
def bank9592 : Fin 2 → Cell := twoBank p9592 ray9592
theorem signs9592 : ∀ j, Signs p9592 (bank9592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9593 := params 24
abbrev ray9593 := rays 24
def bank9593 : Fin 2 → Cell := twoBank p9593 ray9593
theorem signs9593 : ∀ j, Signs p9593 (bank9593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9594 := params 25
abbrev ray9594 := rays 25
def bank9594 : Fin 2 → Cell := twoBank p9594 ray9594
theorem signs9594 : ∀ j, Signs p9594 (bank9594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9595 := params 26
abbrev ray9595 := rays 26
def bank9595 : Fin 2 → Cell := twoBank p9595 ray9595
theorem signs9595 : ∀ j, Signs p9595 (bank9595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9596 := params 27
abbrev ray9596 := rays 27
def bank9596 : Fin 2 → Cell := twoBank p9596 ray9596
theorem signs9596 : ∀ j, Signs p9596 (bank9596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9597 := params 28
abbrev ray9597 := rays 28
def bank9597 : Fin 2 → Cell := twoBank p9597 ray9597
theorem signs9597 : ∀ j, Signs p9597 (bank9597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9598 := params 29
abbrev ray9598 := rays 29
def bank9598 : Fin 2 → Cell := twoBank p9598 ray9598
theorem signs9598 : ∀ j, Signs p9598 (bank9598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9599 := params 30
abbrev ray9599 := rays 30
def bank9599 : Fin 2 → Cell := twoBank p9599 ray9599
theorem signs9599 : ∀ j, Signs p9599 (bank9599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9600 := params 31
abbrev ray9600 := rays 31
def bank9600 : Fin 2 → Cell := twoBank p9600 ray9600
theorem signs9600 : ∀ j, Signs p9600 (bank9600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09569_09600
