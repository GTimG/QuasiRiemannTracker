/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11553_11584
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96876581975487,96876184403022,96875786811003,96875389199431,96874991568306,96874593917628,96874196247398,96873798557616,96873400848283,96873003119399,96872605370964,96872207602979,96871809815445,96871412008362,96871014181730,96870616335550,96870218469822,96869820584547,96869422679725,96869024755357,96868626811443,96868228847984,96867830864980,96867432862431,96867034840338,96866636798702,96866238737523,96865840656801,96865442556537,96865044436731,96864646297384,96864248138496,96863849960067]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11552+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11553 := params 0
abbrev ray11553 := rays 0
def bank11553 : Fin 2 → Cell := twoBank p11553 ray11553
theorem signs11553 : ∀ j, Signs p11553 (bank11553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11554 := params 1
abbrev ray11554 := rays 1
def bank11554 : Fin 2 → Cell := twoBank p11554 ray11554
theorem signs11554 : ∀ j, Signs p11554 (bank11554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11555 := params 2
abbrev ray11555 := rays 2
def bank11555 : Fin 2 → Cell := twoBank p11555 ray11555
theorem signs11555 : ∀ j, Signs p11555 (bank11555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11556 := params 3
abbrev ray11556 := rays 3
def bank11556 : Fin 2 → Cell := twoBank p11556 ray11556
theorem signs11556 : ∀ j, Signs p11556 (bank11556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11557 := params 4
abbrev ray11557 := rays 4
def bank11557 : Fin 2 → Cell := twoBank p11557 ray11557
theorem signs11557 : ∀ j, Signs p11557 (bank11557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11558 := params 5
abbrev ray11558 := rays 5
def bank11558 : Fin 2 → Cell := twoBank p11558 ray11558
theorem signs11558 : ∀ j, Signs p11558 (bank11558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11559 := params 6
abbrev ray11559 := rays 6
def bank11559 : Fin 2 → Cell := twoBank p11559 ray11559
theorem signs11559 : ∀ j, Signs p11559 (bank11559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11560 := params 7
abbrev ray11560 := rays 7
def bank11560 : Fin 2 → Cell := twoBank p11560 ray11560
theorem signs11560 : ∀ j, Signs p11560 (bank11560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11561 := params 8
abbrev ray11561 := rays 8
def bank11561 : Fin 2 → Cell := twoBank p11561 ray11561
theorem signs11561 : ∀ j, Signs p11561 (bank11561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11562 := params 9
abbrev ray11562 := rays 9
def bank11562 : Fin 2 → Cell := twoBank p11562 ray11562
theorem signs11562 : ∀ j, Signs p11562 (bank11562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11563 := params 10
abbrev ray11563 := rays 10
def bank11563 : Fin 2 → Cell := twoBank p11563 ray11563
theorem signs11563 : ∀ j, Signs p11563 (bank11563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11564 := params 11
abbrev ray11564 := rays 11
def bank11564 : Fin 2 → Cell := twoBank p11564 ray11564
theorem signs11564 : ∀ j, Signs p11564 (bank11564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11565 := params 12
abbrev ray11565 := rays 12
def bank11565 : Fin 2 → Cell := twoBank p11565 ray11565
theorem signs11565 : ∀ j, Signs p11565 (bank11565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11566 := params 13
abbrev ray11566 := rays 13
def bank11566 : Fin 2 → Cell := twoBank p11566 ray11566
theorem signs11566 : ∀ j, Signs p11566 (bank11566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11567 := params 14
abbrev ray11567 := rays 14
def bank11567 : Fin 2 → Cell := twoBank p11567 ray11567
theorem signs11567 : ∀ j, Signs p11567 (bank11567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11568 := params 15
abbrev ray11568 := rays 15
def bank11568 : Fin 2 → Cell := twoBank p11568 ray11568
theorem signs11568 : ∀ j, Signs p11568 (bank11568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11569 := params 16
abbrev ray11569 := rays 16
def bank11569 : Fin 2 → Cell := twoBank p11569 ray11569
theorem signs11569 : ∀ j, Signs p11569 (bank11569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11570 := params 17
abbrev ray11570 := rays 17
def bank11570 : Fin 2 → Cell := twoBank p11570 ray11570
theorem signs11570 : ∀ j, Signs p11570 (bank11570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11571 := params 18
abbrev ray11571 := rays 18
def bank11571 : Fin 2 → Cell := twoBank p11571 ray11571
theorem signs11571 : ∀ j, Signs p11571 (bank11571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11572 := params 19
abbrev ray11572 := rays 19
def bank11572 : Fin 2 → Cell := twoBank p11572 ray11572
theorem signs11572 : ∀ j, Signs p11572 (bank11572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11573 := params 20
abbrev ray11573 := rays 20
def bank11573 : Fin 2 → Cell := twoBank p11573 ray11573
theorem signs11573 : ∀ j, Signs p11573 (bank11573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11574 := params 21
abbrev ray11574 := rays 21
def bank11574 : Fin 2 → Cell := twoBank p11574 ray11574
theorem signs11574 : ∀ j, Signs p11574 (bank11574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11575 := params 22
abbrev ray11575 := rays 22
def bank11575 : Fin 2 → Cell := twoBank p11575 ray11575
theorem signs11575 : ∀ j, Signs p11575 (bank11575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11576 := params 23
abbrev ray11576 := rays 23
def bank11576 : Fin 2 → Cell := twoBank p11576 ray11576
theorem signs11576 : ∀ j, Signs p11576 (bank11576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11577 := params 24
abbrev ray11577 := rays 24
def bank11577 : Fin 2 → Cell := twoBank p11577 ray11577
theorem signs11577 : ∀ j, Signs p11577 (bank11577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11578 := params 25
abbrev ray11578 := rays 25
def bank11578 : Fin 2 → Cell := twoBank p11578 ray11578
theorem signs11578 : ∀ j, Signs p11578 (bank11578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11579 := params 26
abbrev ray11579 := rays 26
def bank11579 : Fin 2 → Cell := twoBank p11579 ray11579
theorem signs11579 : ∀ j, Signs p11579 (bank11579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11580 := params 27
abbrev ray11580 := rays 27
def bank11580 : Fin 2 → Cell := twoBank p11580 ray11580
theorem signs11580 : ∀ j, Signs p11580 (bank11580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11581 := params 28
abbrev ray11581 := rays 28
def bank11581 : Fin 2 → Cell := twoBank p11581 ray11581
theorem signs11581 : ∀ j, Signs p11581 (bank11581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11582 := params 29
abbrev ray11582 := rays 29
def bank11582 : Fin 2 → Cell := twoBank p11582 ray11582
theorem signs11582 : ∀ j, Signs p11582 (bank11582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11583 := params 30
abbrev ray11583 := rays 30
def bank11583 : Fin 2 → Cell := twoBank p11583 ray11583
theorem signs11583 : ∀ j, Signs p11583 (bank11583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11584 := params 31
abbrev ray11584 := rays 31
def bank11584 : Fin 2 → Cell := twoBank p11584 ray11584
theorem signs11584 : ∀ j, Signs p11584 (bank11584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11553_11584
