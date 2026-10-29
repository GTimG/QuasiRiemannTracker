/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11649_11680
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96838325917430,96837926469851,96837527002761,96837127516161,96836728010052,96836328484433,96835928939306,96835529374671,96835129790528,96834730186878,96834330563721,96833930921057,96833531258887,96833131577212,96832731876032,96832332155347,96831932415158,96831532655465,96831132876269,96830733077570,96830333259369,96829933421666,96829533564462,96829133687757,96828733791551,96828333875845,96827933940640,96827533985935,96827134011732,96826734018030,96826334004831,96825933972134,96825533919940]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11648+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11649 := params 0
abbrev ray11649 := rays 0
def bank11649 : Fin 2 → Cell := twoBank p11649 ray11649
theorem signs11649 : ∀ j, Signs p11649 (bank11649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11650 := params 1
abbrev ray11650 := rays 1
def bank11650 : Fin 2 → Cell := twoBank p11650 ray11650
theorem signs11650 : ∀ j, Signs p11650 (bank11650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11651 := params 2
abbrev ray11651 := rays 2
def bank11651 : Fin 2 → Cell := twoBank p11651 ray11651
theorem signs11651 : ∀ j, Signs p11651 (bank11651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11652 := params 3
abbrev ray11652 := rays 3
def bank11652 : Fin 2 → Cell := twoBank p11652 ray11652
theorem signs11652 : ∀ j, Signs p11652 (bank11652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11653 := params 4
abbrev ray11653 := rays 4
def bank11653 : Fin 2 → Cell := twoBank p11653 ray11653
theorem signs11653 : ∀ j, Signs p11653 (bank11653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11654 := params 5
abbrev ray11654 := rays 5
def bank11654 : Fin 2 → Cell := twoBank p11654 ray11654
theorem signs11654 : ∀ j, Signs p11654 (bank11654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11655 := params 6
abbrev ray11655 := rays 6
def bank11655 : Fin 2 → Cell := twoBank p11655 ray11655
theorem signs11655 : ∀ j, Signs p11655 (bank11655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11656 := params 7
abbrev ray11656 := rays 7
def bank11656 : Fin 2 → Cell := twoBank p11656 ray11656
theorem signs11656 : ∀ j, Signs p11656 (bank11656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11657 := params 8
abbrev ray11657 := rays 8
def bank11657 : Fin 2 → Cell := twoBank p11657 ray11657
theorem signs11657 : ∀ j, Signs p11657 (bank11657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11658 := params 9
abbrev ray11658 := rays 9
def bank11658 : Fin 2 → Cell := twoBank p11658 ray11658
theorem signs11658 : ∀ j, Signs p11658 (bank11658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11659 := params 10
abbrev ray11659 := rays 10
def bank11659 : Fin 2 → Cell := twoBank p11659 ray11659
theorem signs11659 : ∀ j, Signs p11659 (bank11659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11660 := params 11
abbrev ray11660 := rays 11
def bank11660 : Fin 2 → Cell := twoBank p11660 ray11660
theorem signs11660 : ∀ j, Signs p11660 (bank11660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11661 := params 12
abbrev ray11661 := rays 12
def bank11661 : Fin 2 → Cell := twoBank p11661 ray11661
theorem signs11661 : ∀ j, Signs p11661 (bank11661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11662 := params 13
abbrev ray11662 := rays 13
def bank11662 : Fin 2 → Cell := twoBank p11662 ray11662
theorem signs11662 : ∀ j, Signs p11662 (bank11662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11663 := params 14
abbrev ray11663 := rays 14
def bank11663 : Fin 2 → Cell := twoBank p11663 ray11663
theorem signs11663 : ∀ j, Signs p11663 (bank11663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11664 := params 15
abbrev ray11664 := rays 15
def bank11664 : Fin 2 → Cell := twoBank p11664 ray11664
theorem signs11664 : ∀ j, Signs p11664 (bank11664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11665 := params 16
abbrev ray11665 := rays 16
def bank11665 : Fin 2 → Cell := twoBank p11665 ray11665
theorem signs11665 : ∀ j, Signs p11665 (bank11665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11666 := params 17
abbrev ray11666 := rays 17
def bank11666 : Fin 2 → Cell := twoBank p11666 ray11666
theorem signs11666 : ∀ j, Signs p11666 (bank11666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11667 := params 18
abbrev ray11667 := rays 18
def bank11667 : Fin 2 → Cell := twoBank p11667 ray11667
theorem signs11667 : ∀ j, Signs p11667 (bank11667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11668 := params 19
abbrev ray11668 := rays 19
def bank11668 : Fin 2 → Cell := twoBank p11668 ray11668
theorem signs11668 : ∀ j, Signs p11668 (bank11668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11669 := params 20
abbrev ray11669 := rays 20
def bank11669 : Fin 2 → Cell := twoBank p11669 ray11669
theorem signs11669 : ∀ j, Signs p11669 (bank11669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11670 := params 21
abbrev ray11670 := rays 21
def bank11670 : Fin 2 → Cell := twoBank p11670 ray11670
theorem signs11670 : ∀ j, Signs p11670 (bank11670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11671 := params 22
abbrev ray11671 := rays 22
def bank11671 : Fin 2 → Cell := twoBank p11671 ray11671
theorem signs11671 : ∀ j, Signs p11671 (bank11671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11672 := params 23
abbrev ray11672 := rays 23
def bank11672 : Fin 2 → Cell := twoBank p11672 ray11672
theorem signs11672 : ∀ j, Signs p11672 (bank11672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11673 := params 24
abbrev ray11673 := rays 24
def bank11673 : Fin 2 → Cell := twoBank p11673 ray11673
theorem signs11673 : ∀ j, Signs p11673 (bank11673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11674 := params 25
abbrev ray11674 := rays 25
def bank11674 : Fin 2 → Cell := twoBank p11674 ray11674
theorem signs11674 : ∀ j, Signs p11674 (bank11674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11675 := params 26
abbrev ray11675 := rays 26
def bank11675 : Fin 2 → Cell := twoBank p11675 ray11675
theorem signs11675 : ∀ j, Signs p11675 (bank11675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11676 := params 27
abbrev ray11676 := rays 27
def bank11676 : Fin 2 → Cell := twoBank p11676 ray11676
theorem signs11676 : ∀ j, Signs p11676 (bank11676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11677 := params 28
abbrev ray11677 := rays 28
def bank11677 : Fin 2 → Cell := twoBank p11677 ray11677
theorem signs11677 : ∀ j, Signs p11677 (bank11677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11678 := params 29
abbrev ray11678 := rays 29
def bank11678 : Fin 2 → Cell := twoBank p11678 ray11678
theorem signs11678 : ∀ j, Signs p11678 (bank11678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11679 := params 30
abbrev ray11679 := rays 30
def bank11679 : Fin 2 → Cell := twoBank p11679 ray11679
theorem signs11679 : ∀ j, Signs p11679 (bank11679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11680 := params 31
abbrev ray11680 := rays 31
def bank11680 : Fin 2 → Cell := twoBank p11680 ray11680
theorem signs11680 : ∀ j, Signs p11680 (bank11680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11649_11680
