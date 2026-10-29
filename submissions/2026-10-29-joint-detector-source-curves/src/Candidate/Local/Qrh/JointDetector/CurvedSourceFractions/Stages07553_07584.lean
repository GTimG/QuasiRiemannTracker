/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07553_07584
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98304854526705,98304539506351,98304224464089,98303909399920,98303594313846,98303279205866,98302964075982,98302648924194,98302333750503,98302018554910,98301703337415,98301388098020,98301072836725,98300757553530,98300442248437,98300126921446,98299811572558,98299496201774,98299180809094,98298865394519,98298549958050,98298234499687,98297919019432,98297603517285,98297287993247,98296972447318,98296656879500,98296341289793,98296025678197,98295710044714,98295394389344,98295078712088,98294763012947]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7552+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7553 := params 0
abbrev ray7553 := rays 0
def bank7553 : Fin 2 → Cell := twoBank p7553 ray7553
theorem signs7553 : ∀ j, Signs p7553 (bank7553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7554 := params 1
abbrev ray7554 := rays 1
def bank7554 : Fin 2 → Cell := twoBank p7554 ray7554
theorem signs7554 : ∀ j, Signs p7554 (bank7554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7555 := params 2
abbrev ray7555 := rays 2
def bank7555 : Fin 2 → Cell := twoBank p7555 ray7555
theorem signs7555 : ∀ j, Signs p7555 (bank7555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7556 := params 3
abbrev ray7556 := rays 3
def bank7556 : Fin 2 → Cell := twoBank p7556 ray7556
theorem signs7556 : ∀ j, Signs p7556 (bank7556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7557 := params 4
abbrev ray7557 := rays 4
def bank7557 : Fin 2 → Cell := twoBank p7557 ray7557
theorem signs7557 : ∀ j, Signs p7557 (bank7557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7558 := params 5
abbrev ray7558 := rays 5
def bank7558 : Fin 2 → Cell := twoBank p7558 ray7558
theorem signs7558 : ∀ j, Signs p7558 (bank7558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7559 := params 6
abbrev ray7559 := rays 6
def bank7559 : Fin 2 → Cell := twoBank p7559 ray7559
theorem signs7559 : ∀ j, Signs p7559 (bank7559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7560 := params 7
abbrev ray7560 := rays 7
def bank7560 : Fin 2 → Cell := twoBank p7560 ray7560
theorem signs7560 : ∀ j, Signs p7560 (bank7560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7561 := params 8
abbrev ray7561 := rays 8
def bank7561 : Fin 2 → Cell := twoBank p7561 ray7561
theorem signs7561 : ∀ j, Signs p7561 (bank7561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7562 := params 9
abbrev ray7562 := rays 9
def bank7562 : Fin 2 → Cell := twoBank p7562 ray7562
theorem signs7562 : ∀ j, Signs p7562 (bank7562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7563 := params 10
abbrev ray7563 := rays 10
def bank7563 : Fin 2 → Cell := twoBank p7563 ray7563
theorem signs7563 : ∀ j, Signs p7563 (bank7563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7564 := params 11
abbrev ray7564 := rays 11
def bank7564 : Fin 2 → Cell := twoBank p7564 ray7564
theorem signs7564 : ∀ j, Signs p7564 (bank7564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7565 := params 12
abbrev ray7565 := rays 12
def bank7565 : Fin 2 → Cell := twoBank p7565 ray7565
theorem signs7565 : ∀ j, Signs p7565 (bank7565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7566 := params 13
abbrev ray7566 := rays 13
def bank7566 : Fin 2 → Cell := twoBank p7566 ray7566
theorem signs7566 : ∀ j, Signs p7566 (bank7566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7567 := params 14
abbrev ray7567 := rays 14
def bank7567 : Fin 2 → Cell := twoBank p7567 ray7567
theorem signs7567 : ∀ j, Signs p7567 (bank7567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7568 := params 15
abbrev ray7568 := rays 15
def bank7568 : Fin 2 → Cell := twoBank p7568 ray7568
theorem signs7568 : ∀ j, Signs p7568 (bank7568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7569 := params 16
abbrev ray7569 := rays 16
def bank7569 : Fin 2 → Cell := twoBank p7569 ray7569
theorem signs7569 : ∀ j, Signs p7569 (bank7569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7570 := params 17
abbrev ray7570 := rays 17
def bank7570 : Fin 2 → Cell := twoBank p7570 ray7570
theorem signs7570 : ∀ j, Signs p7570 (bank7570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7571 := params 18
abbrev ray7571 := rays 18
def bank7571 : Fin 2 → Cell := twoBank p7571 ray7571
theorem signs7571 : ∀ j, Signs p7571 (bank7571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7572 := params 19
abbrev ray7572 := rays 19
def bank7572 : Fin 2 → Cell := twoBank p7572 ray7572
theorem signs7572 : ∀ j, Signs p7572 (bank7572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7573 := params 20
abbrev ray7573 := rays 20
def bank7573 : Fin 2 → Cell := twoBank p7573 ray7573
theorem signs7573 : ∀ j, Signs p7573 (bank7573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7574 := params 21
abbrev ray7574 := rays 21
def bank7574 : Fin 2 → Cell := twoBank p7574 ray7574
theorem signs7574 : ∀ j, Signs p7574 (bank7574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7575 := params 22
abbrev ray7575 := rays 22
def bank7575 : Fin 2 → Cell := twoBank p7575 ray7575
theorem signs7575 : ∀ j, Signs p7575 (bank7575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7576 := params 23
abbrev ray7576 := rays 23
def bank7576 : Fin 2 → Cell := twoBank p7576 ray7576
theorem signs7576 : ∀ j, Signs p7576 (bank7576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7577 := params 24
abbrev ray7577 := rays 24
def bank7577 : Fin 2 → Cell := twoBank p7577 ray7577
theorem signs7577 : ∀ j, Signs p7577 (bank7577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7578 := params 25
abbrev ray7578 := rays 25
def bank7578 : Fin 2 → Cell := twoBank p7578 ray7578
theorem signs7578 : ∀ j, Signs p7578 (bank7578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7579 := params 26
abbrev ray7579 := rays 26
def bank7579 : Fin 2 → Cell := twoBank p7579 ray7579
theorem signs7579 : ∀ j, Signs p7579 (bank7579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7580 := params 27
abbrev ray7580 := rays 27
def bank7580 : Fin 2 → Cell := twoBank p7580 ray7580
theorem signs7580 : ∀ j, Signs p7580 (bank7580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7581 := params 28
abbrev ray7581 := rays 28
def bank7581 : Fin 2 → Cell := twoBank p7581 ray7581
theorem signs7581 : ∀ j, Signs p7581 (bank7581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7582 := params 29
abbrev ray7582 := rays 29
def bank7582 : Fin 2 → Cell := twoBank p7582 ray7582
theorem signs7582 : ∀ j, Signs p7582 (bank7582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7583 := params 30
abbrev ray7583 := rays 30
def bank7583 : Fin 2 → Cell := twoBank p7583 ray7583
theorem signs7583 : ∀ j, Signs p7583 (bank7583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7584 := params 31
abbrev ray7584 := rays 31
def bank7584 : Fin 2 → Cell := twoBank p7584 ray7584
theorem signs7584 : ∀ j, Signs p7584 (bank7584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07553_07584
