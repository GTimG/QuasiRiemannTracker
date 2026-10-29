/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05601_05632
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98877045249512,98876774512081,98876503751125,98876232966645,98875962158641,98875691327115,98875420472067,98875149593498,98874878691410,98874607765803,98874336816678,98874065844036,98873794847878,98873523828205,98873252785018,98872981718318,98872710628105,98872439514381,98872168377146,98871897216402,98871626032149,98871354824389,98871083593122,98870812338349,98870541060071,98870269758289,98869998433004,98869727084217,98869455711929,98869184316140,98868912896852,98868641454066,98868369987782]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5600+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5601 := params 0
abbrev ray5601 := rays 0
def bank5601 : Fin 2 → Cell := twoBank p5601 ray5601
theorem signs5601 : ∀ j, Signs p5601 (bank5601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5602 := params 1
abbrev ray5602 := rays 1
def bank5602 : Fin 2 → Cell := twoBank p5602 ray5602
theorem signs5602 : ∀ j, Signs p5602 (bank5602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5603 := params 2
abbrev ray5603 := rays 2
def bank5603 : Fin 2 → Cell := twoBank p5603 ray5603
theorem signs5603 : ∀ j, Signs p5603 (bank5603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5604 := params 3
abbrev ray5604 := rays 3
def bank5604 : Fin 2 → Cell := twoBank p5604 ray5604
theorem signs5604 : ∀ j, Signs p5604 (bank5604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5605 := params 4
abbrev ray5605 := rays 4
def bank5605 : Fin 2 → Cell := twoBank p5605 ray5605
theorem signs5605 : ∀ j, Signs p5605 (bank5605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5606 := params 5
abbrev ray5606 := rays 5
def bank5606 : Fin 2 → Cell := twoBank p5606 ray5606
theorem signs5606 : ∀ j, Signs p5606 (bank5606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5607 := params 6
abbrev ray5607 := rays 6
def bank5607 : Fin 2 → Cell := twoBank p5607 ray5607
theorem signs5607 : ∀ j, Signs p5607 (bank5607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5608 := params 7
abbrev ray5608 := rays 7
def bank5608 : Fin 2 → Cell := twoBank p5608 ray5608
theorem signs5608 : ∀ j, Signs p5608 (bank5608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5609 := params 8
abbrev ray5609 := rays 8
def bank5609 : Fin 2 → Cell := twoBank p5609 ray5609
theorem signs5609 : ∀ j, Signs p5609 (bank5609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5610 := params 9
abbrev ray5610 := rays 9
def bank5610 : Fin 2 → Cell := twoBank p5610 ray5610
theorem signs5610 : ∀ j, Signs p5610 (bank5610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5611 := params 10
abbrev ray5611 := rays 10
def bank5611 : Fin 2 → Cell := twoBank p5611 ray5611
theorem signs5611 : ∀ j, Signs p5611 (bank5611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5612 := params 11
abbrev ray5612 := rays 11
def bank5612 : Fin 2 → Cell := twoBank p5612 ray5612
theorem signs5612 : ∀ j, Signs p5612 (bank5612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5613 := params 12
abbrev ray5613 := rays 12
def bank5613 : Fin 2 → Cell := twoBank p5613 ray5613
theorem signs5613 : ∀ j, Signs p5613 (bank5613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5614 := params 13
abbrev ray5614 := rays 13
def bank5614 : Fin 2 → Cell := twoBank p5614 ray5614
theorem signs5614 : ∀ j, Signs p5614 (bank5614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5615 := params 14
abbrev ray5615 := rays 14
def bank5615 : Fin 2 → Cell := twoBank p5615 ray5615
theorem signs5615 : ∀ j, Signs p5615 (bank5615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5616 := params 15
abbrev ray5616 := rays 15
def bank5616 : Fin 2 → Cell := twoBank p5616 ray5616
theorem signs5616 : ∀ j, Signs p5616 (bank5616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5617 := params 16
abbrev ray5617 := rays 16
def bank5617 : Fin 2 → Cell := twoBank p5617 ray5617
theorem signs5617 : ∀ j, Signs p5617 (bank5617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5618 := params 17
abbrev ray5618 := rays 17
def bank5618 : Fin 2 → Cell := twoBank p5618 ray5618
theorem signs5618 : ∀ j, Signs p5618 (bank5618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5619 := params 18
abbrev ray5619 := rays 18
def bank5619 : Fin 2 → Cell := twoBank p5619 ray5619
theorem signs5619 : ∀ j, Signs p5619 (bank5619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5620 := params 19
abbrev ray5620 := rays 19
def bank5620 : Fin 2 → Cell := twoBank p5620 ray5620
theorem signs5620 : ∀ j, Signs p5620 (bank5620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5621 := params 20
abbrev ray5621 := rays 20
def bank5621 : Fin 2 → Cell := twoBank p5621 ray5621
theorem signs5621 : ∀ j, Signs p5621 (bank5621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5622 := params 21
abbrev ray5622 := rays 21
def bank5622 : Fin 2 → Cell := twoBank p5622 ray5622
theorem signs5622 : ∀ j, Signs p5622 (bank5622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5623 := params 22
abbrev ray5623 := rays 22
def bank5623 : Fin 2 → Cell := twoBank p5623 ray5623
theorem signs5623 : ∀ j, Signs p5623 (bank5623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5624 := params 23
abbrev ray5624 := rays 23
def bank5624 : Fin 2 → Cell := twoBank p5624 ray5624
theorem signs5624 : ∀ j, Signs p5624 (bank5624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5625 := params 24
abbrev ray5625 := rays 24
def bank5625 : Fin 2 → Cell := twoBank p5625 ray5625
theorem signs5625 : ∀ j, Signs p5625 (bank5625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5626 := params 25
abbrev ray5626 := rays 25
def bank5626 : Fin 2 → Cell := twoBank p5626 ray5626
theorem signs5626 : ∀ j, Signs p5626 (bank5626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5627 := params 26
abbrev ray5627 := rays 26
def bank5627 : Fin 2 → Cell := twoBank p5627 ray5627
theorem signs5627 : ∀ j, Signs p5627 (bank5627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5628 := params 27
abbrev ray5628 := rays 27
def bank5628 : Fin 2 → Cell := twoBank p5628 ray5628
theorem signs5628 : ∀ j, Signs p5628 (bank5628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5629 := params 28
abbrev ray5629 := rays 28
def bank5629 : Fin 2 → Cell := twoBank p5629 ray5629
theorem signs5629 : ∀ j, Signs p5629 (bank5629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5630 := params 29
abbrev ray5630 := rays 29
def bank5630 : Fin 2 → Cell := twoBank p5630 ray5630
theorem signs5630 : ∀ j, Signs p5630 (bank5630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5631 := params 30
abbrev ray5631 := rays 30
def bank5631 : Fin 2 → Cell := twoBank p5631 ray5631
theorem signs5631 : ∀ j, Signs p5631 (bank5631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5632 := params 31
abbrev ray5632 := rays 31
def bank5632 : Fin 2 → Cell := twoBank p5632 ray5632
theorem signs5632 : ∀ j, Signs p5632 (bank5632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05601_05632
