/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04577_04608
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99141762594368,99141516454127,99141270289350,99141024100038,99140777886193,99140531647815,99140285384905,99140039097465,99139792785495,99139546448997,99139300087972,99139053702420,99138807292343,99138560857742,99138314398618,99138067914971,99137821406803,99137574874115,99137328316908,99137081735183,99136835128941,99136588498184,99136341842912,99136095163126,99135848458827,99135601730017,99135354976696,99135108198865,99134861396526,99134614569679,99134367718326,99134120842468,99133873942105]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4576+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4577 := params 0
abbrev ray4577 := rays 0
def bank4577 : Fin 2 → Cell := twoBank p4577 ray4577
theorem signs4577 : ∀ j, Signs p4577 (bank4577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4578 := params 1
abbrev ray4578 := rays 1
def bank4578 : Fin 2 → Cell := twoBank p4578 ray4578
theorem signs4578 : ∀ j, Signs p4578 (bank4578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4579 := params 2
abbrev ray4579 := rays 2
def bank4579 : Fin 2 → Cell := twoBank p4579 ray4579
theorem signs4579 : ∀ j, Signs p4579 (bank4579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4580 := params 3
abbrev ray4580 := rays 3
def bank4580 : Fin 2 → Cell := twoBank p4580 ray4580
theorem signs4580 : ∀ j, Signs p4580 (bank4580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4581 := params 4
abbrev ray4581 := rays 4
def bank4581 : Fin 2 → Cell := twoBank p4581 ray4581
theorem signs4581 : ∀ j, Signs p4581 (bank4581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4582 := params 5
abbrev ray4582 := rays 5
def bank4582 : Fin 2 → Cell := twoBank p4582 ray4582
theorem signs4582 : ∀ j, Signs p4582 (bank4582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4583 := params 6
abbrev ray4583 := rays 6
def bank4583 : Fin 2 → Cell := twoBank p4583 ray4583
theorem signs4583 : ∀ j, Signs p4583 (bank4583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4584 := params 7
abbrev ray4584 := rays 7
def bank4584 : Fin 2 → Cell := twoBank p4584 ray4584
theorem signs4584 : ∀ j, Signs p4584 (bank4584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4585 := params 8
abbrev ray4585 := rays 8
def bank4585 : Fin 2 → Cell := twoBank p4585 ray4585
theorem signs4585 : ∀ j, Signs p4585 (bank4585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4586 := params 9
abbrev ray4586 := rays 9
def bank4586 : Fin 2 → Cell := twoBank p4586 ray4586
theorem signs4586 : ∀ j, Signs p4586 (bank4586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4587 := params 10
abbrev ray4587 := rays 10
def bank4587 : Fin 2 → Cell := twoBank p4587 ray4587
theorem signs4587 : ∀ j, Signs p4587 (bank4587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4588 := params 11
abbrev ray4588 := rays 11
def bank4588 : Fin 2 → Cell := twoBank p4588 ray4588
theorem signs4588 : ∀ j, Signs p4588 (bank4588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4589 := params 12
abbrev ray4589 := rays 12
def bank4589 : Fin 2 → Cell := twoBank p4589 ray4589
theorem signs4589 : ∀ j, Signs p4589 (bank4589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4590 := params 13
abbrev ray4590 := rays 13
def bank4590 : Fin 2 → Cell := twoBank p4590 ray4590
theorem signs4590 : ∀ j, Signs p4590 (bank4590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4591 := params 14
abbrev ray4591 := rays 14
def bank4591 : Fin 2 → Cell := twoBank p4591 ray4591
theorem signs4591 : ∀ j, Signs p4591 (bank4591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4592 := params 15
abbrev ray4592 := rays 15
def bank4592 : Fin 2 → Cell := twoBank p4592 ray4592
theorem signs4592 : ∀ j, Signs p4592 (bank4592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4593 := params 16
abbrev ray4593 := rays 16
def bank4593 : Fin 2 → Cell := twoBank p4593 ray4593
theorem signs4593 : ∀ j, Signs p4593 (bank4593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4594 := params 17
abbrev ray4594 := rays 17
def bank4594 : Fin 2 → Cell := twoBank p4594 ray4594
theorem signs4594 : ∀ j, Signs p4594 (bank4594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4595 := params 18
abbrev ray4595 := rays 18
def bank4595 : Fin 2 → Cell := twoBank p4595 ray4595
theorem signs4595 : ∀ j, Signs p4595 (bank4595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4596 := params 19
abbrev ray4596 := rays 19
def bank4596 : Fin 2 → Cell := twoBank p4596 ray4596
theorem signs4596 : ∀ j, Signs p4596 (bank4596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4597 := params 20
abbrev ray4597 := rays 20
def bank4597 : Fin 2 → Cell := twoBank p4597 ray4597
theorem signs4597 : ∀ j, Signs p4597 (bank4597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4598 := params 21
abbrev ray4598 := rays 21
def bank4598 : Fin 2 → Cell := twoBank p4598 ray4598
theorem signs4598 : ∀ j, Signs p4598 (bank4598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4599 := params 22
abbrev ray4599 := rays 22
def bank4599 : Fin 2 → Cell := twoBank p4599 ray4599
theorem signs4599 : ∀ j, Signs p4599 (bank4599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4600 := params 23
abbrev ray4600 := rays 23
def bank4600 : Fin 2 → Cell := twoBank p4600 ray4600
theorem signs4600 : ∀ j, Signs p4600 (bank4600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4601 := params 24
abbrev ray4601 := rays 24
def bank4601 : Fin 2 → Cell := twoBank p4601 ray4601
theorem signs4601 : ∀ j, Signs p4601 (bank4601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4602 := params 25
abbrev ray4602 := rays 25
def bank4602 : Fin 2 → Cell := twoBank p4602 ray4602
theorem signs4602 : ∀ j, Signs p4602 (bank4602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4603 := params 26
abbrev ray4603 := rays 26
def bank4603 : Fin 2 → Cell := twoBank p4603 ray4603
theorem signs4603 : ∀ j, Signs p4603 (bank4603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4604 := params 27
abbrev ray4604 := rays 27
def bank4604 : Fin 2 → Cell := twoBank p4604 ray4604
theorem signs4604 : ∀ j, Signs p4604 (bank4604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4605 := params 28
abbrev ray4605 := rays 28
def bank4605 : Fin 2 → Cell := twoBank p4605 ray4605
theorem signs4605 : ∀ j, Signs p4605 (bank4605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4606 := params 29
abbrev ray4606 := rays 29
def bank4606 : Fin 2 → Cell := twoBank p4606 ray4606
theorem signs4606 : ∀ j, Signs p4606 (bank4606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4607 := params 30
abbrev ray4607 := rays 30
def bank4607 : Fin 2 → Cell := twoBank p4607 ray4607
theorem signs4607 : ∀ j, Signs p4607 (bank4607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4608 := params 31
abbrev ray4608 := rays 31
def bank4608 : Fin 2 → Cell := twoBank p4608 ray4608
theorem signs4608 : ∀ j, Signs p4608 (bank4608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04577_04608
