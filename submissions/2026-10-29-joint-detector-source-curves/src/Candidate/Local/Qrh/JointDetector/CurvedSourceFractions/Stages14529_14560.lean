/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14529_14560
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95612402240677,95611952483869,95611502710935,95611052921875,95610603116689,95610153295377,95609703457939,95609253604375,95608803734686,95608353848872,95607903946933,95607454028868,95607004094679,95606554144365,95606104177926,95605654195363,95605204196676,95604754181864,95604304150928,95603854103868,95603404040685,95602953961378,95602503865948,95602053754394,95601603626717,95601153482917,95600703322994,95600253146949,95599802954781,95599352746491,95598902522078,95598452281543,95598002024886]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14528+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14529 := params 0
abbrev ray14529 := rays 0
def bank14529 : Fin 1 → Cell := oneBank p14529 ray14529
theorem signs14529 : ∀ j, Signs p14529 (bank14529 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14530 := params 1
abbrev ray14530 := rays 1
def bank14530 : Fin 1 → Cell := oneBank p14530 ray14530
theorem signs14530 : ∀ j, Signs p14530 (bank14530 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14531 := params 2
abbrev ray14531 := rays 2
def bank14531 : Fin 1 → Cell := oneBank p14531 ray14531
theorem signs14531 : ∀ j, Signs p14531 (bank14531 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14532 := params 3
abbrev ray14532 := rays 3
def bank14532 : Fin 1 → Cell := oneBank p14532 ray14532
theorem signs14532 : ∀ j, Signs p14532 (bank14532 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14533 := params 4
abbrev ray14533 := rays 4
def bank14533 : Fin 1 → Cell := oneBank p14533 ray14533
theorem signs14533 : ∀ j, Signs p14533 (bank14533 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14534 := params 5
abbrev ray14534 := rays 5
def bank14534 : Fin 1 → Cell := oneBank p14534 ray14534
theorem signs14534 : ∀ j, Signs p14534 (bank14534 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14535 := params 6
abbrev ray14535 := rays 6
def bank14535 : Fin 1 → Cell := oneBank p14535 ray14535
theorem signs14535 : ∀ j, Signs p14535 (bank14535 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14536 := params 7
abbrev ray14536 := rays 7
def bank14536 : Fin 1 → Cell := oneBank p14536 ray14536
theorem signs14536 : ∀ j, Signs p14536 (bank14536 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14537 := params 8
abbrev ray14537 := rays 8
def bank14537 : Fin 1 → Cell := oneBank p14537 ray14537
theorem signs14537 : ∀ j, Signs p14537 (bank14537 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14538 := params 9
abbrev ray14538 := rays 9
def bank14538 : Fin 1 → Cell := oneBank p14538 ray14538
theorem signs14538 : ∀ j, Signs p14538 (bank14538 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14539 := params 10
abbrev ray14539 := rays 10
def bank14539 : Fin 1 → Cell := oneBank p14539 ray14539
theorem signs14539 : ∀ j, Signs p14539 (bank14539 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14540 := params 11
abbrev ray14540 := rays 11
def bank14540 : Fin 1 → Cell := oneBank p14540 ray14540
theorem signs14540 : ∀ j, Signs p14540 (bank14540 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14541 := params 12
abbrev ray14541 := rays 12
def bank14541 : Fin 1 → Cell := oneBank p14541 ray14541
theorem signs14541 : ∀ j, Signs p14541 (bank14541 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14542 := params 13
abbrev ray14542 := rays 13
def bank14542 : Fin 1 → Cell := oneBank p14542 ray14542
theorem signs14542 : ∀ j, Signs p14542 (bank14542 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14543 := params 14
abbrev ray14543 := rays 14
def bank14543 : Fin 1 → Cell := oneBank p14543 ray14543
theorem signs14543 : ∀ j, Signs p14543 (bank14543 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14544 := params 15
abbrev ray14544 := rays 15
def bank14544 : Fin 1 → Cell := oneBank p14544 ray14544
theorem signs14544 : ∀ j, Signs p14544 (bank14544 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14545 := params 16
abbrev ray14545 := rays 16
def bank14545 : Fin 1 → Cell := oneBank p14545 ray14545
theorem signs14545 : ∀ j, Signs p14545 (bank14545 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14546 := params 17
abbrev ray14546 := rays 17
def bank14546 : Fin 1 → Cell := oneBank p14546 ray14546
theorem signs14546 : ∀ j, Signs p14546 (bank14546 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14547 := params 18
abbrev ray14547 := rays 18
def bank14547 : Fin 1 → Cell := oneBank p14547 ray14547
theorem signs14547 : ∀ j, Signs p14547 (bank14547 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14548 := params 19
abbrev ray14548 := rays 19
def bank14548 : Fin 1 → Cell := oneBank p14548 ray14548
theorem signs14548 : ∀ j, Signs p14548 (bank14548 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14549 := params 20
abbrev ray14549 := rays 20
def bank14549 : Fin 1 → Cell := oneBank p14549 ray14549
theorem signs14549 : ∀ j, Signs p14549 (bank14549 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14550 := params 21
abbrev ray14550 := rays 21
def bank14550 : Fin 1 → Cell := oneBank p14550 ray14550
theorem signs14550 : ∀ j, Signs p14550 (bank14550 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14551 := params 22
abbrev ray14551 := rays 22
def bank14551 : Fin 1 → Cell := oneBank p14551 ray14551
theorem signs14551 : ∀ j, Signs p14551 (bank14551 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14552 := params 23
abbrev ray14552 := rays 23
def bank14552 : Fin 1 → Cell := oneBank p14552 ray14552
theorem signs14552 : ∀ j, Signs p14552 (bank14552 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14553 := params 24
abbrev ray14553 := rays 24
def bank14553 : Fin 1 → Cell := oneBank p14553 ray14553
theorem signs14553 : ∀ j, Signs p14553 (bank14553 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14554 := params 25
abbrev ray14554 := rays 25
def bank14554 : Fin 1 → Cell := oneBank p14554 ray14554
theorem signs14554 : ∀ j, Signs p14554 (bank14554 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14555 := params 26
abbrev ray14555 := rays 26
def bank14555 : Fin 1 → Cell := oneBank p14555 ray14555
theorem signs14555 : ∀ j, Signs p14555 (bank14555 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14556 := params 27
abbrev ray14556 := rays 27
def bank14556 : Fin 1 → Cell := oneBank p14556 ray14556
theorem signs14556 : ∀ j, Signs p14556 (bank14556 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14557 := params 28
abbrev ray14557 := rays 28
def bank14557 : Fin 1 → Cell := oneBank p14557 ray14557
theorem signs14557 : ∀ j, Signs p14557 (bank14557 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14558 := params 29
abbrev ray14558 := rays 29
def bank14558 : Fin 1 → Cell := oneBank p14558 ray14558
theorem signs14558 : ∀ j, Signs p14558 (bank14558 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14559 := params 30
abbrev ray14559 := rays 30
def bank14559 : Fin 1 → Cell := oneBank p14559 ray14559
theorem signs14559 : ∀ j, Signs p14559 (bank14559 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14560 := params 31
abbrev ray14560 := rays 31
def bank14560 : Fin 1 → Cell := oneBank p14560 ray14560
theorem signs14560 : ∀ j, Signs p14560 (bank14560 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14529_14560
