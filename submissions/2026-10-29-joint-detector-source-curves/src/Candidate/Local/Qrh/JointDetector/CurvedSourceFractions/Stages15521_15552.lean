/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15521_15552
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95158337481666,95157871787151,95157406076617,95156940350065,95156474607495,95156008848907,95155543074301,95155077283678,95154611477037,95154145654378,95153679815702,95153213961008,95152748090297,95152282203568,95151816300822,95151350382059,95150884447278,95150418496480,95149952529665,95149486546833,95149020547984,95148554533118,95148088502236,95147622455337,95147156392421,95146690313489,95146224218540,95145758107575,95145291980594,95144825837596,95144359678582,95143893503552,95143427312506]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15520+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15521 := params 0
abbrev ray15521 := rays 0
def bank15521 : Fin 1 → Cell := oneBank p15521 ray15521
theorem signs15521 : ∀ j, Signs p15521 (bank15521 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15522 := params 1
abbrev ray15522 := rays 1
def bank15522 : Fin 1 → Cell := oneBank p15522 ray15522
theorem signs15522 : ∀ j, Signs p15522 (bank15522 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15523 := params 2
abbrev ray15523 := rays 2
def bank15523 : Fin 1 → Cell := oneBank p15523 ray15523
theorem signs15523 : ∀ j, Signs p15523 (bank15523 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15524 := params 3
abbrev ray15524 := rays 3
def bank15524 : Fin 1 → Cell := oneBank p15524 ray15524
theorem signs15524 : ∀ j, Signs p15524 (bank15524 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15525 := params 4
abbrev ray15525 := rays 4
def bank15525 : Fin 1 → Cell := oneBank p15525 ray15525
theorem signs15525 : ∀ j, Signs p15525 (bank15525 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15526 := params 5
abbrev ray15526 := rays 5
def bank15526 : Fin 1 → Cell := oneBank p15526 ray15526
theorem signs15526 : ∀ j, Signs p15526 (bank15526 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15527 := params 6
abbrev ray15527 := rays 6
def bank15527 : Fin 1 → Cell := oneBank p15527 ray15527
theorem signs15527 : ∀ j, Signs p15527 (bank15527 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15528 := params 7
abbrev ray15528 := rays 7
def bank15528 : Fin 1 → Cell := oneBank p15528 ray15528
theorem signs15528 : ∀ j, Signs p15528 (bank15528 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15529 := params 8
abbrev ray15529 := rays 8
def bank15529 : Fin 1 → Cell := oneBank p15529 ray15529
theorem signs15529 : ∀ j, Signs p15529 (bank15529 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15530 := params 9
abbrev ray15530 := rays 9
def bank15530 : Fin 1 → Cell := oneBank p15530 ray15530
theorem signs15530 : ∀ j, Signs p15530 (bank15530 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15531 := params 10
abbrev ray15531 := rays 10
def bank15531 : Fin 1 → Cell := oneBank p15531 ray15531
theorem signs15531 : ∀ j, Signs p15531 (bank15531 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15532 := params 11
abbrev ray15532 := rays 11
def bank15532 : Fin 1 → Cell := oneBank p15532 ray15532
theorem signs15532 : ∀ j, Signs p15532 (bank15532 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15533 := params 12
abbrev ray15533 := rays 12
def bank15533 : Fin 1 → Cell := oneBank p15533 ray15533
theorem signs15533 : ∀ j, Signs p15533 (bank15533 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15534 := params 13
abbrev ray15534 := rays 13
def bank15534 : Fin 1 → Cell := oneBank p15534 ray15534
theorem signs15534 : ∀ j, Signs p15534 (bank15534 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15535 := params 14
abbrev ray15535 := rays 14
def bank15535 : Fin 1 → Cell := oneBank p15535 ray15535
theorem signs15535 : ∀ j, Signs p15535 (bank15535 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15536 := params 15
abbrev ray15536 := rays 15
def bank15536 : Fin 1 → Cell := oneBank p15536 ray15536
theorem signs15536 : ∀ j, Signs p15536 (bank15536 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15537 := params 16
abbrev ray15537 := rays 16
def bank15537 : Fin 1 → Cell := oneBank p15537 ray15537
theorem signs15537 : ∀ j, Signs p15537 (bank15537 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15538 := params 17
abbrev ray15538 := rays 17
def bank15538 : Fin 1 → Cell := oneBank p15538 ray15538
theorem signs15538 : ∀ j, Signs p15538 (bank15538 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15539 := params 18
abbrev ray15539 := rays 18
def bank15539 : Fin 1 → Cell := oneBank p15539 ray15539
theorem signs15539 : ∀ j, Signs p15539 (bank15539 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15540 := params 19
abbrev ray15540 := rays 19
def bank15540 : Fin 1 → Cell := oneBank p15540 ray15540
theorem signs15540 : ∀ j, Signs p15540 (bank15540 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15541 := params 20
abbrev ray15541 := rays 20
def bank15541 : Fin 1 → Cell := oneBank p15541 ray15541
theorem signs15541 : ∀ j, Signs p15541 (bank15541 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15542 := params 21
abbrev ray15542 := rays 21
def bank15542 : Fin 1 → Cell := oneBank p15542 ray15542
theorem signs15542 : ∀ j, Signs p15542 (bank15542 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15543 := params 22
abbrev ray15543 := rays 22
def bank15543 : Fin 1 → Cell := oneBank p15543 ray15543
theorem signs15543 : ∀ j, Signs p15543 (bank15543 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15544 := params 23
abbrev ray15544 := rays 23
def bank15544 : Fin 1 → Cell := oneBank p15544 ray15544
theorem signs15544 : ∀ j, Signs p15544 (bank15544 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15545 := params 24
abbrev ray15545 := rays 24
def bank15545 : Fin 1 → Cell := oneBank p15545 ray15545
theorem signs15545 : ∀ j, Signs p15545 (bank15545 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15546 := params 25
abbrev ray15546 := rays 25
def bank15546 : Fin 1 → Cell := oneBank p15546 ray15546
theorem signs15546 : ∀ j, Signs p15546 (bank15546 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15547 := params 26
abbrev ray15547 := rays 26
def bank15547 : Fin 1 → Cell := oneBank p15547 ray15547
theorem signs15547 : ∀ j, Signs p15547 (bank15547 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15548 := params 27
abbrev ray15548 := rays 27
def bank15548 : Fin 1 → Cell := oneBank p15548 ray15548
theorem signs15548 : ∀ j, Signs p15548 (bank15548 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15549 := params 28
abbrev ray15549 := rays 28
def bank15549 : Fin 1 → Cell := oneBank p15549 ray15549
theorem signs15549 : ∀ j, Signs p15549 (bank15549 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15550 := params 29
abbrev ray15550 := rays 29
def bank15550 : Fin 1 → Cell := oneBank p15550 ray15550
theorem signs15550 : ∀ j, Signs p15550 (bank15550 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15551 := params 30
abbrev ray15551 := rays 30
def bank15551 : Fin 1 → Cell := oneBank p15551 ray15551
theorem signs15551 : ∀ j, Signs p15551 (bank15551 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15552 := params 31
abbrev ray15552 := rays 31
def bank15552 : Fin 1 → Cell := oneBank p15552 ray15552
theorem signs15552 : ∀ j, Signs p15552 (bank15552 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15521_15552
