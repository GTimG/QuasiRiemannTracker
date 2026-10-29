/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05505_05536
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98902926367595,98902657892928,98902389394646,98902120872750,98901852327241,98901583758120,98901315165388,98901046549046,98900777909095,98900509245536,98900240558369,98899971847596,98899703113217,98899434355234,98899165573647,98898896768458,98898627939667,98898359087275,98898090211283,98897821311692,98897552388503,98897283441717,98897014471335,98896745477358,98896476459787,98896207418622,98895938353865,98895669265516,98895400153577,98895131018048,98894861858931,98894592676226,98894323469934]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5504+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5505 := params 0
abbrev ray5505 := rays 0
def bank5505 : Fin 2 → Cell := twoBank p5505 ray5505
theorem signs5505 : ∀ j, Signs p5505 (bank5505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5506 := params 1
abbrev ray5506 := rays 1
def bank5506 : Fin 2 → Cell := twoBank p5506 ray5506
theorem signs5506 : ∀ j, Signs p5506 (bank5506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5507 := params 2
abbrev ray5507 := rays 2
def bank5507 : Fin 2 → Cell := twoBank p5507 ray5507
theorem signs5507 : ∀ j, Signs p5507 (bank5507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5508 := params 3
abbrev ray5508 := rays 3
def bank5508 : Fin 2 → Cell := twoBank p5508 ray5508
theorem signs5508 : ∀ j, Signs p5508 (bank5508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5509 := params 4
abbrev ray5509 := rays 4
def bank5509 : Fin 2 → Cell := twoBank p5509 ray5509
theorem signs5509 : ∀ j, Signs p5509 (bank5509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5510 := params 5
abbrev ray5510 := rays 5
def bank5510 : Fin 2 → Cell := twoBank p5510 ray5510
theorem signs5510 : ∀ j, Signs p5510 (bank5510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5511 := params 6
abbrev ray5511 := rays 6
def bank5511 : Fin 2 → Cell := twoBank p5511 ray5511
theorem signs5511 : ∀ j, Signs p5511 (bank5511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5512 := params 7
abbrev ray5512 := rays 7
def bank5512 : Fin 2 → Cell := twoBank p5512 ray5512
theorem signs5512 : ∀ j, Signs p5512 (bank5512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5513 := params 8
abbrev ray5513 := rays 8
def bank5513 : Fin 2 → Cell := twoBank p5513 ray5513
theorem signs5513 : ∀ j, Signs p5513 (bank5513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5514 := params 9
abbrev ray5514 := rays 9
def bank5514 : Fin 2 → Cell := twoBank p5514 ray5514
theorem signs5514 : ∀ j, Signs p5514 (bank5514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5515 := params 10
abbrev ray5515 := rays 10
def bank5515 : Fin 2 → Cell := twoBank p5515 ray5515
theorem signs5515 : ∀ j, Signs p5515 (bank5515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5516 := params 11
abbrev ray5516 := rays 11
def bank5516 : Fin 2 → Cell := twoBank p5516 ray5516
theorem signs5516 : ∀ j, Signs p5516 (bank5516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5517 := params 12
abbrev ray5517 := rays 12
def bank5517 : Fin 2 → Cell := twoBank p5517 ray5517
theorem signs5517 : ∀ j, Signs p5517 (bank5517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5518 := params 13
abbrev ray5518 := rays 13
def bank5518 : Fin 2 → Cell := twoBank p5518 ray5518
theorem signs5518 : ∀ j, Signs p5518 (bank5518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5519 := params 14
abbrev ray5519 := rays 14
def bank5519 : Fin 2 → Cell := twoBank p5519 ray5519
theorem signs5519 : ∀ j, Signs p5519 (bank5519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5520 := params 15
abbrev ray5520 := rays 15
def bank5520 : Fin 2 → Cell := twoBank p5520 ray5520
theorem signs5520 : ∀ j, Signs p5520 (bank5520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5521 := params 16
abbrev ray5521 := rays 16
def bank5521 : Fin 2 → Cell := twoBank p5521 ray5521
theorem signs5521 : ∀ j, Signs p5521 (bank5521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5522 := params 17
abbrev ray5522 := rays 17
def bank5522 : Fin 2 → Cell := twoBank p5522 ray5522
theorem signs5522 : ∀ j, Signs p5522 (bank5522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5523 := params 18
abbrev ray5523 := rays 18
def bank5523 : Fin 2 → Cell := twoBank p5523 ray5523
theorem signs5523 : ∀ j, Signs p5523 (bank5523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5524 := params 19
abbrev ray5524 := rays 19
def bank5524 : Fin 2 → Cell := twoBank p5524 ray5524
theorem signs5524 : ∀ j, Signs p5524 (bank5524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5525 := params 20
abbrev ray5525 := rays 20
def bank5525 : Fin 2 → Cell := twoBank p5525 ray5525
theorem signs5525 : ∀ j, Signs p5525 (bank5525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5526 := params 21
abbrev ray5526 := rays 21
def bank5526 : Fin 2 → Cell := twoBank p5526 ray5526
theorem signs5526 : ∀ j, Signs p5526 (bank5526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5527 := params 22
abbrev ray5527 := rays 22
def bank5527 : Fin 2 → Cell := twoBank p5527 ray5527
theorem signs5527 : ∀ j, Signs p5527 (bank5527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5528 := params 23
abbrev ray5528 := rays 23
def bank5528 : Fin 2 → Cell := twoBank p5528 ray5528
theorem signs5528 : ∀ j, Signs p5528 (bank5528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5529 := params 24
abbrev ray5529 := rays 24
def bank5529 : Fin 2 → Cell := twoBank p5529 ray5529
theorem signs5529 : ∀ j, Signs p5529 (bank5529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5530 := params 25
abbrev ray5530 := rays 25
def bank5530 : Fin 2 → Cell := twoBank p5530 ray5530
theorem signs5530 : ∀ j, Signs p5530 (bank5530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5531 := params 26
abbrev ray5531 := rays 26
def bank5531 : Fin 2 → Cell := twoBank p5531 ray5531
theorem signs5531 : ∀ j, Signs p5531 (bank5531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5532 := params 27
abbrev ray5532 := rays 27
def bank5532 : Fin 2 → Cell := twoBank p5532 ray5532
theorem signs5532 : ∀ j, Signs p5532 (bank5532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5533 := params 28
abbrev ray5533 := rays 28
def bank5533 : Fin 2 → Cell := twoBank p5533 ray5533
theorem signs5533 : ∀ j, Signs p5533 (bank5533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5534 := params 29
abbrev ray5534 := rays 29
def bank5534 : Fin 2 → Cell := twoBank p5534 ray5534
theorem signs5534 : ∀ j, Signs p5534 (bank5534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5535 := params 30
abbrev ray5535 := rays 30
def bank5535 : Fin 2 → Cell := twoBank p5535 ray5535
theorem signs5535 : ∀ j, Signs p5535 (bank5535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5536 := params 31
abbrev ray5536 := rays 31
def bank5536 : Fin 2 → Cell := twoBank p5536 ray5536
theorem signs5536 : ∀ j, Signs p5536 (bank5536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05505_05536
