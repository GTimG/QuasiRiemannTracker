/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14465_14496
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95641153126853,95640704402438,95640255661887,95639806905200,95639358132378,95638909343420,95638460538327,95638011717099,95637562879736,95637114026238,95636665156606,95636216270839,95635767368938,95635318450903,95634869516734,95634420566431,95633971599994,95633522617423,95633073618719,95632624603882,95632175572912,95631726525809,95631277462573,95630828383204,95630379287703,95629930176069,95629481048303,95629031904405,95628582744375,95628133568213,95627684375920,95627235167495,95626785942939]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14464+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14465 := params 0
abbrev ray14465 := rays 0
def bank14465 : Fin 1 → Cell := oneBank p14465 ray14465
theorem signs14465 : ∀ j, Signs p14465 (bank14465 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14466 := params 1
abbrev ray14466 := rays 1
def bank14466 : Fin 1 → Cell := oneBank p14466 ray14466
theorem signs14466 : ∀ j, Signs p14466 (bank14466 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14467 := params 2
abbrev ray14467 := rays 2
def bank14467 : Fin 1 → Cell := oneBank p14467 ray14467
theorem signs14467 : ∀ j, Signs p14467 (bank14467 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14468 := params 3
abbrev ray14468 := rays 3
def bank14468 : Fin 1 → Cell := oneBank p14468 ray14468
theorem signs14468 : ∀ j, Signs p14468 (bank14468 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14469 := params 4
abbrev ray14469 := rays 4
def bank14469 : Fin 1 → Cell := oneBank p14469 ray14469
theorem signs14469 : ∀ j, Signs p14469 (bank14469 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14470 := params 5
abbrev ray14470 := rays 5
def bank14470 : Fin 1 → Cell := oneBank p14470 ray14470
theorem signs14470 : ∀ j, Signs p14470 (bank14470 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14471 := params 6
abbrev ray14471 := rays 6
def bank14471 : Fin 1 → Cell := oneBank p14471 ray14471
theorem signs14471 : ∀ j, Signs p14471 (bank14471 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14472 := params 7
abbrev ray14472 := rays 7
def bank14472 : Fin 1 → Cell := oneBank p14472 ray14472
theorem signs14472 : ∀ j, Signs p14472 (bank14472 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14473 := params 8
abbrev ray14473 := rays 8
def bank14473 : Fin 1 → Cell := oneBank p14473 ray14473
theorem signs14473 : ∀ j, Signs p14473 (bank14473 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14474 := params 9
abbrev ray14474 := rays 9
def bank14474 : Fin 1 → Cell := oneBank p14474 ray14474
theorem signs14474 : ∀ j, Signs p14474 (bank14474 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14475 := params 10
abbrev ray14475 := rays 10
def bank14475 : Fin 1 → Cell := oneBank p14475 ray14475
theorem signs14475 : ∀ j, Signs p14475 (bank14475 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14476 := params 11
abbrev ray14476 := rays 11
def bank14476 : Fin 1 → Cell := oneBank p14476 ray14476
theorem signs14476 : ∀ j, Signs p14476 (bank14476 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14477 := params 12
abbrev ray14477 := rays 12
def bank14477 : Fin 1 → Cell := oneBank p14477 ray14477
theorem signs14477 : ∀ j, Signs p14477 (bank14477 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14478 := params 13
abbrev ray14478 := rays 13
def bank14478 : Fin 1 → Cell := oneBank p14478 ray14478
theorem signs14478 : ∀ j, Signs p14478 (bank14478 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14479 := params 14
abbrev ray14479 := rays 14
def bank14479 : Fin 1 → Cell := oneBank p14479 ray14479
theorem signs14479 : ∀ j, Signs p14479 (bank14479 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14480 := params 15
abbrev ray14480 := rays 15
def bank14480 : Fin 1 → Cell := oneBank p14480 ray14480
theorem signs14480 : ∀ j, Signs p14480 (bank14480 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14481 := params 16
abbrev ray14481 := rays 16
def bank14481 : Fin 1 → Cell := oneBank p14481 ray14481
theorem signs14481 : ∀ j, Signs p14481 (bank14481 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14482 := params 17
abbrev ray14482 := rays 17
def bank14482 : Fin 1 → Cell := oneBank p14482 ray14482
theorem signs14482 : ∀ j, Signs p14482 (bank14482 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14483 := params 18
abbrev ray14483 := rays 18
def bank14483 : Fin 1 → Cell := oneBank p14483 ray14483
theorem signs14483 : ∀ j, Signs p14483 (bank14483 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14484 := params 19
abbrev ray14484 := rays 19
def bank14484 : Fin 1 → Cell := oneBank p14484 ray14484
theorem signs14484 : ∀ j, Signs p14484 (bank14484 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14485 := params 20
abbrev ray14485 := rays 20
def bank14485 : Fin 1 → Cell := oneBank p14485 ray14485
theorem signs14485 : ∀ j, Signs p14485 (bank14485 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14486 := params 21
abbrev ray14486 := rays 21
def bank14486 : Fin 1 → Cell := oneBank p14486 ray14486
theorem signs14486 : ∀ j, Signs p14486 (bank14486 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14487 := params 22
abbrev ray14487 := rays 22
def bank14487 : Fin 1 → Cell := oneBank p14487 ray14487
theorem signs14487 : ∀ j, Signs p14487 (bank14487 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14488 := params 23
abbrev ray14488 := rays 23
def bank14488 : Fin 1 → Cell := oneBank p14488 ray14488
theorem signs14488 : ∀ j, Signs p14488 (bank14488 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14489 := params 24
abbrev ray14489 := rays 24
def bank14489 : Fin 1 → Cell := oneBank p14489 ray14489
theorem signs14489 : ∀ j, Signs p14489 (bank14489 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14490 := params 25
abbrev ray14490 := rays 25
def bank14490 : Fin 1 → Cell := oneBank p14490 ray14490
theorem signs14490 : ∀ j, Signs p14490 (bank14490 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14491 := params 26
abbrev ray14491 := rays 26
def bank14491 : Fin 1 → Cell := oneBank p14491 ray14491
theorem signs14491 : ∀ j, Signs p14491 (bank14491 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14492 := params 27
abbrev ray14492 := rays 27
def bank14492 : Fin 1 → Cell := oneBank p14492 ray14492
theorem signs14492 : ∀ j, Signs p14492 (bank14492 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14493 := params 28
abbrev ray14493 := rays 28
def bank14493 : Fin 1 → Cell := oneBank p14493 ray14493
theorem signs14493 : ∀ j, Signs p14493 (bank14493 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14494 := params 29
abbrev ray14494 := rays 29
def bank14494 : Fin 1 → Cell := oneBank p14494 ray14494
theorem signs14494 : ∀ j, Signs p14494 (bank14494 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14495 := params 30
abbrev ray14495 := rays 30
def bank14495 : Fin 1 → Cell := oneBank p14495 ray14495
theorem signs14495 : ∀ j, Signs p14495 (bank14495 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14496 := params 31
abbrev ray14496 := rays 31
def bank14496 : Fin 1 → Cell := oneBank p14496 ray14496
theorem signs14496 : ∀ j, Signs p14496 (bank14496 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14465_14496
