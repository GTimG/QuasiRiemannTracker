/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16449_16480
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94719290387251,94718809848972,94718329294709,94717848724463,94717368138233,94716887536020,94716406917823,94715926283643,94715445633480,94714964967333,94714484285203,94714003587089,94713522872992,94713042142912,94712561396848,94712080634801,94711599856770,94711119062756,94710638252759,94710157426778,94709676584814,94709195726866,94708714852935,94708233963021,94707753057123,94707272135242,94706791197378,94706310243530,94705829273699,94705348287884,94704867286086,94704386268305,94703905234540]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16448+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16449 := params 0
abbrev ray16449 := rays 0
def bank16449 : Fin 1 → Cell := oneBank p16449 ray16449
theorem signs16449 : ∀ j, Signs p16449 (bank16449 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16450 := params 1
abbrev ray16450 := rays 1
def bank16450 : Fin 1 → Cell := oneBank p16450 ray16450
theorem signs16450 : ∀ j, Signs p16450 (bank16450 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16451 := params 2
abbrev ray16451 := rays 2
def bank16451 : Fin 1 → Cell := oneBank p16451 ray16451
theorem signs16451 : ∀ j, Signs p16451 (bank16451 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16452 := params 3
abbrev ray16452 := rays 3
def bank16452 : Fin 1 → Cell := oneBank p16452 ray16452
theorem signs16452 : ∀ j, Signs p16452 (bank16452 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16453 := params 4
abbrev ray16453 := rays 4
def bank16453 : Fin 1 → Cell := oneBank p16453 ray16453
theorem signs16453 : ∀ j, Signs p16453 (bank16453 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16454 := params 5
abbrev ray16454 := rays 5
def bank16454 : Fin 1 → Cell := oneBank p16454 ray16454
theorem signs16454 : ∀ j, Signs p16454 (bank16454 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16455 := params 6
abbrev ray16455 := rays 6
def bank16455 : Fin 1 → Cell := oneBank p16455 ray16455
theorem signs16455 : ∀ j, Signs p16455 (bank16455 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16456 := params 7
abbrev ray16456 := rays 7
def bank16456 : Fin 1 → Cell := oneBank p16456 ray16456
theorem signs16456 : ∀ j, Signs p16456 (bank16456 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16457 := params 8
abbrev ray16457 := rays 8
def bank16457 : Fin 1 → Cell := oneBank p16457 ray16457
theorem signs16457 : ∀ j, Signs p16457 (bank16457 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16458 := params 9
abbrev ray16458 := rays 9
def bank16458 : Fin 1 → Cell := oneBank p16458 ray16458
theorem signs16458 : ∀ j, Signs p16458 (bank16458 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16459 := params 10
abbrev ray16459 := rays 10
def bank16459 : Fin 1 → Cell := oneBank p16459 ray16459
theorem signs16459 : ∀ j, Signs p16459 (bank16459 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16460 := params 11
abbrev ray16460 := rays 11
def bank16460 : Fin 1 → Cell := oneBank p16460 ray16460
theorem signs16460 : ∀ j, Signs p16460 (bank16460 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16461 := params 12
abbrev ray16461 := rays 12
def bank16461 : Fin 1 → Cell := oneBank p16461 ray16461
theorem signs16461 : ∀ j, Signs p16461 (bank16461 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16462 := params 13
abbrev ray16462 := rays 13
def bank16462 : Fin 1 → Cell := oneBank p16462 ray16462
theorem signs16462 : ∀ j, Signs p16462 (bank16462 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16463 := params 14
abbrev ray16463 := rays 14
def bank16463 : Fin 1 → Cell := oneBank p16463 ray16463
theorem signs16463 : ∀ j, Signs p16463 (bank16463 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16464 := params 15
abbrev ray16464 := rays 15
def bank16464 : Fin 1 → Cell := oneBank p16464 ray16464
theorem signs16464 : ∀ j, Signs p16464 (bank16464 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16465 := params 16
abbrev ray16465 := rays 16
def bank16465 : Fin 1 → Cell := oneBank p16465 ray16465
theorem signs16465 : ∀ j, Signs p16465 (bank16465 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16466 := params 17
abbrev ray16466 := rays 17
def bank16466 : Fin 1 → Cell := oneBank p16466 ray16466
theorem signs16466 : ∀ j, Signs p16466 (bank16466 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16467 := params 18
abbrev ray16467 := rays 18
def bank16467 : Fin 1 → Cell := oneBank p16467 ray16467
theorem signs16467 : ∀ j, Signs p16467 (bank16467 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16468 := params 19
abbrev ray16468 := rays 19
def bank16468 : Fin 1 → Cell := oneBank p16468 ray16468
theorem signs16468 : ∀ j, Signs p16468 (bank16468 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16469 := params 20
abbrev ray16469 := rays 20
def bank16469 : Fin 1 → Cell := oneBank p16469 ray16469
theorem signs16469 : ∀ j, Signs p16469 (bank16469 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16470 := params 21
abbrev ray16470 := rays 21
def bank16470 : Fin 1 → Cell := oneBank p16470 ray16470
theorem signs16470 : ∀ j, Signs p16470 (bank16470 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16471 := params 22
abbrev ray16471 := rays 22
def bank16471 : Fin 1 → Cell := oneBank p16471 ray16471
theorem signs16471 : ∀ j, Signs p16471 (bank16471 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16472 := params 23
abbrev ray16472 := rays 23
def bank16472 : Fin 1 → Cell := oneBank p16472 ray16472
theorem signs16472 : ∀ j, Signs p16472 (bank16472 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16473 := params 24
abbrev ray16473 := rays 24
def bank16473 : Fin 1 → Cell := oneBank p16473 ray16473
theorem signs16473 : ∀ j, Signs p16473 (bank16473 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16474 := params 25
abbrev ray16474 := rays 25
def bank16474 : Fin 1 → Cell := oneBank p16474 ray16474
theorem signs16474 : ∀ j, Signs p16474 (bank16474 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16475 := params 26
abbrev ray16475 := rays 26
def bank16475 : Fin 1 → Cell := oneBank p16475 ray16475
theorem signs16475 : ∀ j, Signs p16475 (bank16475 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16476 := params 27
abbrev ray16476 := rays 27
def bank16476 : Fin 1 → Cell := oneBank p16476 ray16476
theorem signs16476 : ∀ j, Signs p16476 (bank16476 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16477 := params 28
abbrev ray16477 := rays 28
def bank16477 : Fin 1 → Cell := oneBank p16477 ray16477
theorem signs16477 : ∀ j, Signs p16477 (bank16477 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16478 := params 29
abbrev ray16478 := rays 29
def bank16478 : Fin 1 → Cell := oneBank p16478 ray16478
theorem signs16478 : ∀ j, Signs p16478 (bank16478 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16479 := params 30
abbrev ray16479 := rays 30
def bank16479 : Fin 1 → Cell := oneBank p16479 ray16479
theorem signs16479 : ∀ j, Signs p16479 (bank16479 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16480 := params 31
abbrev ray16480 := rays 31
def bank16480 : Fin 1 → Cell := oneBank p16480 ray16480
theorem signs16480 : ∀ j, Signs p16480 (bank16480 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16449_16480
