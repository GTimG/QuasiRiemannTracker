/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14401_14432
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95669837919978,95669390228572,95668942521020,95668494797323,95668047057480,95667599301492,95667151529359,95666703741081,95666255936659,95665808116092,95665360279381,95664912426526,95664464557527,95664016672384,95663568771097,95663120853666,95662672920092,95662224970375,95661777004514,95661329022511,95660881024365,95660433010076,95659984979644,95659536933070,95659088870354,95658640791496,95658192696496,95657744585354,95657296458071,95656848314646,95656400155080,95655951979373,95655503787525]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14400+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14401 := params 0
abbrev ray14401 := rays 0
def bank14401 : Fin 1 → Cell := oneBank p14401 ray14401
theorem signs14401 : ∀ j, Signs p14401 (bank14401 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14402 := params 1
abbrev ray14402 := rays 1
def bank14402 : Fin 1 → Cell := oneBank p14402 ray14402
theorem signs14402 : ∀ j, Signs p14402 (bank14402 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14403 := params 2
abbrev ray14403 := rays 2
def bank14403 : Fin 1 → Cell := oneBank p14403 ray14403
theorem signs14403 : ∀ j, Signs p14403 (bank14403 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14404 := params 3
abbrev ray14404 := rays 3
def bank14404 : Fin 1 → Cell := oneBank p14404 ray14404
theorem signs14404 : ∀ j, Signs p14404 (bank14404 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14405 := params 4
abbrev ray14405 := rays 4
def bank14405 : Fin 1 → Cell := oneBank p14405 ray14405
theorem signs14405 : ∀ j, Signs p14405 (bank14405 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14406 := params 5
abbrev ray14406 := rays 5
def bank14406 : Fin 1 → Cell := oneBank p14406 ray14406
theorem signs14406 : ∀ j, Signs p14406 (bank14406 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14407 := params 6
abbrev ray14407 := rays 6
def bank14407 : Fin 1 → Cell := oneBank p14407 ray14407
theorem signs14407 : ∀ j, Signs p14407 (bank14407 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14408 := params 7
abbrev ray14408 := rays 7
def bank14408 : Fin 1 → Cell := oneBank p14408 ray14408
theorem signs14408 : ∀ j, Signs p14408 (bank14408 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14409 := params 8
abbrev ray14409 := rays 8
def bank14409 : Fin 1 → Cell := oneBank p14409 ray14409
theorem signs14409 : ∀ j, Signs p14409 (bank14409 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14410 := params 9
abbrev ray14410 := rays 9
def bank14410 : Fin 1 → Cell := oneBank p14410 ray14410
theorem signs14410 : ∀ j, Signs p14410 (bank14410 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14411 := params 10
abbrev ray14411 := rays 10
def bank14411 : Fin 1 → Cell := oneBank p14411 ray14411
theorem signs14411 : ∀ j, Signs p14411 (bank14411 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14412 := params 11
abbrev ray14412 := rays 11
def bank14412 : Fin 1 → Cell := oneBank p14412 ray14412
theorem signs14412 : ∀ j, Signs p14412 (bank14412 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14413 := params 12
abbrev ray14413 := rays 12
def bank14413 : Fin 1 → Cell := oneBank p14413 ray14413
theorem signs14413 : ∀ j, Signs p14413 (bank14413 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14414 := params 13
abbrev ray14414 := rays 13
def bank14414 : Fin 1 → Cell := oneBank p14414 ray14414
theorem signs14414 : ∀ j, Signs p14414 (bank14414 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14415 := params 14
abbrev ray14415 := rays 14
def bank14415 : Fin 1 → Cell := oneBank p14415 ray14415
theorem signs14415 : ∀ j, Signs p14415 (bank14415 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14416 := params 15
abbrev ray14416 := rays 15
def bank14416 : Fin 1 → Cell := oneBank p14416 ray14416
theorem signs14416 : ∀ j, Signs p14416 (bank14416 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14417 := params 16
abbrev ray14417 := rays 16
def bank14417 : Fin 1 → Cell := oneBank p14417 ray14417
theorem signs14417 : ∀ j, Signs p14417 (bank14417 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14418 := params 17
abbrev ray14418 := rays 17
def bank14418 : Fin 1 → Cell := oneBank p14418 ray14418
theorem signs14418 : ∀ j, Signs p14418 (bank14418 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14419 := params 18
abbrev ray14419 := rays 18
def bank14419 : Fin 1 → Cell := oneBank p14419 ray14419
theorem signs14419 : ∀ j, Signs p14419 (bank14419 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14420 := params 19
abbrev ray14420 := rays 19
def bank14420 : Fin 1 → Cell := oneBank p14420 ray14420
theorem signs14420 : ∀ j, Signs p14420 (bank14420 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14421 := params 20
abbrev ray14421 := rays 20
def bank14421 : Fin 1 → Cell := oneBank p14421 ray14421
theorem signs14421 : ∀ j, Signs p14421 (bank14421 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14422 := params 21
abbrev ray14422 := rays 21
def bank14422 : Fin 1 → Cell := oneBank p14422 ray14422
theorem signs14422 : ∀ j, Signs p14422 (bank14422 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14423 := params 22
abbrev ray14423 := rays 22
def bank14423 : Fin 1 → Cell := oneBank p14423 ray14423
theorem signs14423 : ∀ j, Signs p14423 (bank14423 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14424 := params 23
abbrev ray14424 := rays 23
def bank14424 : Fin 1 → Cell := oneBank p14424 ray14424
theorem signs14424 : ∀ j, Signs p14424 (bank14424 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14425 := params 24
abbrev ray14425 := rays 24
def bank14425 : Fin 1 → Cell := oneBank p14425 ray14425
theorem signs14425 : ∀ j, Signs p14425 (bank14425 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14426 := params 25
abbrev ray14426 := rays 25
def bank14426 : Fin 1 → Cell := oneBank p14426 ray14426
theorem signs14426 : ∀ j, Signs p14426 (bank14426 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14427 := params 26
abbrev ray14427 := rays 26
def bank14427 : Fin 1 → Cell := oneBank p14427 ray14427
theorem signs14427 : ∀ j, Signs p14427 (bank14427 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14428 := params 27
abbrev ray14428 := rays 27
def bank14428 : Fin 1 → Cell := oneBank p14428 ray14428
theorem signs14428 : ∀ j, Signs p14428 (bank14428 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14429 := params 28
abbrev ray14429 := rays 28
def bank14429 : Fin 1 → Cell := oneBank p14429 ray14429
theorem signs14429 : ∀ j, Signs p14429 (bank14429 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14430 := params 29
abbrev ray14430 := rays 29
def bank14430 : Fin 1 → Cell := oneBank p14430 ray14430
theorem signs14430 : ∀ j, Signs p14430 (bank14430 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14431 := params 30
abbrev ray14431 := rays 30
def bank14431 : Fin 1 → Cell := oneBank p14431 ray14431
theorem signs14431 : ∀ j, Signs p14431 (bank14431 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14432 := params 31
abbrev ray14432 := rays 31
def bank14432 : Fin 1 → Cell := oneBank p14432 ray14432
theorem signs14432 : ∀ j, Signs p14432 (bank14432 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14401_14432
