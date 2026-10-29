/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15425_15456
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95202969563174,95202505406753,95202041234306,95201577045834,95201112841336,95200648620813,95200184384265,95199720131692,95199255863094,95198791578471,95198327277823,95197862961150,95197398628453,95196934279731,95196469914985,95196005534214,95195541137419,95195076724600,95194612295756,95194147850888,95193683389996,95193218913080,95192754420140,95192289911176,95191825386189,95191360845178,95190896288143,95190431715085,95189967126004,95189502520899,95189037899771,95188573262620,95188108609446]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15424+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15425 := params 0
abbrev ray15425 := rays 0
def bank15425 : Fin 1 → Cell := oneBank p15425 ray15425
theorem signs15425 : ∀ j, Signs p15425 (bank15425 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15426 := params 1
abbrev ray15426 := rays 1
def bank15426 : Fin 1 → Cell := oneBank p15426 ray15426
theorem signs15426 : ∀ j, Signs p15426 (bank15426 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15427 := params 2
abbrev ray15427 := rays 2
def bank15427 : Fin 1 → Cell := oneBank p15427 ray15427
theorem signs15427 : ∀ j, Signs p15427 (bank15427 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15428 := params 3
abbrev ray15428 := rays 3
def bank15428 : Fin 1 → Cell := oneBank p15428 ray15428
theorem signs15428 : ∀ j, Signs p15428 (bank15428 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15429 := params 4
abbrev ray15429 := rays 4
def bank15429 : Fin 1 → Cell := oneBank p15429 ray15429
theorem signs15429 : ∀ j, Signs p15429 (bank15429 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15430 := params 5
abbrev ray15430 := rays 5
def bank15430 : Fin 1 → Cell := oneBank p15430 ray15430
theorem signs15430 : ∀ j, Signs p15430 (bank15430 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15431 := params 6
abbrev ray15431 := rays 6
def bank15431 : Fin 1 → Cell := oneBank p15431 ray15431
theorem signs15431 : ∀ j, Signs p15431 (bank15431 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15432 := params 7
abbrev ray15432 := rays 7
def bank15432 : Fin 1 → Cell := oneBank p15432 ray15432
theorem signs15432 : ∀ j, Signs p15432 (bank15432 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15433 := params 8
abbrev ray15433 := rays 8
def bank15433 : Fin 1 → Cell := oneBank p15433 ray15433
theorem signs15433 : ∀ j, Signs p15433 (bank15433 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15434 := params 9
abbrev ray15434 := rays 9
def bank15434 : Fin 1 → Cell := oneBank p15434 ray15434
theorem signs15434 : ∀ j, Signs p15434 (bank15434 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15435 := params 10
abbrev ray15435 := rays 10
def bank15435 : Fin 1 → Cell := oneBank p15435 ray15435
theorem signs15435 : ∀ j, Signs p15435 (bank15435 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15436 := params 11
abbrev ray15436 := rays 11
def bank15436 : Fin 1 → Cell := oneBank p15436 ray15436
theorem signs15436 : ∀ j, Signs p15436 (bank15436 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15437 := params 12
abbrev ray15437 := rays 12
def bank15437 : Fin 1 → Cell := oneBank p15437 ray15437
theorem signs15437 : ∀ j, Signs p15437 (bank15437 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15438 := params 13
abbrev ray15438 := rays 13
def bank15438 : Fin 1 → Cell := oneBank p15438 ray15438
theorem signs15438 : ∀ j, Signs p15438 (bank15438 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15439 := params 14
abbrev ray15439 := rays 14
def bank15439 : Fin 1 → Cell := oneBank p15439 ray15439
theorem signs15439 : ∀ j, Signs p15439 (bank15439 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15440 := params 15
abbrev ray15440 := rays 15
def bank15440 : Fin 1 → Cell := oneBank p15440 ray15440
theorem signs15440 : ∀ j, Signs p15440 (bank15440 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15441 := params 16
abbrev ray15441 := rays 16
def bank15441 : Fin 1 → Cell := oneBank p15441 ray15441
theorem signs15441 : ∀ j, Signs p15441 (bank15441 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15442 := params 17
abbrev ray15442 := rays 17
def bank15442 : Fin 1 → Cell := oneBank p15442 ray15442
theorem signs15442 : ∀ j, Signs p15442 (bank15442 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15443 := params 18
abbrev ray15443 := rays 18
def bank15443 : Fin 1 → Cell := oneBank p15443 ray15443
theorem signs15443 : ∀ j, Signs p15443 (bank15443 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15444 := params 19
abbrev ray15444 := rays 19
def bank15444 : Fin 1 → Cell := oneBank p15444 ray15444
theorem signs15444 : ∀ j, Signs p15444 (bank15444 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15445 := params 20
abbrev ray15445 := rays 20
def bank15445 : Fin 1 → Cell := oneBank p15445 ray15445
theorem signs15445 : ∀ j, Signs p15445 (bank15445 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15446 := params 21
abbrev ray15446 := rays 21
def bank15446 : Fin 1 → Cell := oneBank p15446 ray15446
theorem signs15446 : ∀ j, Signs p15446 (bank15446 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15447 := params 22
abbrev ray15447 := rays 22
def bank15447 : Fin 1 → Cell := oneBank p15447 ray15447
theorem signs15447 : ∀ j, Signs p15447 (bank15447 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15448 := params 23
abbrev ray15448 := rays 23
def bank15448 : Fin 1 → Cell := oneBank p15448 ray15448
theorem signs15448 : ∀ j, Signs p15448 (bank15448 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15449 := params 24
abbrev ray15449 := rays 24
def bank15449 : Fin 1 → Cell := oneBank p15449 ray15449
theorem signs15449 : ∀ j, Signs p15449 (bank15449 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15450 := params 25
abbrev ray15450 := rays 25
def bank15450 : Fin 1 → Cell := oneBank p15450 ray15450
theorem signs15450 : ∀ j, Signs p15450 (bank15450 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15451 := params 26
abbrev ray15451 := rays 26
def bank15451 : Fin 1 → Cell := oneBank p15451 ray15451
theorem signs15451 : ∀ j, Signs p15451 (bank15451 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15452 := params 27
abbrev ray15452 := rays 27
def bank15452 : Fin 1 → Cell := oneBank p15452 ray15452
theorem signs15452 : ∀ j, Signs p15452 (bank15452 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15453 := params 28
abbrev ray15453 := rays 28
def bank15453 : Fin 1 → Cell := oneBank p15453 ray15453
theorem signs15453 : ∀ j, Signs p15453 (bank15453 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15454 := params 29
abbrev ray15454 := rays 29
def bank15454 : Fin 1 → Cell := oneBank p15454 ray15454
theorem signs15454 : ∀ j, Signs p15454 (bank15454 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15455 := params 30
abbrev ray15455 := rays 30
def bank15455 : Fin 1 → Cell := oneBank p15455 ray15455
theorem signs15455 : ∀ j, Signs p15455 (bank15455 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15456 := params 31
abbrev ray15456 := rays 31
def bank15456 : Fin 1 → Cell := oneBank p15456 ray15456
theorem signs15456 : ∀ j, Signs p15456 (bank15456 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15425_15456
