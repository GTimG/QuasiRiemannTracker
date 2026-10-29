/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04449_04480
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99173065601359,99172822610398,99172579594766,99172336554464,99172093489493,99171850399855,99171607285550,99171364146579,99171120982943,99170877794644,99170634581682,99170391344059,99170148081775,99169904794832,99169661483231,99169418146973,99169174786059,99168931400489,99168687990265,99168444555388,99168201095860,99167957611681,99167714102852,99167470569374,99167227011249,99166983428477,99166739821060,99166496188998,99166252532293,99166008850945,99165765144956,99165521414327,99165277659059]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4448+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4449 := params 0
abbrev ray4449 := rays 0
def bank4449 : Fin 2 → Cell := twoBank p4449 ray4449
theorem signs4449 : ∀ j, Signs p4449 (bank4449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4450 := params 1
abbrev ray4450 := rays 1
def bank4450 : Fin 2 → Cell := twoBank p4450 ray4450
theorem signs4450 : ∀ j, Signs p4450 (bank4450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4451 := params 2
abbrev ray4451 := rays 2
def bank4451 : Fin 2 → Cell := twoBank p4451 ray4451
theorem signs4451 : ∀ j, Signs p4451 (bank4451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4452 := params 3
abbrev ray4452 := rays 3
def bank4452 : Fin 2 → Cell := twoBank p4452 ray4452
theorem signs4452 : ∀ j, Signs p4452 (bank4452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4453 := params 4
abbrev ray4453 := rays 4
def bank4453 : Fin 2 → Cell := twoBank p4453 ray4453
theorem signs4453 : ∀ j, Signs p4453 (bank4453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4454 := params 5
abbrev ray4454 := rays 5
def bank4454 : Fin 2 → Cell := twoBank p4454 ray4454
theorem signs4454 : ∀ j, Signs p4454 (bank4454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4455 := params 6
abbrev ray4455 := rays 6
def bank4455 : Fin 2 → Cell := twoBank p4455 ray4455
theorem signs4455 : ∀ j, Signs p4455 (bank4455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4456 := params 7
abbrev ray4456 := rays 7
def bank4456 : Fin 2 → Cell := twoBank p4456 ray4456
theorem signs4456 : ∀ j, Signs p4456 (bank4456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4457 := params 8
abbrev ray4457 := rays 8
def bank4457 : Fin 2 → Cell := twoBank p4457 ray4457
theorem signs4457 : ∀ j, Signs p4457 (bank4457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4458 := params 9
abbrev ray4458 := rays 9
def bank4458 : Fin 2 → Cell := twoBank p4458 ray4458
theorem signs4458 : ∀ j, Signs p4458 (bank4458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4459 := params 10
abbrev ray4459 := rays 10
def bank4459 : Fin 2 → Cell := twoBank p4459 ray4459
theorem signs4459 : ∀ j, Signs p4459 (bank4459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4460 := params 11
abbrev ray4460 := rays 11
def bank4460 : Fin 2 → Cell := twoBank p4460 ray4460
theorem signs4460 : ∀ j, Signs p4460 (bank4460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4461 := params 12
abbrev ray4461 := rays 12
def bank4461 : Fin 2 → Cell := twoBank p4461 ray4461
theorem signs4461 : ∀ j, Signs p4461 (bank4461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4462 := params 13
abbrev ray4462 := rays 13
def bank4462 : Fin 2 → Cell := twoBank p4462 ray4462
theorem signs4462 : ∀ j, Signs p4462 (bank4462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4463 := params 14
abbrev ray4463 := rays 14
def bank4463 : Fin 2 → Cell := twoBank p4463 ray4463
theorem signs4463 : ∀ j, Signs p4463 (bank4463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4464 := params 15
abbrev ray4464 := rays 15
def bank4464 : Fin 2 → Cell := twoBank p4464 ray4464
theorem signs4464 : ∀ j, Signs p4464 (bank4464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4465 := params 16
abbrev ray4465 := rays 16
def bank4465 : Fin 2 → Cell := twoBank p4465 ray4465
theorem signs4465 : ∀ j, Signs p4465 (bank4465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4466 := params 17
abbrev ray4466 := rays 17
def bank4466 : Fin 2 → Cell := twoBank p4466 ray4466
theorem signs4466 : ∀ j, Signs p4466 (bank4466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4467 := params 18
abbrev ray4467 := rays 18
def bank4467 : Fin 2 → Cell := twoBank p4467 ray4467
theorem signs4467 : ∀ j, Signs p4467 (bank4467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4468 := params 19
abbrev ray4468 := rays 19
def bank4468 : Fin 2 → Cell := twoBank p4468 ray4468
theorem signs4468 : ∀ j, Signs p4468 (bank4468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4469 := params 20
abbrev ray4469 := rays 20
def bank4469 : Fin 2 → Cell := twoBank p4469 ray4469
theorem signs4469 : ∀ j, Signs p4469 (bank4469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4470 := params 21
abbrev ray4470 := rays 21
def bank4470 : Fin 2 → Cell := twoBank p4470 ray4470
theorem signs4470 : ∀ j, Signs p4470 (bank4470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4471 := params 22
abbrev ray4471 := rays 22
def bank4471 : Fin 2 → Cell := twoBank p4471 ray4471
theorem signs4471 : ∀ j, Signs p4471 (bank4471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4472 := params 23
abbrev ray4472 := rays 23
def bank4472 : Fin 2 → Cell := twoBank p4472 ray4472
theorem signs4472 : ∀ j, Signs p4472 (bank4472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4473 := params 24
abbrev ray4473 := rays 24
def bank4473 : Fin 2 → Cell := twoBank p4473 ray4473
theorem signs4473 : ∀ j, Signs p4473 (bank4473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4474 := params 25
abbrev ray4474 := rays 25
def bank4474 : Fin 2 → Cell := twoBank p4474 ray4474
theorem signs4474 : ∀ j, Signs p4474 (bank4474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4475 := params 26
abbrev ray4475 := rays 26
def bank4475 : Fin 2 → Cell := twoBank p4475 ray4475
theorem signs4475 : ∀ j, Signs p4475 (bank4475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4476 := params 27
abbrev ray4476 := rays 27
def bank4476 : Fin 2 → Cell := twoBank p4476 ray4476
theorem signs4476 : ∀ j, Signs p4476 (bank4476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4477 := params 28
abbrev ray4477 := rays 28
def bank4477 : Fin 2 → Cell := twoBank p4477 ray4477
theorem signs4477 : ∀ j, Signs p4477 (bank4477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4478 := params 29
abbrev ray4478 := rays 29
def bank4478 : Fin 2 → Cell := twoBank p4478 ray4478
theorem signs4478 : ∀ j, Signs p4478 (bank4478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4479 := params 30
abbrev ray4479 := rays 30
def bank4479 : Fin 2 → Cell := twoBank p4479 ray4479
theorem signs4479 : ∀ j, Signs p4479 (bank4479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4480 := params 31
abbrev ray4480 := rays 31
def bank4480 : Fin 2 → Cell := twoBank p4480 ray4480
theorem signs4480 : ∀ j, Signs p4480 (bank4480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04449_04480
