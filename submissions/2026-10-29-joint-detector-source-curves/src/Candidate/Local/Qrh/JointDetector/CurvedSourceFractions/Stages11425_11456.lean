/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11425_11456
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96927309648237,96926914582490,96926519497130,96926124392157,96925729267572,96925334123375,96924938959567,96924543776148,96924148573119,96923753350480,96923358108232,96922962846375,96922567564909,96922172263836,96921776943155,96921381602867,96920986242972,96920590863471,96920195464365,96919800045653,96919404607337,96919009149416,96918613671892,96918218174764,96917822658033,96917427121700,96917031565765,96916635990229,96916240395092,96915844780354,96915449146016,96915053492078,96914657818541]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11424+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11425 := params 0
abbrev ray11425 := rays 0
def bank11425 : Fin 2 → Cell := twoBank p11425 ray11425
theorem signs11425 : ∀ j, Signs p11425 (bank11425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11426 := params 1
abbrev ray11426 := rays 1
def bank11426 : Fin 2 → Cell := twoBank p11426 ray11426
theorem signs11426 : ∀ j, Signs p11426 (bank11426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11427 := params 2
abbrev ray11427 := rays 2
def bank11427 : Fin 2 → Cell := twoBank p11427 ray11427
theorem signs11427 : ∀ j, Signs p11427 (bank11427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11428 := params 3
abbrev ray11428 := rays 3
def bank11428 : Fin 2 → Cell := twoBank p11428 ray11428
theorem signs11428 : ∀ j, Signs p11428 (bank11428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11429 := params 4
abbrev ray11429 := rays 4
def bank11429 : Fin 2 → Cell := twoBank p11429 ray11429
theorem signs11429 : ∀ j, Signs p11429 (bank11429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11430 := params 5
abbrev ray11430 := rays 5
def bank11430 : Fin 2 → Cell := twoBank p11430 ray11430
theorem signs11430 : ∀ j, Signs p11430 (bank11430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11431 := params 6
abbrev ray11431 := rays 6
def bank11431 : Fin 2 → Cell := twoBank p11431 ray11431
theorem signs11431 : ∀ j, Signs p11431 (bank11431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11432 := params 7
abbrev ray11432 := rays 7
def bank11432 : Fin 2 → Cell := twoBank p11432 ray11432
theorem signs11432 : ∀ j, Signs p11432 (bank11432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11433 := params 8
abbrev ray11433 := rays 8
def bank11433 : Fin 2 → Cell := twoBank p11433 ray11433
theorem signs11433 : ∀ j, Signs p11433 (bank11433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11434 := params 9
abbrev ray11434 := rays 9
def bank11434 : Fin 2 → Cell := twoBank p11434 ray11434
theorem signs11434 : ∀ j, Signs p11434 (bank11434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11435 := params 10
abbrev ray11435 := rays 10
def bank11435 : Fin 2 → Cell := twoBank p11435 ray11435
theorem signs11435 : ∀ j, Signs p11435 (bank11435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11436 := params 11
abbrev ray11436 := rays 11
def bank11436 : Fin 2 → Cell := twoBank p11436 ray11436
theorem signs11436 : ∀ j, Signs p11436 (bank11436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11437 := params 12
abbrev ray11437 := rays 12
def bank11437 : Fin 2 → Cell := twoBank p11437 ray11437
theorem signs11437 : ∀ j, Signs p11437 (bank11437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11438 := params 13
abbrev ray11438 := rays 13
def bank11438 : Fin 2 → Cell := twoBank p11438 ray11438
theorem signs11438 : ∀ j, Signs p11438 (bank11438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11439 := params 14
abbrev ray11439 := rays 14
def bank11439 : Fin 2 → Cell := twoBank p11439 ray11439
theorem signs11439 : ∀ j, Signs p11439 (bank11439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11440 := params 15
abbrev ray11440 := rays 15
def bank11440 : Fin 2 → Cell := twoBank p11440 ray11440
theorem signs11440 : ∀ j, Signs p11440 (bank11440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11441 := params 16
abbrev ray11441 := rays 16
def bank11441 : Fin 2 → Cell := twoBank p11441 ray11441
theorem signs11441 : ∀ j, Signs p11441 (bank11441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11442 := params 17
abbrev ray11442 := rays 17
def bank11442 : Fin 2 → Cell := twoBank p11442 ray11442
theorem signs11442 : ∀ j, Signs p11442 (bank11442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11443 := params 18
abbrev ray11443 := rays 18
def bank11443 : Fin 2 → Cell := twoBank p11443 ray11443
theorem signs11443 : ∀ j, Signs p11443 (bank11443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11444 := params 19
abbrev ray11444 := rays 19
def bank11444 : Fin 2 → Cell := twoBank p11444 ray11444
theorem signs11444 : ∀ j, Signs p11444 (bank11444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11445 := params 20
abbrev ray11445 := rays 20
def bank11445 : Fin 2 → Cell := twoBank p11445 ray11445
theorem signs11445 : ∀ j, Signs p11445 (bank11445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11446 := params 21
abbrev ray11446 := rays 21
def bank11446 : Fin 2 → Cell := twoBank p11446 ray11446
theorem signs11446 : ∀ j, Signs p11446 (bank11446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11447 := params 22
abbrev ray11447 := rays 22
def bank11447 : Fin 2 → Cell := twoBank p11447 ray11447
theorem signs11447 : ∀ j, Signs p11447 (bank11447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11448 := params 23
abbrev ray11448 := rays 23
def bank11448 : Fin 2 → Cell := twoBank p11448 ray11448
theorem signs11448 : ∀ j, Signs p11448 (bank11448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11449 := params 24
abbrev ray11449 := rays 24
def bank11449 : Fin 2 → Cell := twoBank p11449 ray11449
theorem signs11449 : ∀ j, Signs p11449 (bank11449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11450 := params 25
abbrev ray11450 := rays 25
def bank11450 : Fin 2 → Cell := twoBank p11450 ray11450
theorem signs11450 : ∀ j, Signs p11450 (bank11450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11451 := params 26
abbrev ray11451 := rays 26
def bank11451 : Fin 2 → Cell := twoBank p11451 ray11451
theorem signs11451 : ∀ j, Signs p11451 (bank11451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11452 := params 27
abbrev ray11452 := rays 27
def bank11452 : Fin 2 → Cell := twoBank p11452 ray11452
theorem signs11452 : ∀ j, Signs p11452 (bank11452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11453 := params 28
abbrev ray11453 := rays 28
def bank11453 : Fin 2 → Cell := twoBank p11453 ray11453
theorem signs11453 : ∀ j, Signs p11453 (bank11453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11454 := params 29
abbrev ray11454 := rays 29
def bank11454 : Fin 2 → Cell := twoBank p11454 ray11454
theorem signs11454 : ∀ j, Signs p11454 (bank11454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11455 := params 30
abbrev ray11455 := rays 30
def bank11455 : Fin 2 → Cell := twoBank p11455 ray11455
theorem signs11455 : ∀ j, Signs p11455 (bank11455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11456 := params 31
abbrev ray11456 := rays 31
def bank11456 : Fin 2 → Cell := twoBank p11456 ray11456
theorem signs11456 : ∀ j, Signs p11456 (bank11456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11425_11456
