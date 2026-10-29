/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06433_06464
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98643745694385,98643455694347,98643165671519,98642875625902,98642585557496,98642295466302,98642005352322,98641715215556,98641425056004,98641134873668,98640844668549,98640554440647,98640264189963,98639973916498,98639683620253,98639393301229,98639102959426,98638812594846,98638522207489,98638231797356,98637941364448,98637650908766,98637360430311,98637069929083,98636779405083,98636488858312,98636198288771,98635907696461,98635617081383,98635326443537,98635035782925,98634745099547,98634454393404]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6432+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6433 := params 0
abbrev ray6433 := rays 0
def bank6433 : Fin 2 → Cell := twoBank p6433 ray6433
theorem signs6433 : ∀ j, Signs p6433 (bank6433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6434 := params 1
abbrev ray6434 := rays 1
def bank6434 : Fin 2 → Cell := twoBank p6434 ray6434
theorem signs6434 : ∀ j, Signs p6434 (bank6434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6435 := params 2
abbrev ray6435 := rays 2
def bank6435 : Fin 2 → Cell := twoBank p6435 ray6435
theorem signs6435 : ∀ j, Signs p6435 (bank6435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6436 := params 3
abbrev ray6436 := rays 3
def bank6436 : Fin 2 → Cell := twoBank p6436 ray6436
theorem signs6436 : ∀ j, Signs p6436 (bank6436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6437 := params 4
abbrev ray6437 := rays 4
def bank6437 : Fin 2 → Cell := twoBank p6437 ray6437
theorem signs6437 : ∀ j, Signs p6437 (bank6437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6438 := params 5
abbrev ray6438 := rays 5
def bank6438 : Fin 2 → Cell := twoBank p6438 ray6438
theorem signs6438 : ∀ j, Signs p6438 (bank6438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6439 := params 6
abbrev ray6439 := rays 6
def bank6439 : Fin 2 → Cell := twoBank p6439 ray6439
theorem signs6439 : ∀ j, Signs p6439 (bank6439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6440 := params 7
abbrev ray6440 := rays 7
def bank6440 : Fin 2 → Cell := twoBank p6440 ray6440
theorem signs6440 : ∀ j, Signs p6440 (bank6440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6441 := params 8
abbrev ray6441 := rays 8
def bank6441 : Fin 2 → Cell := twoBank p6441 ray6441
theorem signs6441 : ∀ j, Signs p6441 (bank6441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6442 := params 9
abbrev ray6442 := rays 9
def bank6442 : Fin 2 → Cell := twoBank p6442 ray6442
theorem signs6442 : ∀ j, Signs p6442 (bank6442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6443 := params 10
abbrev ray6443 := rays 10
def bank6443 : Fin 2 → Cell := twoBank p6443 ray6443
theorem signs6443 : ∀ j, Signs p6443 (bank6443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6444 := params 11
abbrev ray6444 := rays 11
def bank6444 : Fin 2 → Cell := twoBank p6444 ray6444
theorem signs6444 : ∀ j, Signs p6444 (bank6444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6445 := params 12
abbrev ray6445 := rays 12
def bank6445 : Fin 2 → Cell := twoBank p6445 ray6445
theorem signs6445 : ∀ j, Signs p6445 (bank6445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6446 := params 13
abbrev ray6446 := rays 13
def bank6446 : Fin 2 → Cell := twoBank p6446 ray6446
theorem signs6446 : ∀ j, Signs p6446 (bank6446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6447 := params 14
abbrev ray6447 := rays 14
def bank6447 : Fin 2 → Cell := twoBank p6447 ray6447
theorem signs6447 : ∀ j, Signs p6447 (bank6447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6448 := params 15
abbrev ray6448 := rays 15
def bank6448 : Fin 2 → Cell := twoBank p6448 ray6448
theorem signs6448 : ∀ j, Signs p6448 (bank6448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6449 := params 16
abbrev ray6449 := rays 16
def bank6449 : Fin 2 → Cell := twoBank p6449 ray6449
theorem signs6449 : ∀ j, Signs p6449 (bank6449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6450 := params 17
abbrev ray6450 := rays 17
def bank6450 : Fin 2 → Cell := twoBank p6450 ray6450
theorem signs6450 : ∀ j, Signs p6450 (bank6450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6451 := params 18
abbrev ray6451 := rays 18
def bank6451 : Fin 2 → Cell := twoBank p6451 ray6451
theorem signs6451 : ∀ j, Signs p6451 (bank6451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6452 := params 19
abbrev ray6452 := rays 19
def bank6452 : Fin 2 → Cell := twoBank p6452 ray6452
theorem signs6452 : ∀ j, Signs p6452 (bank6452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6453 := params 20
abbrev ray6453 := rays 20
def bank6453 : Fin 2 → Cell := twoBank p6453 ray6453
theorem signs6453 : ∀ j, Signs p6453 (bank6453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6454 := params 21
abbrev ray6454 := rays 21
def bank6454 : Fin 2 → Cell := twoBank p6454 ray6454
theorem signs6454 : ∀ j, Signs p6454 (bank6454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6455 := params 22
abbrev ray6455 := rays 22
def bank6455 : Fin 2 → Cell := twoBank p6455 ray6455
theorem signs6455 : ∀ j, Signs p6455 (bank6455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6456 := params 23
abbrev ray6456 := rays 23
def bank6456 : Fin 2 → Cell := twoBank p6456 ray6456
theorem signs6456 : ∀ j, Signs p6456 (bank6456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6457 := params 24
abbrev ray6457 := rays 24
def bank6457 : Fin 2 → Cell := twoBank p6457 ray6457
theorem signs6457 : ∀ j, Signs p6457 (bank6457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6458 := params 25
abbrev ray6458 := rays 25
def bank6458 : Fin 2 → Cell := twoBank p6458 ray6458
theorem signs6458 : ∀ j, Signs p6458 (bank6458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6459 := params 26
abbrev ray6459 := rays 26
def bank6459 : Fin 2 → Cell := twoBank p6459 ray6459
theorem signs6459 : ∀ j, Signs p6459 (bank6459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6460 := params 27
abbrev ray6460 := rays 27
def bank6460 : Fin 2 → Cell := twoBank p6460 ray6460
theorem signs6460 : ∀ j, Signs p6460 (bank6460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6461 := params 28
abbrev ray6461 := rays 28
def bank6461 : Fin 2 → Cell := twoBank p6461 ray6461
theorem signs6461 : ∀ j, Signs p6461 (bank6461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6462 := params 29
abbrev ray6462 := rays 29
def bank6462 : Fin 2 → Cell := twoBank p6462 ray6462
theorem signs6462 : ∀ j, Signs p6462 (bank6462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6463 := params 30
abbrev ray6463 := rays 30
def bank6463 : Fin 2 → Cell := twoBank p6463 ray6463
theorem signs6463 : ∀ j, Signs p6463 (bank6463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6464 := params 31
abbrev ray6464 := rays 31
def bank6464 : Fin 2 → Cell := twoBank p6464 ray6464
theorem signs6464 : ∀ j, Signs p6464 (bank6464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06433_06464
