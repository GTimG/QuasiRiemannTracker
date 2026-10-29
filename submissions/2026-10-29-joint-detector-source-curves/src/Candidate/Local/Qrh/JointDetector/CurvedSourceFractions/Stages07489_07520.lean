/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07489_07520
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98324970228166,98324656611424,98324342972727,98324029312076,98323715629472,98323401924915,98323088198406,98322774449946,98322460679536,98322146887176,98321833072867,98321519236610,98321205378406,98320891498255,98320577596158,98320263672116,98319949726130,98319635758200,98319321768327,98319007756512,98318693722756,98318379667059,98318065589422,98317751489846,98317437368331,98317123224879,98316809059490,98316494872164,98316180662903,98315866431707,98315552178577,98315237903514,98314923606518]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7488+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7489 := params 0
abbrev ray7489 := rays 0
def bank7489 : Fin 2 → Cell := twoBank p7489 ray7489
theorem signs7489 : ∀ j, Signs p7489 (bank7489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7490 := params 1
abbrev ray7490 := rays 1
def bank7490 : Fin 2 → Cell := twoBank p7490 ray7490
theorem signs7490 : ∀ j, Signs p7490 (bank7490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7491 := params 2
abbrev ray7491 := rays 2
def bank7491 : Fin 2 → Cell := twoBank p7491 ray7491
theorem signs7491 : ∀ j, Signs p7491 (bank7491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7492 := params 3
abbrev ray7492 := rays 3
def bank7492 : Fin 2 → Cell := twoBank p7492 ray7492
theorem signs7492 : ∀ j, Signs p7492 (bank7492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7493 := params 4
abbrev ray7493 := rays 4
def bank7493 : Fin 2 → Cell := twoBank p7493 ray7493
theorem signs7493 : ∀ j, Signs p7493 (bank7493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7494 := params 5
abbrev ray7494 := rays 5
def bank7494 : Fin 2 → Cell := twoBank p7494 ray7494
theorem signs7494 : ∀ j, Signs p7494 (bank7494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7495 := params 6
abbrev ray7495 := rays 6
def bank7495 : Fin 2 → Cell := twoBank p7495 ray7495
theorem signs7495 : ∀ j, Signs p7495 (bank7495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7496 := params 7
abbrev ray7496 := rays 7
def bank7496 : Fin 2 → Cell := twoBank p7496 ray7496
theorem signs7496 : ∀ j, Signs p7496 (bank7496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7497 := params 8
abbrev ray7497 := rays 8
def bank7497 : Fin 2 → Cell := twoBank p7497 ray7497
theorem signs7497 : ∀ j, Signs p7497 (bank7497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7498 := params 9
abbrev ray7498 := rays 9
def bank7498 : Fin 2 → Cell := twoBank p7498 ray7498
theorem signs7498 : ∀ j, Signs p7498 (bank7498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7499 := params 10
abbrev ray7499 := rays 10
def bank7499 : Fin 2 → Cell := twoBank p7499 ray7499
theorem signs7499 : ∀ j, Signs p7499 (bank7499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7500 := params 11
abbrev ray7500 := rays 11
def bank7500 : Fin 2 → Cell := twoBank p7500 ray7500
theorem signs7500 : ∀ j, Signs p7500 (bank7500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7501 := params 12
abbrev ray7501 := rays 12
def bank7501 : Fin 2 → Cell := twoBank p7501 ray7501
theorem signs7501 : ∀ j, Signs p7501 (bank7501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7502 := params 13
abbrev ray7502 := rays 13
def bank7502 : Fin 2 → Cell := twoBank p7502 ray7502
theorem signs7502 : ∀ j, Signs p7502 (bank7502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7503 := params 14
abbrev ray7503 := rays 14
def bank7503 : Fin 2 → Cell := twoBank p7503 ray7503
theorem signs7503 : ∀ j, Signs p7503 (bank7503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7504 := params 15
abbrev ray7504 := rays 15
def bank7504 : Fin 2 → Cell := twoBank p7504 ray7504
theorem signs7504 : ∀ j, Signs p7504 (bank7504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7505 := params 16
abbrev ray7505 := rays 16
def bank7505 : Fin 2 → Cell := twoBank p7505 ray7505
theorem signs7505 : ∀ j, Signs p7505 (bank7505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7506 := params 17
abbrev ray7506 := rays 17
def bank7506 : Fin 2 → Cell := twoBank p7506 ray7506
theorem signs7506 : ∀ j, Signs p7506 (bank7506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7507 := params 18
abbrev ray7507 := rays 18
def bank7507 : Fin 2 → Cell := twoBank p7507 ray7507
theorem signs7507 : ∀ j, Signs p7507 (bank7507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7508 := params 19
abbrev ray7508 := rays 19
def bank7508 : Fin 2 → Cell := twoBank p7508 ray7508
theorem signs7508 : ∀ j, Signs p7508 (bank7508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7509 := params 20
abbrev ray7509 := rays 20
def bank7509 : Fin 2 → Cell := twoBank p7509 ray7509
theorem signs7509 : ∀ j, Signs p7509 (bank7509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7510 := params 21
abbrev ray7510 := rays 21
def bank7510 : Fin 2 → Cell := twoBank p7510 ray7510
theorem signs7510 : ∀ j, Signs p7510 (bank7510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7511 := params 22
abbrev ray7511 := rays 22
def bank7511 : Fin 2 → Cell := twoBank p7511 ray7511
theorem signs7511 : ∀ j, Signs p7511 (bank7511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7512 := params 23
abbrev ray7512 := rays 23
def bank7512 : Fin 2 → Cell := twoBank p7512 ray7512
theorem signs7512 : ∀ j, Signs p7512 (bank7512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7513 := params 24
abbrev ray7513 := rays 24
def bank7513 : Fin 2 → Cell := twoBank p7513 ray7513
theorem signs7513 : ∀ j, Signs p7513 (bank7513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7514 := params 25
abbrev ray7514 := rays 25
def bank7514 : Fin 2 → Cell := twoBank p7514 ray7514
theorem signs7514 : ∀ j, Signs p7514 (bank7514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7515 := params 26
abbrev ray7515 := rays 26
def bank7515 : Fin 2 → Cell := twoBank p7515 ray7515
theorem signs7515 : ∀ j, Signs p7515 (bank7515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7516 := params 27
abbrev ray7516 := rays 27
def bank7516 : Fin 2 → Cell := twoBank p7516 ray7516
theorem signs7516 : ∀ j, Signs p7516 (bank7516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7517 := params 28
abbrev ray7517 := rays 28
def bank7517 : Fin 2 → Cell := twoBank p7517 ray7517
theorem signs7517 : ∀ j, Signs p7517 (bank7517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7518 := params 29
abbrev ray7518 := rays 29
def bank7518 : Fin 2 → Cell := twoBank p7518 ray7518
theorem signs7518 : ∀ j, Signs p7518 (bank7518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7519 := params 30
abbrev ray7519 := rays 30
def bank7519 : Fin 2 → Cell := twoBank p7519 ray7519
theorem signs7519 : ∀ j, Signs p7519 (bank7519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7520 := params 31
abbrev ray7520 := rays 31
def bank7520 : Fin 2 → Cell := twoBank p7520 ray7520
theorem signs7520 : ∀ j, Signs p7520 (bank7520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07489_07520
