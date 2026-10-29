/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14497_14528
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95626785942939,95626336702252,95625887445434,95625438172485,95624988883405,95624539578194,95624090256853,95623640919382,95623191565780,95622742196048,95622292810187,95621843408196,95621393990075,95620944555825,95620495105446,95620045638937,95619596156299,95619146657533,95618697142638,95618247611614,95617798064462,95617348501182,95616898921774,95616449326238,95615999714574,95615550086782,95615100442863,95614650782816,95614201106642,95613751414341,95613301705913,95612851981358,95612402240677]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14496+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14497 := params 0
abbrev ray14497 := rays 0
def bank14497 : Fin 1 → Cell := oneBank p14497 ray14497
theorem signs14497 : ∀ j, Signs p14497 (bank14497 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14498 := params 1
abbrev ray14498 := rays 1
def bank14498 : Fin 1 → Cell := oneBank p14498 ray14498
theorem signs14498 : ∀ j, Signs p14498 (bank14498 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14499 := params 2
abbrev ray14499 := rays 2
def bank14499 : Fin 1 → Cell := oneBank p14499 ray14499
theorem signs14499 : ∀ j, Signs p14499 (bank14499 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14500 := params 3
abbrev ray14500 := rays 3
def bank14500 : Fin 1 → Cell := oneBank p14500 ray14500
theorem signs14500 : ∀ j, Signs p14500 (bank14500 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14501 := params 4
abbrev ray14501 := rays 4
def bank14501 : Fin 1 → Cell := oneBank p14501 ray14501
theorem signs14501 : ∀ j, Signs p14501 (bank14501 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14502 := params 5
abbrev ray14502 := rays 5
def bank14502 : Fin 1 → Cell := oneBank p14502 ray14502
theorem signs14502 : ∀ j, Signs p14502 (bank14502 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14503 := params 6
abbrev ray14503 := rays 6
def bank14503 : Fin 1 → Cell := oneBank p14503 ray14503
theorem signs14503 : ∀ j, Signs p14503 (bank14503 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14504 := params 7
abbrev ray14504 := rays 7
def bank14504 : Fin 1 → Cell := oneBank p14504 ray14504
theorem signs14504 : ∀ j, Signs p14504 (bank14504 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14505 := params 8
abbrev ray14505 := rays 8
def bank14505 : Fin 1 → Cell := oneBank p14505 ray14505
theorem signs14505 : ∀ j, Signs p14505 (bank14505 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14506 := params 9
abbrev ray14506 := rays 9
def bank14506 : Fin 1 → Cell := oneBank p14506 ray14506
theorem signs14506 : ∀ j, Signs p14506 (bank14506 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14507 := params 10
abbrev ray14507 := rays 10
def bank14507 : Fin 1 → Cell := oneBank p14507 ray14507
theorem signs14507 : ∀ j, Signs p14507 (bank14507 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14508 := params 11
abbrev ray14508 := rays 11
def bank14508 : Fin 1 → Cell := oneBank p14508 ray14508
theorem signs14508 : ∀ j, Signs p14508 (bank14508 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14509 := params 12
abbrev ray14509 := rays 12
def bank14509 : Fin 1 → Cell := oneBank p14509 ray14509
theorem signs14509 : ∀ j, Signs p14509 (bank14509 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14510 := params 13
abbrev ray14510 := rays 13
def bank14510 : Fin 1 → Cell := oneBank p14510 ray14510
theorem signs14510 : ∀ j, Signs p14510 (bank14510 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14511 := params 14
abbrev ray14511 := rays 14
def bank14511 : Fin 1 → Cell := oneBank p14511 ray14511
theorem signs14511 : ∀ j, Signs p14511 (bank14511 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14512 := params 15
abbrev ray14512 := rays 15
def bank14512 : Fin 1 → Cell := oneBank p14512 ray14512
theorem signs14512 : ∀ j, Signs p14512 (bank14512 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14513 := params 16
abbrev ray14513 := rays 16
def bank14513 : Fin 1 → Cell := oneBank p14513 ray14513
theorem signs14513 : ∀ j, Signs p14513 (bank14513 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14514 := params 17
abbrev ray14514 := rays 17
def bank14514 : Fin 1 → Cell := oneBank p14514 ray14514
theorem signs14514 : ∀ j, Signs p14514 (bank14514 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14515 := params 18
abbrev ray14515 := rays 18
def bank14515 : Fin 1 → Cell := oneBank p14515 ray14515
theorem signs14515 : ∀ j, Signs p14515 (bank14515 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14516 := params 19
abbrev ray14516 := rays 19
def bank14516 : Fin 1 → Cell := oneBank p14516 ray14516
theorem signs14516 : ∀ j, Signs p14516 (bank14516 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14517 := params 20
abbrev ray14517 := rays 20
def bank14517 : Fin 1 → Cell := oneBank p14517 ray14517
theorem signs14517 : ∀ j, Signs p14517 (bank14517 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14518 := params 21
abbrev ray14518 := rays 21
def bank14518 : Fin 1 → Cell := oneBank p14518 ray14518
theorem signs14518 : ∀ j, Signs p14518 (bank14518 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14519 := params 22
abbrev ray14519 := rays 22
def bank14519 : Fin 1 → Cell := oneBank p14519 ray14519
theorem signs14519 : ∀ j, Signs p14519 (bank14519 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14520 := params 23
abbrev ray14520 := rays 23
def bank14520 : Fin 1 → Cell := oneBank p14520 ray14520
theorem signs14520 : ∀ j, Signs p14520 (bank14520 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14521 := params 24
abbrev ray14521 := rays 24
def bank14521 : Fin 1 → Cell := oneBank p14521 ray14521
theorem signs14521 : ∀ j, Signs p14521 (bank14521 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14522 := params 25
abbrev ray14522 := rays 25
def bank14522 : Fin 1 → Cell := oneBank p14522 ray14522
theorem signs14522 : ∀ j, Signs p14522 (bank14522 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14523 := params 26
abbrev ray14523 := rays 26
def bank14523 : Fin 1 → Cell := oneBank p14523 ray14523
theorem signs14523 : ∀ j, Signs p14523 (bank14523 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14524 := params 27
abbrev ray14524 := rays 27
def bank14524 : Fin 1 → Cell := oneBank p14524 ray14524
theorem signs14524 : ∀ j, Signs p14524 (bank14524 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14525 := params 28
abbrev ray14525 := rays 28
def bank14525 : Fin 1 → Cell := oneBank p14525 ray14525
theorem signs14525 : ∀ j, Signs p14525 (bank14525 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14526 := params 29
abbrev ray14526 := rays 29
def bank14526 : Fin 1 → Cell := oneBank p14526 ray14526
theorem signs14526 : ∀ j, Signs p14526 (bank14526 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14527 := params 30
abbrev ray14527 := rays 30
def bank14527 : Fin 1 → Cell := oneBank p14527 ray14527
theorem signs14527 : ∀ j, Signs p14527 (bank14527 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14528 := params 31
abbrev ray14528 := rays 31
def bank14528 : Fin 1 → Cell := oneBank p14528 ray14528
theorem signs14528 : ∀ j, Signs p14528 (bank14528 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14497_14528
