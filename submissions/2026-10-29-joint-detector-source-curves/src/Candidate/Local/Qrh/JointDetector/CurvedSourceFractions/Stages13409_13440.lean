/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13409_13440
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96105967253984,96105535667714,96105104065108,96104672446166,96104240810887,96103809159273,96103377491323,96102945807038,96102514106417,96102082389461,96101650656171,96101218906546,96100787140587,96100355358294,96099923559667,96099491744707,96099059913413,96098628065786,96098196201826,96097764321533,96097332424908,96096900511951,96096468582662,96096036637041,96095604675089,96095172696805,96094740702190,96094308691244,96093876663968,96093444620361,96093012560424,96092580484157,96092148391561]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13408+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13409 := params 0
abbrev ray13409 := rays 0
def bank13409 : Fin 1 → Cell := oneBank p13409 ray13409
theorem signs13409 : ∀ j, Signs p13409 (bank13409 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13410 := params 1
abbrev ray13410 := rays 1
def bank13410 : Fin 1 → Cell := oneBank p13410 ray13410
theorem signs13410 : ∀ j, Signs p13410 (bank13410 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13411 := params 2
abbrev ray13411 := rays 2
def bank13411 : Fin 1 → Cell := oneBank p13411 ray13411
theorem signs13411 : ∀ j, Signs p13411 (bank13411 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13412 := params 3
abbrev ray13412 := rays 3
def bank13412 : Fin 1 → Cell := oneBank p13412 ray13412
theorem signs13412 : ∀ j, Signs p13412 (bank13412 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13413 := params 4
abbrev ray13413 := rays 4
def bank13413 : Fin 1 → Cell := oneBank p13413 ray13413
theorem signs13413 : ∀ j, Signs p13413 (bank13413 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13414 := params 5
abbrev ray13414 := rays 5
def bank13414 : Fin 1 → Cell := oneBank p13414 ray13414
theorem signs13414 : ∀ j, Signs p13414 (bank13414 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13415 := params 6
abbrev ray13415 := rays 6
def bank13415 : Fin 1 → Cell := oneBank p13415 ray13415
theorem signs13415 : ∀ j, Signs p13415 (bank13415 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13416 := params 7
abbrev ray13416 := rays 7
def bank13416 : Fin 1 → Cell := oneBank p13416 ray13416
theorem signs13416 : ∀ j, Signs p13416 (bank13416 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13417 := params 8
abbrev ray13417 := rays 8
def bank13417 : Fin 1 → Cell := oneBank p13417 ray13417
theorem signs13417 : ∀ j, Signs p13417 (bank13417 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13418 := params 9
abbrev ray13418 := rays 9
def bank13418 : Fin 1 → Cell := oneBank p13418 ray13418
theorem signs13418 : ∀ j, Signs p13418 (bank13418 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13419 := params 10
abbrev ray13419 := rays 10
def bank13419 : Fin 1 → Cell := oneBank p13419 ray13419
theorem signs13419 : ∀ j, Signs p13419 (bank13419 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13420 := params 11
abbrev ray13420 := rays 11
def bank13420 : Fin 1 → Cell := oneBank p13420 ray13420
theorem signs13420 : ∀ j, Signs p13420 (bank13420 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13421 := params 12
abbrev ray13421 := rays 12
def bank13421 : Fin 1 → Cell := oneBank p13421 ray13421
theorem signs13421 : ∀ j, Signs p13421 (bank13421 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13422 := params 13
abbrev ray13422 := rays 13
def bank13422 : Fin 1 → Cell := oneBank p13422 ray13422
theorem signs13422 : ∀ j, Signs p13422 (bank13422 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13423 := params 14
abbrev ray13423 := rays 14
def bank13423 : Fin 1 → Cell := oneBank p13423 ray13423
theorem signs13423 : ∀ j, Signs p13423 (bank13423 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13424 := params 15
abbrev ray13424 := rays 15
def bank13424 : Fin 1 → Cell := oneBank p13424 ray13424
theorem signs13424 : ∀ j, Signs p13424 (bank13424 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13425 := params 16
abbrev ray13425 := rays 16
def bank13425 : Fin 1 → Cell := oneBank p13425 ray13425
theorem signs13425 : ∀ j, Signs p13425 (bank13425 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13426 := params 17
abbrev ray13426 := rays 17
def bank13426 : Fin 1 → Cell := oneBank p13426 ray13426
theorem signs13426 : ∀ j, Signs p13426 (bank13426 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13427 := params 18
abbrev ray13427 := rays 18
def bank13427 : Fin 1 → Cell := oneBank p13427 ray13427
theorem signs13427 : ∀ j, Signs p13427 (bank13427 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13428 := params 19
abbrev ray13428 := rays 19
def bank13428 : Fin 1 → Cell := oneBank p13428 ray13428
theorem signs13428 : ∀ j, Signs p13428 (bank13428 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13429 := params 20
abbrev ray13429 := rays 20
def bank13429 : Fin 1 → Cell := oneBank p13429 ray13429
theorem signs13429 : ∀ j, Signs p13429 (bank13429 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13430 := params 21
abbrev ray13430 := rays 21
def bank13430 : Fin 1 → Cell := oneBank p13430 ray13430
theorem signs13430 : ∀ j, Signs p13430 (bank13430 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13431 := params 22
abbrev ray13431 := rays 22
def bank13431 : Fin 1 → Cell := oneBank p13431 ray13431
theorem signs13431 : ∀ j, Signs p13431 (bank13431 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13432 := params 23
abbrev ray13432 := rays 23
def bank13432 : Fin 1 → Cell := oneBank p13432 ray13432
theorem signs13432 : ∀ j, Signs p13432 (bank13432 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13433 := params 24
abbrev ray13433 := rays 24
def bank13433 : Fin 1 → Cell := oneBank p13433 ray13433
theorem signs13433 : ∀ j, Signs p13433 (bank13433 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13434 := params 25
abbrev ray13434 := rays 25
def bank13434 : Fin 1 → Cell := oneBank p13434 ray13434
theorem signs13434 : ∀ j, Signs p13434 (bank13434 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13435 := params 26
abbrev ray13435 := rays 26
def bank13435 : Fin 1 → Cell := oneBank p13435 ray13435
theorem signs13435 : ∀ j, Signs p13435 (bank13435 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13436 := params 27
abbrev ray13436 := rays 27
def bank13436 : Fin 1 → Cell := oneBank p13436 ray13436
theorem signs13436 : ∀ j, Signs p13436 (bank13436 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13437 := params 28
abbrev ray13437 := rays 28
def bank13437 : Fin 1 → Cell := oneBank p13437 ray13437
theorem signs13437 : ∀ j, Signs p13437 (bank13437 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13438 := params 29
abbrev ray13438 := rays 29
def bank13438 : Fin 1 → Cell := oneBank p13438 ray13438
theorem signs13438 : ∀ j, Signs p13438 (bank13438 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13439 := params 30
abbrev ray13439 := rays 30
def bank13439 : Fin 1 → Cell := oneBank p13439 ray13439
theorem signs13439 : ∀ j, Signs p13439 (bank13439 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13440 := params 31
abbrev ray13440 := rays 31
def bank13440 : Fin 1 → Cell := oneBank p13440 ray13440
theorem signs13440 : ∀ j, Signs p13440 (bank13440 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13409_13440
