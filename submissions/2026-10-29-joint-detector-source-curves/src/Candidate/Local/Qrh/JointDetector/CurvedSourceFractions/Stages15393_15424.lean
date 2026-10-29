/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15393_15424
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95217814106735,95217350463171,95216886803579,95216423127959,95215959436311,95215495728635,95215032004931,95214568265200,95214104509441,95213640737655,95213176949841,95212713146000,95212249326132,95211785490237,95211321638315,95210857770366,95210393886390,95209929986387,95209466070357,95209002138300,95208538190217,95208074226107,95207610245971,95207146249809,95206682237620,95206218209405,95205754165164,95205290104897,95204826028604,95204361936285,95203897827940,95203433703570,95202969563174]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15392+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15393 := params 0
abbrev ray15393 := rays 0
def bank15393 : Fin 1 → Cell := oneBank p15393 ray15393
theorem signs15393 : ∀ j, Signs p15393 (bank15393 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15394 := params 1
abbrev ray15394 := rays 1
def bank15394 : Fin 1 → Cell := oneBank p15394 ray15394
theorem signs15394 : ∀ j, Signs p15394 (bank15394 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15395 := params 2
abbrev ray15395 := rays 2
def bank15395 : Fin 1 → Cell := oneBank p15395 ray15395
theorem signs15395 : ∀ j, Signs p15395 (bank15395 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15396 := params 3
abbrev ray15396 := rays 3
def bank15396 : Fin 1 → Cell := oneBank p15396 ray15396
theorem signs15396 : ∀ j, Signs p15396 (bank15396 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15397 := params 4
abbrev ray15397 := rays 4
def bank15397 : Fin 1 → Cell := oneBank p15397 ray15397
theorem signs15397 : ∀ j, Signs p15397 (bank15397 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15398 := params 5
abbrev ray15398 := rays 5
def bank15398 : Fin 1 → Cell := oneBank p15398 ray15398
theorem signs15398 : ∀ j, Signs p15398 (bank15398 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15399 := params 6
abbrev ray15399 := rays 6
def bank15399 : Fin 1 → Cell := oneBank p15399 ray15399
theorem signs15399 : ∀ j, Signs p15399 (bank15399 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15400 := params 7
abbrev ray15400 := rays 7
def bank15400 : Fin 1 → Cell := oneBank p15400 ray15400
theorem signs15400 : ∀ j, Signs p15400 (bank15400 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15401 := params 8
abbrev ray15401 := rays 8
def bank15401 : Fin 1 → Cell := oneBank p15401 ray15401
theorem signs15401 : ∀ j, Signs p15401 (bank15401 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15402 := params 9
abbrev ray15402 := rays 9
def bank15402 : Fin 1 → Cell := oneBank p15402 ray15402
theorem signs15402 : ∀ j, Signs p15402 (bank15402 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15403 := params 10
abbrev ray15403 := rays 10
def bank15403 : Fin 1 → Cell := oneBank p15403 ray15403
theorem signs15403 : ∀ j, Signs p15403 (bank15403 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15404 := params 11
abbrev ray15404 := rays 11
def bank15404 : Fin 1 → Cell := oneBank p15404 ray15404
theorem signs15404 : ∀ j, Signs p15404 (bank15404 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15405 := params 12
abbrev ray15405 := rays 12
def bank15405 : Fin 1 → Cell := oneBank p15405 ray15405
theorem signs15405 : ∀ j, Signs p15405 (bank15405 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15406 := params 13
abbrev ray15406 := rays 13
def bank15406 : Fin 1 → Cell := oneBank p15406 ray15406
theorem signs15406 : ∀ j, Signs p15406 (bank15406 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15407 := params 14
abbrev ray15407 := rays 14
def bank15407 : Fin 1 → Cell := oneBank p15407 ray15407
theorem signs15407 : ∀ j, Signs p15407 (bank15407 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15408 := params 15
abbrev ray15408 := rays 15
def bank15408 : Fin 1 → Cell := oneBank p15408 ray15408
theorem signs15408 : ∀ j, Signs p15408 (bank15408 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15409 := params 16
abbrev ray15409 := rays 16
def bank15409 : Fin 1 → Cell := oneBank p15409 ray15409
theorem signs15409 : ∀ j, Signs p15409 (bank15409 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15410 := params 17
abbrev ray15410 := rays 17
def bank15410 : Fin 1 → Cell := oneBank p15410 ray15410
theorem signs15410 : ∀ j, Signs p15410 (bank15410 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15411 := params 18
abbrev ray15411 := rays 18
def bank15411 : Fin 1 → Cell := oneBank p15411 ray15411
theorem signs15411 : ∀ j, Signs p15411 (bank15411 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15412 := params 19
abbrev ray15412 := rays 19
def bank15412 : Fin 1 → Cell := oneBank p15412 ray15412
theorem signs15412 : ∀ j, Signs p15412 (bank15412 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15413 := params 20
abbrev ray15413 := rays 20
def bank15413 : Fin 1 → Cell := oneBank p15413 ray15413
theorem signs15413 : ∀ j, Signs p15413 (bank15413 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15414 := params 21
abbrev ray15414 := rays 21
def bank15414 : Fin 1 → Cell := oneBank p15414 ray15414
theorem signs15414 : ∀ j, Signs p15414 (bank15414 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15415 := params 22
abbrev ray15415 := rays 22
def bank15415 : Fin 1 → Cell := oneBank p15415 ray15415
theorem signs15415 : ∀ j, Signs p15415 (bank15415 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15416 := params 23
abbrev ray15416 := rays 23
def bank15416 : Fin 1 → Cell := oneBank p15416 ray15416
theorem signs15416 : ∀ j, Signs p15416 (bank15416 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15417 := params 24
abbrev ray15417 := rays 24
def bank15417 : Fin 1 → Cell := oneBank p15417 ray15417
theorem signs15417 : ∀ j, Signs p15417 (bank15417 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15418 := params 25
abbrev ray15418 := rays 25
def bank15418 : Fin 1 → Cell := oneBank p15418 ray15418
theorem signs15418 : ∀ j, Signs p15418 (bank15418 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15419 := params 26
abbrev ray15419 := rays 26
def bank15419 : Fin 1 → Cell := oneBank p15419 ray15419
theorem signs15419 : ∀ j, Signs p15419 (bank15419 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15420 := params 27
abbrev ray15420 := rays 27
def bank15420 : Fin 1 → Cell := oneBank p15420 ray15420
theorem signs15420 : ∀ j, Signs p15420 (bank15420 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15421 := params 28
abbrev ray15421 := rays 28
def bank15421 : Fin 1 → Cell := oneBank p15421 ray15421
theorem signs15421 : ∀ j, Signs p15421 (bank15421 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15422 := params 29
abbrev ray15422 := rays 29
def bank15422 : Fin 1 → Cell := oneBank p15422 ray15422
theorem signs15422 : ∀ j, Signs p15422 (bank15422 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15423 := params 30
abbrev ray15423 := rays 30
def bank15423 : Fin 1 → Cell := oneBank p15423 ray15423
theorem signs15423 : ∀ j, Signs p15423 (bank15423 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15424 := params 31
abbrev ray15424 := rays 31
def bank15424 : Fin 1 → Cell := oneBank p15424 ray15424
theorem signs15424 : ∀ j, Signs p15424 (bank15424 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15393_15424
