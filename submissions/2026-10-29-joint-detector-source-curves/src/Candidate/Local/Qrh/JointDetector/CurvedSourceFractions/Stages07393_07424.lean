/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07393_07424
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98354975100473,98354663594866,98354352067232,98354040517572,98353728945887,98353417352178,98353105736445,98352794098690,98352482438913,98352170757114,98351859053295,98351547327456,98351235579598,98350923809722,98350612017828,98350300203917,98349988367990,98349676510048,98349364630091,98349052728121,98348740804138,98348428858142,98348116890135,98347804900117,98347492888089,98347180854052,98346868798006,98346556719952,98346244619891,98345932497824,98345620353751,98345308187674,98344995999592]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7392+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7393 := params 0
abbrev ray7393 := rays 0
def bank7393 : Fin 2 → Cell := twoBank p7393 ray7393
theorem signs7393 : ∀ j, Signs p7393 (bank7393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7394 := params 1
abbrev ray7394 := rays 1
def bank7394 : Fin 2 → Cell := twoBank p7394 ray7394
theorem signs7394 : ∀ j, Signs p7394 (bank7394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7395 := params 2
abbrev ray7395 := rays 2
def bank7395 : Fin 2 → Cell := twoBank p7395 ray7395
theorem signs7395 : ∀ j, Signs p7395 (bank7395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7396 := params 3
abbrev ray7396 := rays 3
def bank7396 : Fin 2 → Cell := twoBank p7396 ray7396
theorem signs7396 : ∀ j, Signs p7396 (bank7396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7397 := params 4
abbrev ray7397 := rays 4
def bank7397 : Fin 2 → Cell := twoBank p7397 ray7397
theorem signs7397 : ∀ j, Signs p7397 (bank7397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7398 := params 5
abbrev ray7398 := rays 5
def bank7398 : Fin 2 → Cell := twoBank p7398 ray7398
theorem signs7398 : ∀ j, Signs p7398 (bank7398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7399 := params 6
abbrev ray7399 := rays 6
def bank7399 : Fin 2 → Cell := twoBank p7399 ray7399
theorem signs7399 : ∀ j, Signs p7399 (bank7399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7400 := params 7
abbrev ray7400 := rays 7
def bank7400 : Fin 2 → Cell := twoBank p7400 ray7400
theorem signs7400 : ∀ j, Signs p7400 (bank7400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7401 := params 8
abbrev ray7401 := rays 8
def bank7401 : Fin 2 → Cell := twoBank p7401 ray7401
theorem signs7401 : ∀ j, Signs p7401 (bank7401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7402 := params 9
abbrev ray7402 := rays 9
def bank7402 : Fin 2 → Cell := twoBank p7402 ray7402
theorem signs7402 : ∀ j, Signs p7402 (bank7402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7403 := params 10
abbrev ray7403 := rays 10
def bank7403 : Fin 2 → Cell := twoBank p7403 ray7403
theorem signs7403 : ∀ j, Signs p7403 (bank7403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7404 := params 11
abbrev ray7404 := rays 11
def bank7404 : Fin 2 → Cell := twoBank p7404 ray7404
theorem signs7404 : ∀ j, Signs p7404 (bank7404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7405 := params 12
abbrev ray7405 := rays 12
def bank7405 : Fin 2 → Cell := twoBank p7405 ray7405
theorem signs7405 : ∀ j, Signs p7405 (bank7405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7406 := params 13
abbrev ray7406 := rays 13
def bank7406 : Fin 2 → Cell := twoBank p7406 ray7406
theorem signs7406 : ∀ j, Signs p7406 (bank7406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7407 := params 14
abbrev ray7407 := rays 14
def bank7407 : Fin 2 → Cell := twoBank p7407 ray7407
theorem signs7407 : ∀ j, Signs p7407 (bank7407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7408 := params 15
abbrev ray7408 := rays 15
def bank7408 : Fin 2 → Cell := twoBank p7408 ray7408
theorem signs7408 : ∀ j, Signs p7408 (bank7408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7409 := params 16
abbrev ray7409 := rays 16
def bank7409 : Fin 2 → Cell := twoBank p7409 ray7409
theorem signs7409 : ∀ j, Signs p7409 (bank7409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7410 := params 17
abbrev ray7410 := rays 17
def bank7410 : Fin 2 → Cell := twoBank p7410 ray7410
theorem signs7410 : ∀ j, Signs p7410 (bank7410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7411 := params 18
abbrev ray7411 := rays 18
def bank7411 : Fin 2 → Cell := twoBank p7411 ray7411
theorem signs7411 : ∀ j, Signs p7411 (bank7411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7412 := params 19
abbrev ray7412 := rays 19
def bank7412 : Fin 2 → Cell := twoBank p7412 ray7412
theorem signs7412 : ∀ j, Signs p7412 (bank7412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7413 := params 20
abbrev ray7413 := rays 20
def bank7413 : Fin 2 → Cell := twoBank p7413 ray7413
theorem signs7413 : ∀ j, Signs p7413 (bank7413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7414 := params 21
abbrev ray7414 := rays 21
def bank7414 : Fin 2 → Cell := twoBank p7414 ray7414
theorem signs7414 : ∀ j, Signs p7414 (bank7414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7415 := params 22
abbrev ray7415 := rays 22
def bank7415 : Fin 2 → Cell := twoBank p7415 ray7415
theorem signs7415 : ∀ j, Signs p7415 (bank7415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7416 := params 23
abbrev ray7416 := rays 23
def bank7416 : Fin 2 → Cell := twoBank p7416 ray7416
theorem signs7416 : ∀ j, Signs p7416 (bank7416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7417 := params 24
abbrev ray7417 := rays 24
def bank7417 : Fin 2 → Cell := twoBank p7417 ray7417
theorem signs7417 : ∀ j, Signs p7417 (bank7417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7418 := params 25
abbrev ray7418 := rays 25
def bank7418 : Fin 2 → Cell := twoBank p7418 ray7418
theorem signs7418 : ∀ j, Signs p7418 (bank7418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7419 := params 26
abbrev ray7419 := rays 26
def bank7419 : Fin 2 → Cell := twoBank p7419 ray7419
theorem signs7419 : ∀ j, Signs p7419 (bank7419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7420 := params 27
abbrev ray7420 := rays 27
def bank7420 : Fin 2 → Cell := twoBank p7420 ray7420
theorem signs7420 : ∀ j, Signs p7420 (bank7420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7421 := params 28
abbrev ray7421 := rays 28
def bank7421 : Fin 2 → Cell := twoBank p7421 ray7421
theorem signs7421 : ∀ j, Signs p7421 (bank7421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7422 := params 29
abbrev ray7422 := rays 29
def bank7422 : Fin 2 → Cell := twoBank p7422 ray7422
theorem signs7422 : ∀ j, Signs p7422 (bank7422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7423 := params 30
abbrev ray7423 := rays 30
def bank7423 : Fin 2 → Cell := twoBank p7423 ray7423
theorem signs7423 : ∀ j, Signs p7423 (bank7423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7424 := params 31
abbrev ray7424 := rays 31
def bank7424 : Fin 2 → Cell := twoBank p7424 ray7424
theorem signs7424 : ∀ j, Signs p7424 (bank7424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07393_07424
