/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04417_04448
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99180828279402,99180586078478,99180343852849,99180101602516,99179859327480,99179617027742,99179374703303,99179132354164,99178889980326,99178647581790,99178405158558,99178162710630,99177920238008,99177677740692,99177435218684,99177192671985,99176950100595,99176707504516,99176464883749,99176222238295,99175979568155,99175736873330,99175494153821,99175251409630,99175008640757,99174765847203,99174523028970,99174280186058,99174037318469,99173794426203,99173551509262,99173308567647,99173065601359]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4416+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4417 := params 0
abbrev ray4417 := rays 0
def bank4417 : Fin 2 → Cell := twoBank p4417 ray4417
theorem signs4417 : ∀ j, Signs p4417 (bank4417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4418 := params 1
abbrev ray4418 := rays 1
def bank4418 : Fin 2 → Cell := twoBank p4418 ray4418
theorem signs4418 : ∀ j, Signs p4418 (bank4418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4419 := params 2
abbrev ray4419 := rays 2
def bank4419 : Fin 2 → Cell := twoBank p4419 ray4419
theorem signs4419 : ∀ j, Signs p4419 (bank4419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4420 := params 3
abbrev ray4420 := rays 3
def bank4420 : Fin 2 → Cell := twoBank p4420 ray4420
theorem signs4420 : ∀ j, Signs p4420 (bank4420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4421 := params 4
abbrev ray4421 := rays 4
def bank4421 : Fin 2 → Cell := twoBank p4421 ray4421
theorem signs4421 : ∀ j, Signs p4421 (bank4421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4422 := params 5
abbrev ray4422 := rays 5
def bank4422 : Fin 2 → Cell := twoBank p4422 ray4422
theorem signs4422 : ∀ j, Signs p4422 (bank4422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4423 := params 6
abbrev ray4423 := rays 6
def bank4423 : Fin 2 → Cell := twoBank p4423 ray4423
theorem signs4423 : ∀ j, Signs p4423 (bank4423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4424 := params 7
abbrev ray4424 := rays 7
def bank4424 : Fin 2 → Cell := twoBank p4424 ray4424
theorem signs4424 : ∀ j, Signs p4424 (bank4424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4425 := params 8
abbrev ray4425 := rays 8
def bank4425 : Fin 2 → Cell := twoBank p4425 ray4425
theorem signs4425 : ∀ j, Signs p4425 (bank4425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4426 := params 9
abbrev ray4426 := rays 9
def bank4426 : Fin 2 → Cell := twoBank p4426 ray4426
theorem signs4426 : ∀ j, Signs p4426 (bank4426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4427 := params 10
abbrev ray4427 := rays 10
def bank4427 : Fin 2 → Cell := twoBank p4427 ray4427
theorem signs4427 : ∀ j, Signs p4427 (bank4427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4428 := params 11
abbrev ray4428 := rays 11
def bank4428 : Fin 2 → Cell := twoBank p4428 ray4428
theorem signs4428 : ∀ j, Signs p4428 (bank4428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4429 := params 12
abbrev ray4429 := rays 12
def bank4429 : Fin 2 → Cell := twoBank p4429 ray4429
theorem signs4429 : ∀ j, Signs p4429 (bank4429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4430 := params 13
abbrev ray4430 := rays 13
def bank4430 : Fin 2 → Cell := twoBank p4430 ray4430
theorem signs4430 : ∀ j, Signs p4430 (bank4430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4431 := params 14
abbrev ray4431 := rays 14
def bank4431 : Fin 2 → Cell := twoBank p4431 ray4431
theorem signs4431 : ∀ j, Signs p4431 (bank4431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4432 := params 15
abbrev ray4432 := rays 15
def bank4432 : Fin 2 → Cell := twoBank p4432 ray4432
theorem signs4432 : ∀ j, Signs p4432 (bank4432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4433 := params 16
abbrev ray4433 := rays 16
def bank4433 : Fin 2 → Cell := twoBank p4433 ray4433
theorem signs4433 : ∀ j, Signs p4433 (bank4433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4434 := params 17
abbrev ray4434 := rays 17
def bank4434 : Fin 2 → Cell := twoBank p4434 ray4434
theorem signs4434 : ∀ j, Signs p4434 (bank4434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4435 := params 18
abbrev ray4435 := rays 18
def bank4435 : Fin 2 → Cell := twoBank p4435 ray4435
theorem signs4435 : ∀ j, Signs p4435 (bank4435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4436 := params 19
abbrev ray4436 := rays 19
def bank4436 : Fin 2 → Cell := twoBank p4436 ray4436
theorem signs4436 : ∀ j, Signs p4436 (bank4436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4437 := params 20
abbrev ray4437 := rays 20
def bank4437 : Fin 2 → Cell := twoBank p4437 ray4437
theorem signs4437 : ∀ j, Signs p4437 (bank4437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4438 := params 21
abbrev ray4438 := rays 21
def bank4438 : Fin 2 → Cell := twoBank p4438 ray4438
theorem signs4438 : ∀ j, Signs p4438 (bank4438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4439 := params 22
abbrev ray4439 := rays 22
def bank4439 : Fin 2 → Cell := twoBank p4439 ray4439
theorem signs4439 : ∀ j, Signs p4439 (bank4439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4440 := params 23
abbrev ray4440 := rays 23
def bank4440 : Fin 2 → Cell := twoBank p4440 ray4440
theorem signs4440 : ∀ j, Signs p4440 (bank4440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4441 := params 24
abbrev ray4441 := rays 24
def bank4441 : Fin 2 → Cell := twoBank p4441 ray4441
theorem signs4441 : ∀ j, Signs p4441 (bank4441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4442 := params 25
abbrev ray4442 := rays 25
def bank4442 : Fin 2 → Cell := twoBank p4442 ray4442
theorem signs4442 : ∀ j, Signs p4442 (bank4442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4443 := params 26
abbrev ray4443 := rays 26
def bank4443 : Fin 2 → Cell := twoBank p4443 ray4443
theorem signs4443 : ∀ j, Signs p4443 (bank4443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4444 := params 27
abbrev ray4444 := rays 27
def bank4444 : Fin 2 → Cell := twoBank p4444 ray4444
theorem signs4444 : ∀ j, Signs p4444 (bank4444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4445 := params 28
abbrev ray4445 := rays 28
def bank4445 : Fin 2 → Cell := twoBank p4445 ray4445
theorem signs4445 : ∀ j, Signs p4445 (bank4445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4446 := params 29
abbrev ray4446 := rays 29
def bank4446 : Fin 2 → Cell := twoBank p4446 ray4446
theorem signs4446 : ∀ j, Signs p4446 (bank4446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4447 := params 30
abbrev ray4447 := rays 30
def bank4447 : Fin 2 → Cell := twoBank p4447 ray4447
theorem signs4447 : ∀ j, Signs p4447 (bank4447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4448 := params 31
abbrev ray4448 := rays 31
def bank4448 : Fin 2 → Cell := twoBank p4448 ray4448
theorem signs4448 : ∀ j, Signs p4448 (bank4448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04417_04448
