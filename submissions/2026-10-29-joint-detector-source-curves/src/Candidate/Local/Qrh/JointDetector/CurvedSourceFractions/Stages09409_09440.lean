/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09409_09440
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97683208717211,97682854219938,97682499701989,97682145163365,97681790604066,97681436024092,97681081423444,97680726802123,97680372160129,97680017497463,97679662814126,97679308110118,97678953385440,97678598640092,97678243874075,97677889087390,97677534280037,97677179452016,97676824603329,97676469733976,97676114843957,97675759933273,97675405001925,97675050049913,97674695077238,97674340083900,97673985069900,97673630035239,97673274979917,97672919903935,97672564807293,97672209689992,97671854552033]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9408+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9409 := params 0
abbrev ray9409 := rays 0
def bank9409 : Fin 2 → Cell := twoBank p9409 ray9409
theorem signs9409 : ∀ j, Signs p9409 (bank9409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9410 := params 1
abbrev ray9410 := rays 1
def bank9410 : Fin 2 → Cell := twoBank p9410 ray9410
theorem signs9410 : ∀ j, Signs p9410 (bank9410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9411 := params 2
abbrev ray9411 := rays 2
def bank9411 : Fin 2 → Cell := twoBank p9411 ray9411
theorem signs9411 : ∀ j, Signs p9411 (bank9411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9412 := params 3
abbrev ray9412 := rays 3
def bank9412 : Fin 2 → Cell := twoBank p9412 ray9412
theorem signs9412 : ∀ j, Signs p9412 (bank9412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9413 := params 4
abbrev ray9413 := rays 4
def bank9413 : Fin 2 → Cell := twoBank p9413 ray9413
theorem signs9413 : ∀ j, Signs p9413 (bank9413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9414 := params 5
abbrev ray9414 := rays 5
def bank9414 : Fin 2 → Cell := twoBank p9414 ray9414
theorem signs9414 : ∀ j, Signs p9414 (bank9414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9415 := params 6
abbrev ray9415 := rays 6
def bank9415 : Fin 2 → Cell := twoBank p9415 ray9415
theorem signs9415 : ∀ j, Signs p9415 (bank9415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9416 := params 7
abbrev ray9416 := rays 7
def bank9416 : Fin 2 → Cell := twoBank p9416 ray9416
theorem signs9416 : ∀ j, Signs p9416 (bank9416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9417 := params 8
abbrev ray9417 := rays 8
def bank9417 : Fin 2 → Cell := twoBank p9417 ray9417
theorem signs9417 : ∀ j, Signs p9417 (bank9417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9418 := params 9
abbrev ray9418 := rays 9
def bank9418 : Fin 2 → Cell := twoBank p9418 ray9418
theorem signs9418 : ∀ j, Signs p9418 (bank9418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9419 := params 10
abbrev ray9419 := rays 10
def bank9419 : Fin 2 → Cell := twoBank p9419 ray9419
theorem signs9419 : ∀ j, Signs p9419 (bank9419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9420 := params 11
abbrev ray9420 := rays 11
def bank9420 : Fin 2 → Cell := twoBank p9420 ray9420
theorem signs9420 : ∀ j, Signs p9420 (bank9420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9421 := params 12
abbrev ray9421 := rays 12
def bank9421 : Fin 2 → Cell := twoBank p9421 ray9421
theorem signs9421 : ∀ j, Signs p9421 (bank9421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9422 := params 13
abbrev ray9422 := rays 13
def bank9422 : Fin 2 → Cell := twoBank p9422 ray9422
theorem signs9422 : ∀ j, Signs p9422 (bank9422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9423 := params 14
abbrev ray9423 := rays 14
def bank9423 : Fin 2 → Cell := twoBank p9423 ray9423
theorem signs9423 : ∀ j, Signs p9423 (bank9423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9424 := params 15
abbrev ray9424 := rays 15
def bank9424 : Fin 2 → Cell := twoBank p9424 ray9424
theorem signs9424 : ∀ j, Signs p9424 (bank9424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9425 := params 16
abbrev ray9425 := rays 16
def bank9425 : Fin 2 → Cell := twoBank p9425 ray9425
theorem signs9425 : ∀ j, Signs p9425 (bank9425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9426 := params 17
abbrev ray9426 := rays 17
def bank9426 : Fin 2 → Cell := twoBank p9426 ray9426
theorem signs9426 : ∀ j, Signs p9426 (bank9426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9427 := params 18
abbrev ray9427 := rays 18
def bank9427 : Fin 2 → Cell := twoBank p9427 ray9427
theorem signs9427 : ∀ j, Signs p9427 (bank9427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9428 := params 19
abbrev ray9428 := rays 19
def bank9428 : Fin 2 → Cell := twoBank p9428 ray9428
theorem signs9428 : ∀ j, Signs p9428 (bank9428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9429 := params 20
abbrev ray9429 := rays 20
def bank9429 : Fin 2 → Cell := twoBank p9429 ray9429
theorem signs9429 : ∀ j, Signs p9429 (bank9429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9430 := params 21
abbrev ray9430 := rays 21
def bank9430 : Fin 2 → Cell := twoBank p9430 ray9430
theorem signs9430 : ∀ j, Signs p9430 (bank9430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9431 := params 22
abbrev ray9431 := rays 22
def bank9431 : Fin 2 → Cell := twoBank p9431 ray9431
theorem signs9431 : ∀ j, Signs p9431 (bank9431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9432 := params 23
abbrev ray9432 := rays 23
def bank9432 : Fin 2 → Cell := twoBank p9432 ray9432
theorem signs9432 : ∀ j, Signs p9432 (bank9432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9433 := params 24
abbrev ray9433 := rays 24
def bank9433 : Fin 2 → Cell := twoBank p9433 ray9433
theorem signs9433 : ∀ j, Signs p9433 (bank9433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9434 := params 25
abbrev ray9434 := rays 25
def bank9434 : Fin 2 → Cell := twoBank p9434 ray9434
theorem signs9434 : ∀ j, Signs p9434 (bank9434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9435 := params 26
abbrev ray9435 := rays 26
def bank9435 : Fin 2 → Cell := twoBank p9435 ray9435
theorem signs9435 : ∀ j, Signs p9435 (bank9435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9436 := params 27
abbrev ray9436 := rays 27
def bank9436 : Fin 2 → Cell := twoBank p9436 ray9436
theorem signs9436 : ∀ j, Signs p9436 (bank9436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9437 := params 28
abbrev ray9437 := rays 28
def bank9437 : Fin 2 → Cell := twoBank p9437 ray9437
theorem signs9437 : ∀ j, Signs p9437 (bank9437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9438 := params 29
abbrev ray9438 := rays 29
def bank9438 : Fin 2 → Cell := twoBank p9438 ray9438
theorem signs9438 : ∀ j, Signs p9438 (bank9438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9439 := params 30
abbrev ray9439 := rays 30
def bank9439 : Fin 2 → Cell := twoBank p9439 ray9439
theorem signs9439 : ∀ j, Signs p9439 (bank9439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9440 := params 31
abbrev ray9440 := rays 31
def bank9440 : Fin 2 → Cell := twoBank p9440 ray9440
theorem signs9440 : ∀ j, Signs p9440 (bank9440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09409_09440
