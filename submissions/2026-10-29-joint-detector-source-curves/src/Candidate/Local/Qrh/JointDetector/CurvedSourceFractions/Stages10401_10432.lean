/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10401_10432
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97321477874919,97321103147594,97320728400148,97320353632582,97319978844897,97319604037093,97319229209170,97318854361129,97318479492971,97318104604696,97317729696304,97317354767796,97316979819173,97316604850435,97316229861583,97315854852617,97315479823538,97315104774346,97314729705042,97314354615627,97313979506100,97313604376463,97313229226716,97312854056859,97312478866893,97312103656819,97311728426637,97311353176347,97310977905950,97310602615447,97310227304838,97309851974124,97309476623305]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10400+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10401 := params 0
abbrev ray10401 := rays 0
def bank10401 : Fin 2 → Cell := twoBank p10401 ray10401
theorem signs10401 : ∀ j, Signs p10401 (bank10401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10402 := params 1
abbrev ray10402 := rays 1
def bank10402 : Fin 2 → Cell := twoBank p10402 ray10402
theorem signs10402 : ∀ j, Signs p10402 (bank10402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10403 := params 2
abbrev ray10403 := rays 2
def bank10403 : Fin 2 → Cell := twoBank p10403 ray10403
theorem signs10403 : ∀ j, Signs p10403 (bank10403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10404 := params 3
abbrev ray10404 := rays 3
def bank10404 : Fin 2 → Cell := twoBank p10404 ray10404
theorem signs10404 : ∀ j, Signs p10404 (bank10404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10405 := params 4
abbrev ray10405 := rays 4
def bank10405 : Fin 2 → Cell := twoBank p10405 ray10405
theorem signs10405 : ∀ j, Signs p10405 (bank10405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10406 := params 5
abbrev ray10406 := rays 5
def bank10406 : Fin 2 → Cell := twoBank p10406 ray10406
theorem signs10406 : ∀ j, Signs p10406 (bank10406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10407 := params 6
abbrev ray10407 := rays 6
def bank10407 : Fin 2 → Cell := twoBank p10407 ray10407
theorem signs10407 : ∀ j, Signs p10407 (bank10407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10408 := params 7
abbrev ray10408 := rays 7
def bank10408 : Fin 2 → Cell := twoBank p10408 ray10408
theorem signs10408 : ∀ j, Signs p10408 (bank10408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10409 := params 8
abbrev ray10409 := rays 8
def bank10409 : Fin 2 → Cell := twoBank p10409 ray10409
theorem signs10409 : ∀ j, Signs p10409 (bank10409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10410 := params 9
abbrev ray10410 := rays 9
def bank10410 : Fin 2 → Cell := twoBank p10410 ray10410
theorem signs10410 : ∀ j, Signs p10410 (bank10410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10411 := params 10
abbrev ray10411 := rays 10
def bank10411 : Fin 2 → Cell := twoBank p10411 ray10411
theorem signs10411 : ∀ j, Signs p10411 (bank10411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10412 := params 11
abbrev ray10412 := rays 11
def bank10412 : Fin 2 → Cell := twoBank p10412 ray10412
theorem signs10412 : ∀ j, Signs p10412 (bank10412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10413 := params 12
abbrev ray10413 := rays 12
def bank10413 : Fin 2 → Cell := twoBank p10413 ray10413
theorem signs10413 : ∀ j, Signs p10413 (bank10413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10414 := params 13
abbrev ray10414 := rays 13
def bank10414 : Fin 2 → Cell := twoBank p10414 ray10414
theorem signs10414 : ∀ j, Signs p10414 (bank10414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10415 := params 14
abbrev ray10415 := rays 14
def bank10415 : Fin 2 → Cell := twoBank p10415 ray10415
theorem signs10415 : ∀ j, Signs p10415 (bank10415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10416 := params 15
abbrev ray10416 := rays 15
def bank10416 : Fin 2 → Cell := twoBank p10416 ray10416
theorem signs10416 : ∀ j, Signs p10416 (bank10416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10417 := params 16
abbrev ray10417 := rays 16
def bank10417 : Fin 2 → Cell := twoBank p10417 ray10417
theorem signs10417 : ∀ j, Signs p10417 (bank10417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10418 := params 17
abbrev ray10418 := rays 17
def bank10418 : Fin 2 → Cell := twoBank p10418 ray10418
theorem signs10418 : ∀ j, Signs p10418 (bank10418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10419 := params 18
abbrev ray10419 := rays 18
def bank10419 : Fin 2 → Cell := twoBank p10419 ray10419
theorem signs10419 : ∀ j, Signs p10419 (bank10419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10420 := params 19
abbrev ray10420 := rays 19
def bank10420 : Fin 2 → Cell := twoBank p10420 ray10420
theorem signs10420 : ∀ j, Signs p10420 (bank10420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10421 := params 20
abbrev ray10421 := rays 20
def bank10421 : Fin 2 → Cell := twoBank p10421 ray10421
theorem signs10421 : ∀ j, Signs p10421 (bank10421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10422 := params 21
abbrev ray10422 := rays 21
def bank10422 : Fin 2 → Cell := twoBank p10422 ray10422
theorem signs10422 : ∀ j, Signs p10422 (bank10422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10423 := params 22
abbrev ray10423 := rays 22
def bank10423 : Fin 2 → Cell := twoBank p10423 ray10423
theorem signs10423 : ∀ j, Signs p10423 (bank10423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10424 := params 23
abbrev ray10424 := rays 23
def bank10424 : Fin 2 → Cell := twoBank p10424 ray10424
theorem signs10424 : ∀ j, Signs p10424 (bank10424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10425 := params 24
abbrev ray10425 := rays 24
def bank10425 : Fin 2 → Cell := twoBank p10425 ray10425
theorem signs10425 : ∀ j, Signs p10425 (bank10425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10426 := params 25
abbrev ray10426 := rays 25
def bank10426 : Fin 2 → Cell := twoBank p10426 ray10426
theorem signs10426 : ∀ j, Signs p10426 (bank10426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10427 := params 26
abbrev ray10427 := rays 26
def bank10427 : Fin 2 → Cell := twoBank p10427 ray10427
theorem signs10427 : ∀ j, Signs p10427 (bank10427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10428 := params 27
abbrev ray10428 := rays 27
def bank10428 : Fin 2 → Cell := twoBank p10428 ray10428
theorem signs10428 : ∀ j, Signs p10428 (bank10428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10429 := params 28
abbrev ray10429 := rays 28
def bank10429 : Fin 2 → Cell := twoBank p10429 ray10429
theorem signs10429 : ∀ j, Signs p10429 (bank10429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10430 := params 29
abbrev ray10430 := rays 29
def bank10430 : Fin 2 → Cell := twoBank p10430 ray10430
theorem signs10430 : ∀ j, Signs p10430 (bank10430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10431 := params 30
abbrev ray10431 := rays 30
def bank10431 : Fin 2 → Cell := twoBank p10431 ray10431
theorem signs10431 : ∀ j, Signs p10431 (bank10431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10432 := params 31
abbrev ray10432 := rays 31
def bank10432 : Fin 2 → Cell := twoBank p10432 ray10432
theorem signs10432 : ∀ j, Signs p10432 (bank10432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10401_10432
