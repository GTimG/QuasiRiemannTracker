/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12385_12416
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96539084504050,96538670815149,96538257107055,96537843379768,96537429633288,96537015867616,96536602082752,96536188278697,96535774455451,96535360613014,96534946751387,96534532870570,96534118970564,96533705051369,96533291112985,96532877155413,96532463178653,96532049182706,96531635167572,96531221133252,96530807079745,96530393007053,96529978915176,96529564804114,96529150673867,96528736524436,96528322355822,96527908168024,96527493961043,96527079734880,96526665489535,96526251225008,96525836941300]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12384+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12385 := params 0
abbrev ray12385 := rays 0
def bank12385 : Fin 2 → Cell := twoBank p12385 ray12385
theorem signs12385 : ∀ j, Signs p12385 (bank12385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12386 := params 1
abbrev ray12386 := rays 1
def bank12386 : Fin 2 → Cell := twoBank p12386 ray12386
theorem signs12386 : ∀ j, Signs p12386 (bank12386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12387 := params 2
abbrev ray12387 := rays 2
def bank12387 : Fin 2 → Cell := twoBank p12387 ray12387
theorem signs12387 : ∀ j, Signs p12387 (bank12387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12388 := params 3
abbrev ray12388 := rays 3
def bank12388 : Fin 2 → Cell := twoBank p12388 ray12388
theorem signs12388 : ∀ j, Signs p12388 (bank12388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12389 := params 4
abbrev ray12389 := rays 4
def bank12389 : Fin 2 → Cell := twoBank p12389 ray12389
theorem signs12389 : ∀ j, Signs p12389 (bank12389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12390 := params 5
abbrev ray12390 := rays 5
def bank12390 : Fin 2 → Cell := twoBank p12390 ray12390
theorem signs12390 : ∀ j, Signs p12390 (bank12390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12391 := params 6
abbrev ray12391 := rays 6
def bank12391 : Fin 2 → Cell := twoBank p12391 ray12391
theorem signs12391 : ∀ j, Signs p12391 (bank12391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12392 := params 7
abbrev ray12392 := rays 7
def bank12392 : Fin 2 → Cell := twoBank p12392 ray12392
theorem signs12392 : ∀ j, Signs p12392 (bank12392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12393 := params 8
abbrev ray12393 := rays 8
def bank12393 : Fin 2 → Cell := twoBank p12393 ray12393
theorem signs12393 : ∀ j, Signs p12393 (bank12393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12394 := params 9
abbrev ray12394 := rays 9
def bank12394 : Fin 2 → Cell := twoBank p12394 ray12394
theorem signs12394 : ∀ j, Signs p12394 (bank12394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12395 := params 10
abbrev ray12395 := rays 10
def bank12395 : Fin 2 → Cell := twoBank p12395 ray12395
theorem signs12395 : ∀ j, Signs p12395 (bank12395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12396 := params 11
abbrev ray12396 := rays 11
def bank12396 : Fin 2 → Cell := twoBank p12396 ray12396
theorem signs12396 : ∀ j, Signs p12396 (bank12396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12397 := params 12
abbrev ray12397 := rays 12
def bank12397 : Fin 2 → Cell := twoBank p12397 ray12397
theorem signs12397 : ∀ j, Signs p12397 (bank12397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12398 := params 13
abbrev ray12398 := rays 13
def bank12398 : Fin 2 → Cell := twoBank p12398 ray12398
theorem signs12398 : ∀ j, Signs p12398 (bank12398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12399 := params 14
abbrev ray12399 := rays 14
def bank12399 : Fin 2 → Cell := twoBank p12399 ray12399
theorem signs12399 : ∀ j, Signs p12399 (bank12399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12400 := params 15
abbrev ray12400 := rays 15
def bank12400 : Fin 2 → Cell := twoBank p12400 ray12400
theorem signs12400 : ∀ j, Signs p12400 (bank12400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12401 := params 16
abbrev ray12401 := rays 16
def bank12401 : Fin 2 → Cell := twoBank p12401 ray12401
theorem signs12401 : ∀ j, Signs p12401 (bank12401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12402 := params 17
abbrev ray12402 := rays 17
def bank12402 : Fin 2 → Cell := twoBank p12402 ray12402
theorem signs12402 : ∀ j, Signs p12402 (bank12402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12403 := params 18
abbrev ray12403 := rays 18
def bank12403 : Fin 2 → Cell := twoBank p12403 ray12403
theorem signs12403 : ∀ j, Signs p12403 (bank12403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12404 := params 19
abbrev ray12404 := rays 19
def bank12404 : Fin 2 → Cell := twoBank p12404 ray12404
theorem signs12404 : ∀ j, Signs p12404 (bank12404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12405 := params 20
abbrev ray12405 := rays 20
def bank12405 : Fin 2 → Cell := twoBank p12405 ray12405
theorem signs12405 : ∀ j, Signs p12405 (bank12405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12406 := params 21
abbrev ray12406 := rays 21
def bank12406 : Fin 2 → Cell := twoBank p12406 ray12406
theorem signs12406 : ∀ j, Signs p12406 (bank12406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12407 := params 22
abbrev ray12407 := rays 22
def bank12407 : Fin 2 → Cell := twoBank p12407 ray12407
theorem signs12407 : ∀ j, Signs p12407 (bank12407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12408 := params 23
abbrev ray12408 := rays 23
def bank12408 : Fin 2 → Cell := twoBank p12408 ray12408
theorem signs12408 : ∀ j, Signs p12408 (bank12408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12409 := params 24
abbrev ray12409 := rays 24
def bank12409 : Fin 2 → Cell := twoBank p12409 ray12409
theorem signs12409 : ∀ j, Signs p12409 (bank12409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12410 := params 25
abbrev ray12410 := rays 25
def bank12410 : Fin 2 → Cell := twoBank p12410 ray12410
theorem signs12410 : ∀ j, Signs p12410 (bank12410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12411 := params 26
abbrev ray12411 := rays 26
def bank12411 : Fin 2 → Cell := twoBank p12411 ray12411
theorem signs12411 : ∀ j, Signs p12411 (bank12411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12412 := params 27
abbrev ray12412 := rays 27
def bank12412 : Fin 2 → Cell := twoBank p12412 ray12412
theorem signs12412 : ∀ j, Signs p12412 (bank12412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12413 := params 28
abbrev ray12413 := rays 28
def bank12413 : Fin 2 → Cell := twoBank p12413 ray12413
theorem signs12413 : ∀ j, Signs p12413 (bank12413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12414 := params 29
abbrev ray12414 := rays 29
def bank12414 : Fin 2 → Cell := twoBank p12414 ray12414
theorem signs12414 : ∀ j, Signs p12414 (bank12414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12415 := params 30
abbrev ray12415 := rays 30
def bank12415 : Fin 2 → Cell := twoBank p12415 ray12415
theorem signs12415 : ∀ j, Signs p12415 (bank12415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12416 := params 31
abbrev ray12416 := rays 31
def bank12416 : Fin 2 → Cell := twoBank p12416 ray12416
theorem signs12416 : ∀ j, Signs p12416 (bank12416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12385_12416
