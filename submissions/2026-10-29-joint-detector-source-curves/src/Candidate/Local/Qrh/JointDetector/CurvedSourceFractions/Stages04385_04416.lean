/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04385_04416
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99188565658219,99188324248427,99188082813895,99187841354625,99187599870617,99187358361873,99187116828394,99186875270181,99186633687235,99186392079557,99186150447148,99185908790009,99185667108141,99185425401546,99185183670224,99184941914177,99184700133405,99184458327910,99184216497692,99183974642753,99183732763094,99183490858716,99183248929620,99183006975807,99182764997278,99182522994034,99182280966076,99182038913406,99181796836024,99181554733932,99181312607130,99181070455620,99180828279402]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4384+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4385 := params 0
abbrev ray4385 := rays 0
def bank4385 : Fin 2 → Cell := twoBank p4385 ray4385
theorem signs4385 : ∀ j, Signs p4385 (bank4385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4386 := params 1
abbrev ray4386 := rays 1
def bank4386 : Fin 2 → Cell := twoBank p4386 ray4386
theorem signs4386 : ∀ j, Signs p4386 (bank4386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4387 := params 2
abbrev ray4387 := rays 2
def bank4387 : Fin 2 → Cell := twoBank p4387 ray4387
theorem signs4387 : ∀ j, Signs p4387 (bank4387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4388 := params 3
abbrev ray4388 := rays 3
def bank4388 : Fin 2 → Cell := twoBank p4388 ray4388
theorem signs4388 : ∀ j, Signs p4388 (bank4388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4389 := params 4
abbrev ray4389 := rays 4
def bank4389 : Fin 2 → Cell := twoBank p4389 ray4389
theorem signs4389 : ∀ j, Signs p4389 (bank4389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4390 := params 5
abbrev ray4390 := rays 5
def bank4390 : Fin 2 → Cell := twoBank p4390 ray4390
theorem signs4390 : ∀ j, Signs p4390 (bank4390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4391 := params 6
abbrev ray4391 := rays 6
def bank4391 : Fin 2 → Cell := twoBank p4391 ray4391
theorem signs4391 : ∀ j, Signs p4391 (bank4391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4392 := params 7
abbrev ray4392 := rays 7
def bank4392 : Fin 2 → Cell := twoBank p4392 ray4392
theorem signs4392 : ∀ j, Signs p4392 (bank4392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4393 := params 8
abbrev ray4393 := rays 8
def bank4393 : Fin 2 → Cell := twoBank p4393 ray4393
theorem signs4393 : ∀ j, Signs p4393 (bank4393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4394 := params 9
abbrev ray4394 := rays 9
def bank4394 : Fin 2 → Cell := twoBank p4394 ray4394
theorem signs4394 : ∀ j, Signs p4394 (bank4394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4395 := params 10
abbrev ray4395 := rays 10
def bank4395 : Fin 2 → Cell := twoBank p4395 ray4395
theorem signs4395 : ∀ j, Signs p4395 (bank4395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4396 := params 11
abbrev ray4396 := rays 11
def bank4396 : Fin 2 → Cell := twoBank p4396 ray4396
theorem signs4396 : ∀ j, Signs p4396 (bank4396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4397 := params 12
abbrev ray4397 := rays 12
def bank4397 : Fin 2 → Cell := twoBank p4397 ray4397
theorem signs4397 : ∀ j, Signs p4397 (bank4397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4398 := params 13
abbrev ray4398 := rays 13
def bank4398 : Fin 2 → Cell := twoBank p4398 ray4398
theorem signs4398 : ∀ j, Signs p4398 (bank4398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4399 := params 14
abbrev ray4399 := rays 14
def bank4399 : Fin 2 → Cell := twoBank p4399 ray4399
theorem signs4399 : ∀ j, Signs p4399 (bank4399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4400 := params 15
abbrev ray4400 := rays 15
def bank4400 : Fin 2 → Cell := twoBank p4400 ray4400
theorem signs4400 : ∀ j, Signs p4400 (bank4400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4401 := params 16
abbrev ray4401 := rays 16
def bank4401 : Fin 2 → Cell := twoBank p4401 ray4401
theorem signs4401 : ∀ j, Signs p4401 (bank4401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4402 := params 17
abbrev ray4402 := rays 17
def bank4402 : Fin 2 → Cell := twoBank p4402 ray4402
theorem signs4402 : ∀ j, Signs p4402 (bank4402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4403 := params 18
abbrev ray4403 := rays 18
def bank4403 : Fin 2 → Cell := twoBank p4403 ray4403
theorem signs4403 : ∀ j, Signs p4403 (bank4403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4404 := params 19
abbrev ray4404 := rays 19
def bank4404 : Fin 2 → Cell := twoBank p4404 ray4404
theorem signs4404 : ∀ j, Signs p4404 (bank4404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4405 := params 20
abbrev ray4405 := rays 20
def bank4405 : Fin 2 → Cell := twoBank p4405 ray4405
theorem signs4405 : ∀ j, Signs p4405 (bank4405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4406 := params 21
abbrev ray4406 := rays 21
def bank4406 : Fin 2 → Cell := twoBank p4406 ray4406
theorem signs4406 : ∀ j, Signs p4406 (bank4406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4407 := params 22
abbrev ray4407 := rays 22
def bank4407 : Fin 2 → Cell := twoBank p4407 ray4407
theorem signs4407 : ∀ j, Signs p4407 (bank4407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4408 := params 23
abbrev ray4408 := rays 23
def bank4408 : Fin 2 → Cell := twoBank p4408 ray4408
theorem signs4408 : ∀ j, Signs p4408 (bank4408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4409 := params 24
abbrev ray4409 := rays 24
def bank4409 : Fin 2 → Cell := twoBank p4409 ray4409
theorem signs4409 : ∀ j, Signs p4409 (bank4409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4410 := params 25
abbrev ray4410 := rays 25
def bank4410 : Fin 2 → Cell := twoBank p4410 ray4410
theorem signs4410 : ∀ j, Signs p4410 (bank4410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4411 := params 26
abbrev ray4411 := rays 26
def bank4411 : Fin 2 → Cell := twoBank p4411 ray4411
theorem signs4411 : ∀ j, Signs p4411 (bank4411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4412 := params 27
abbrev ray4412 := rays 27
def bank4412 : Fin 2 → Cell := twoBank p4412 ray4412
theorem signs4412 : ∀ j, Signs p4412 (bank4412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4413 := params 28
abbrev ray4413 := rays 28
def bank4413 : Fin 2 → Cell := twoBank p4413 ray4413
theorem signs4413 : ∀ j, Signs p4413 (bank4413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4414 := params 29
abbrev ray4414 := rays 29
def bank4414 : Fin 2 → Cell := twoBank p4414 ray4414
theorem signs4414 : ∀ j, Signs p4414 (bank4414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4415 := params 30
abbrev ray4415 := rays 30
def bank4415 : Fin 2 → Cell := twoBank p4415 ray4415
theorem signs4415 : ∀ j, Signs p4415 (bank4415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4416 := params 31
abbrev ray4416 := rays 31
def bank4416 : Fin 2 → Cell := twoBank p4416 ray4416
theorem signs4416 : ∀ j, Signs p4416 (bank4416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04385_04416
