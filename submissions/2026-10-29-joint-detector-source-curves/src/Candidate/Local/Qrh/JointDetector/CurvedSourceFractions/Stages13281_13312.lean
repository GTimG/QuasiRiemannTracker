/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13281_13312
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96161075338670,96160645845406,96160216335775,96159786809778,96159357267415,96158927708686,96158498133591,96158068542131,96157638934306,96157209310116,96156779669561,96156350012642,96155920339358,96155490649710,96155060943699,96154631221324,96154201482586,96153771727485,96153341956021,96152912168194,96152482364005,96152052543454,96151622706541,96151192853267,96150762983631,96150333097634,96149903195276,96149473276558,96149043341479,96148613390040,96148183422241,96147753438082,96147323437564]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13280+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13281 := params 0
abbrev ray13281 := rays 0
def bank13281 : Fin 1 → Cell := oneBank p13281 ray13281
theorem signs13281 : ∀ j, Signs p13281 (bank13281 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13282 := params 1
abbrev ray13282 := rays 1
def bank13282 : Fin 1 → Cell := oneBank p13282 ray13282
theorem signs13282 : ∀ j, Signs p13282 (bank13282 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13283 := params 2
abbrev ray13283 := rays 2
def bank13283 : Fin 1 → Cell := oneBank p13283 ray13283
theorem signs13283 : ∀ j, Signs p13283 (bank13283 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13284 := params 3
abbrev ray13284 := rays 3
def bank13284 : Fin 1 → Cell := oneBank p13284 ray13284
theorem signs13284 : ∀ j, Signs p13284 (bank13284 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13285 := params 4
abbrev ray13285 := rays 4
def bank13285 : Fin 1 → Cell := oneBank p13285 ray13285
theorem signs13285 : ∀ j, Signs p13285 (bank13285 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13286 := params 5
abbrev ray13286 := rays 5
def bank13286 : Fin 1 → Cell := oneBank p13286 ray13286
theorem signs13286 : ∀ j, Signs p13286 (bank13286 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13287 := params 6
abbrev ray13287 := rays 6
def bank13287 : Fin 1 → Cell := oneBank p13287 ray13287
theorem signs13287 : ∀ j, Signs p13287 (bank13287 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13288 := params 7
abbrev ray13288 := rays 7
def bank13288 : Fin 1 → Cell := oneBank p13288 ray13288
theorem signs13288 : ∀ j, Signs p13288 (bank13288 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13289 := params 8
abbrev ray13289 := rays 8
def bank13289 : Fin 1 → Cell := oneBank p13289 ray13289
theorem signs13289 : ∀ j, Signs p13289 (bank13289 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13290 := params 9
abbrev ray13290 := rays 9
def bank13290 : Fin 1 → Cell := oneBank p13290 ray13290
theorem signs13290 : ∀ j, Signs p13290 (bank13290 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13291 := params 10
abbrev ray13291 := rays 10
def bank13291 : Fin 1 → Cell := oneBank p13291 ray13291
theorem signs13291 : ∀ j, Signs p13291 (bank13291 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13292 := params 11
abbrev ray13292 := rays 11
def bank13292 : Fin 1 → Cell := oneBank p13292 ray13292
theorem signs13292 : ∀ j, Signs p13292 (bank13292 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13293 := params 12
abbrev ray13293 := rays 12
def bank13293 : Fin 1 → Cell := oneBank p13293 ray13293
theorem signs13293 : ∀ j, Signs p13293 (bank13293 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13294 := params 13
abbrev ray13294 := rays 13
def bank13294 : Fin 1 → Cell := oneBank p13294 ray13294
theorem signs13294 : ∀ j, Signs p13294 (bank13294 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13295 := params 14
abbrev ray13295 := rays 14
def bank13295 : Fin 1 → Cell := oneBank p13295 ray13295
theorem signs13295 : ∀ j, Signs p13295 (bank13295 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13296 := params 15
abbrev ray13296 := rays 15
def bank13296 : Fin 1 → Cell := oneBank p13296 ray13296
theorem signs13296 : ∀ j, Signs p13296 (bank13296 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13297 := params 16
abbrev ray13297 := rays 16
def bank13297 : Fin 1 → Cell := oneBank p13297 ray13297
theorem signs13297 : ∀ j, Signs p13297 (bank13297 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13298 := params 17
abbrev ray13298 := rays 17
def bank13298 : Fin 1 → Cell := oneBank p13298 ray13298
theorem signs13298 : ∀ j, Signs p13298 (bank13298 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13299 := params 18
abbrev ray13299 := rays 18
def bank13299 : Fin 1 → Cell := oneBank p13299 ray13299
theorem signs13299 : ∀ j, Signs p13299 (bank13299 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13300 := params 19
abbrev ray13300 := rays 19
def bank13300 : Fin 1 → Cell := oneBank p13300 ray13300
theorem signs13300 : ∀ j, Signs p13300 (bank13300 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13301 := params 20
abbrev ray13301 := rays 20
def bank13301 : Fin 1 → Cell := oneBank p13301 ray13301
theorem signs13301 : ∀ j, Signs p13301 (bank13301 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13302 := params 21
abbrev ray13302 := rays 21
def bank13302 : Fin 1 → Cell := oneBank p13302 ray13302
theorem signs13302 : ∀ j, Signs p13302 (bank13302 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13303 := params 22
abbrev ray13303 := rays 22
def bank13303 : Fin 1 → Cell := oneBank p13303 ray13303
theorem signs13303 : ∀ j, Signs p13303 (bank13303 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13304 := params 23
abbrev ray13304 := rays 23
def bank13304 : Fin 1 → Cell := oneBank p13304 ray13304
theorem signs13304 : ∀ j, Signs p13304 (bank13304 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13305 := params 24
abbrev ray13305 := rays 24
def bank13305 : Fin 1 → Cell := oneBank p13305 ray13305
theorem signs13305 : ∀ j, Signs p13305 (bank13305 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13306 := params 25
abbrev ray13306 := rays 25
def bank13306 : Fin 1 → Cell := oneBank p13306 ray13306
theorem signs13306 : ∀ j, Signs p13306 (bank13306 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13307 := params 26
abbrev ray13307 := rays 26
def bank13307 : Fin 1 → Cell := oneBank p13307 ray13307
theorem signs13307 : ∀ j, Signs p13307 (bank13307 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13308 := params 27
abbrev ray13308 := rays 27
def bank13308 : Fin 1 → Cell := oneBank p13308 ray13308
theorem signs13308 : ∀ j, Signs p13308 (bank13308 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13309 := params 28
abbrev ray13309 := rays 28
def bank13309 : Fin 1 → Cell := oneBank p13309 ray13309
theorem signs13309 : ∀ j, Signs p13309 (bank13309 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13310 := params 29
abbrev ray13310 := rays 29
def bank13310 : Fin 1 → Cell := oneBank p13310 ray13310
theorem signs13310 : ∀ j, Signs p13310 (bank13310 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13311 := params 30
abbrev ray13311 := rays 30
def bank13311 : Fin 1 → Cell := oneBank p13311 ray13311
theorem signs13311 : ∀ j, Signs p13311 (bank13311 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13312 := params 31
abbrev ray13312 := rays 31
def bank13312 : Fin 1 → Cell := oneBank p13312 ray13312
theorem signs13312 : ∀ j, Signs p13312 (bank13312 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13281_13312
