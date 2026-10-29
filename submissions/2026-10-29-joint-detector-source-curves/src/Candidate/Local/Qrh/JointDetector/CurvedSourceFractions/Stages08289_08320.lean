/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08289_08320
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98067121829402,98066790879179,98066459907569,98066128914572,98065797900190,98065466864423,98065135807271,98064804728736,98064473628818,98064142507518,98063811364836,98063480200773,98063149015330,98062817808507,98062486580305,98062155330725,98061824059768,98061492767434,98061161453724,98060830118638,98060498762177,98060167384342,98059835985134,98059504564553,98059173122600,98058841659275,98058510174579,98058178668513,98057847141078,98057515592274,98057184022102,98056852430563,98056520817657]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8288+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8289 := params 0
abbrev ray8289 := rays 0
def bank8289 : Fin 2 → Cell := twoBank p8289 ray8289
theorem signs8289 : ∀ j, Signs p8289 (bank8289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8290 := params 1
abbrev ray8290 := rays 1
def bank8290 : Fin 2 → Cell := twoBank p8290 ray8290
theorem signs8290 : ∀ j, Signs p8290 (bank8290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8291 := params 2
abbrev ray8291 := rays 2
def bank8291 : Fin 2 → Cell := twoBank p8291 ray8291
theorem signs8291 : ∀ j, Signs p8291 (bank8291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8292 := params 3
abbrev ray8292 := rays 3
def bank8292 : Fin 2 → Cell := twoBank p8292 ray8292
theorem signs8292 : ∀ j, Signs p8292 (bank8292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8293 := params 4
abbrev ray8293 := rays 4
def bank8293 : Fin 2 → Cell := twoBank p8293 ray8293
theorem signs8293 : ∀ j, Signs p8293 (bank8293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8294 := params 5
abbrev ray8294 := rays 5
def bank8294 : Fin 2 → Cell := twoBank p8294 ray8294
theorem signs8294 : ∀ j, Signs p8294 (bank8294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8295 := params 6
abbrev ray8295 := rays 6
def bank8295 : Fin 2 → Cell := twoBank p8295 ray8295
theorem signs8295 : ∀ j, Signs p8295 (bank8295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8296 := params 7
abbrev ray8296 := rays 7
def bank8296 : Fin 2 → Cell := twoBank p8296 ray8296
theorem signs8296 : ∀ j, Signs p8296 (bank8296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8297 := params 8
abbrev ray8297 := rays 8
def bank8297 : Fin 2 → Cell := twoBank p8297 ray8297
theorem signs8297 : ∀ j, Signs p8297 (bank8297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8298 := params 9
abbrev ray8298 := rays 9
def bank8298 : Fin 2 → Cell := twoBank p8298 ray8298
theorem signs8298 : ∀ j, Signs p8298 (bank8298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8299 := params 10
abbrev ray8299 := rays 10
def bank8299 : Fin 2 → Cell := twoBank p8299 ray8299
theorem signs8299 : ∀ j, Signs p8299 (bank8299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8300 := params 11
abbrev ray8300 := rays 11
def bank8300 : Fin 2 → Cell := twoBank p8300 ray8300
theorem signs8300 : ∀ j, Signs p8300 (bank8300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8301 := params 12
abbrev ray8301 := rays 12
def bank8301 : Fin 2 → Cell := twoBank p8301 ray8301
theorem signs8301 : ∀ j, Signs p8301 (bank8301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8302 := params 13
abbrev ray8302 := rays 13
def bank8302 : Fin 2 → Cell := twoBank p8302 ray8302
theorem signs8302 : ∀ j, Signs p8302 (bank8302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8303 := params 14
abbrev ray8303 := rays 14
def bank8303 : Fin 2 → Cell := twoBank p8303 ray8303
theorem signs8303 : ∀ j, Signs p8303 (bank8303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8304 := params 15
abbrev ray8304 := rays 15
def bank8304 : Fin 2 → Cell := twoBank p8304 ray8304
theorem signs8304 : ∀ j, Signs p8304 (bank8304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8305 := params 16
abbrev ray8305 := rays 16
def bank8305 : Fin 2 → Cell := twoBank p8305 ray8305
theorem signs8305 : ∀ j, Signs p8305 (bank8305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8306 := params 17
abbrev ray8306 := rays 17
def bank8306 : Fin 2 → Cell := twoBank p8306 ray8306
theorem signs8306 : ∀ j, Signs p8306 (bank8306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8307 := params 18
abbrev ray8307 := rays 18
def bank8307 : Fin 2 → Cell := twoBank p8307 ray8307
theorem signs8307 : ∀ j, Signs p8307 (bank8307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8308 := params 19
abbrev ray8308 := rays 19
def bank8308 : Fin 2 → Cell := twoBank p8308 ray8308
theorem signs8308 : ∀ j, Signs p8308 (bank8308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8309 := params 20
abbrev ray8309 := rays 20
def bank8309 : Fin 2 → Cell := twoBank p8309 ray8309
theorem signs8309 : ∀ j, Signs p8309 (bank8309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8310 := params 21
abbrev ray8310 := rays 21
def bank8310 : Fin 2 → Cell := twoBank p8310 ray8310
theorem signs8310 : ∀ j, Signs p8310 (bank8310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8311 := params 22
abbrev ray8311 := rays 22
def bank8311 : Fin 2 → Cell := twoBank p8311 ray8311
theorem signs8311 : ∀ j, Signs p8311 (bank8311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8312 := params 23
abbrev ray8312 := rays 23
def bank8312 : Fin 2 → Cell := twoBank p8312 ray8312
theorem signs8312 : ∀ j, Signs p8312 (bank8312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8313 := params 24
abbrev ray8313 := rays 24
def bank8313 : Fin 2 → Cell := twoBank p8313 ray8313
theorem signs8313 : ∀ j, Signs p8313 (bank8313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8314 := params 25
abbrev ray8314 := rays 25
def bank8314 : Fin 2 → Cell := twoBank p8314 ray8314
theorem signs8314 : ∀ j, Signs p8314 (bank8314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8315 := params 26
abbrev ray8315 := rays 26
def bank8315 : Fin 2 → Cell := twoBank p8315 ray8315
theorem signs8315 : ∀ j, Signs p8315 (bank8315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8316 := params 27
abbrev ray8316 := rays 27
def bank8316 : Fin 2 → Cell := twoBank p8316 ray8316
theorem signs8316 : ∀ j, Signs p8316 (bank8316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8317 := params 28
abbrev ray8317 := rays 28
def bank8317 : Fin 2 → Cell := twoBank p8317 ray8317
theorem signs8317 : ∀ j, Signs p8317 (bank8317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8318 := params 29
abbrev ray8318 := rays 29
def bank8318 : Fin 2 → Cell := twoBank p8318 ray8318
theorem signs8318 : ∀ j, Signs p8318 (bank8318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8319 := params 30
abbrev ray8319 := rays 30
def bank8319 : Fin 2 → Cell := twoBank p8319 ray8319
theorem signs8319 : ∀ j, Signs p8319 (bank8319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8320 := params 31
abbrev ray8320 := rays 31
def bank8320 : Fin 2 → Cell := twoBank p8320 ray8320
theorem signs8320 : ∀ j, Signs p8320 (bank8320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08289_08320
