/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12289_12320
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96578709211211,96578297366800,96577885503156,96577473620279,96577061718170,96576649796829,96576237856257,96575825896454,96575413917420,96575001919156,96574589901662,96574177864939,96573765808987,96573353733806,96572941639397,96572529525760,96572117392896,96571705240805,96571293069488,96570880878945,96570468669176,96570056440182,96569644191963,96569231924520,96568819637853,96568407331962,96567995006848,96567582662512,96567170298953,96566757916172,96566345514170,96565933092947,96565520652503]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12288+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12289 := params 0
abbrev ray12289 := rays 0
def bank12289 : Fin 2 → Cell := twoBank p12289 ray12289
theorem signs12289 : ∀ j, Signs p12289 (bank12289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12290 := params 1
abbrev ray12290 := rays 1
def bank12290 : Fin 2 → Cell := twoBank p12290 ray12290
theorem signs12290 : ∀ j, Signs p12290 (bank12290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12291 := params 2
abbrev ray12291 := rays 2
def bank12291 : Fin 2 → Cell := twoBank p12291 ray12291
theorem signs12291 : ∀ j, Signs p12291 (bank12291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12292 := params 3
abbrev ray12292 := rays 3
def bank12292 : Fin 2 → Cell := twoBank p12292 ray12292
theorem signs12292 : ∀ j, Signs p12292 (bank12292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12293 := params 4
abbrev ray12293 := rays 4
def bank12293 : Fin 2 → Cell := twoBank p12293 ray12293
theorem signs12293 : ∀ j, Signs p12293 (bank12293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12294 := params 5
abbrev ray12294 := rays 5
def bank12294 : Fin 2 → Cell := twoBank p12294 ray12294
theorem signs12294 : ∀ j, Signs p12294 (bank12294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12295 := params 6
abbrev ray12295 := rays 6
def bank12295 : Fin 2 → Cell := twoBank p12295 ray12295
theorem signs12295 : ∀ j, Signs p12295 (bank12295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12296 := params 7
abbrev ray12296 := rays 7
def bank12296 : Fin 2 → Cell := twoBank p12296 ray12296
theorem signs12296 : ∀ j, Signs p12296 (bank12296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12297 := params 8
abbrev ray12297 := rays 8
def bank12297 : Fin 2 → Cell := twoBank p12297 ray12297
theorem signs12297 : ∀ j, Signs p12297 (bank12297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12298 := params 9
abbrev ray12298 := rays 9
def bank12298 : Fin 2 → Cell := twoBank p12298 ray12298
theorem signs12298 : ∀ j, Signs p12298 (bank12298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12299 := params 10
abbrev ray12299 := rays 10
def bank12299 : Fin 2 → Cell := twoBank p12299 ray12299
theorem signs12299 : ∀ j, Signs p12299 (bank12299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12300 := params 11
abbrev ray12300 := rays 11
def bank12300 : Fin 2 → Cell := twoBank p12300 ray12300
theorem signs12300 : ∀ j, Signs p12300 (bank12300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12301 := params 12
abbrev ray12301 := rays 12
def bank12301 : Fin 2 → Cell := twoBank p12301 ray12301
theorem signs12301 : ∀ j, Signs p12301 (bank12301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12302 := params 13
abbrev ray12302 := rays 13
def bank12302 : Fin 2 → Cell := twoBank p12302 ray12302
theorem signs12302 : ∀ j, Signs p12302 (bank12302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12303 := params 14
abbrev ray12303 := rays 14
def bank12303 : Fin 2 → Cell := twoBank p12303 ray12303
theorem signs12303 : ∀ j, Signs p12303 (bank12303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12304 := params 15
abbrev ray12304 := rays 15
def bank12304 : Fin 2 → Cell := twoBank p12304 ray12304
theorem signs12304 : ∀ j, Signs p12304 (bank12304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12305 := params 16
abbrev ray12305 := rays 16
def bank12305 : Fin 2 → Cell := twoBank p12305 ray12305
theorem signs12305 : ∀ j, Signs p12305 (bank12305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12306 := params 17
abbrev ray12306 := rays 17
def bank12306 : Fin 2 → Cell := twoBank p12306 ray12306
theorem signs12306 : ∀ j, Signs p12306 (bank12306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12307 := params 18
abbrev ray12307 := rays 18
def bank12307 : Fin 2 → Cell := twoBank p12307 ray12307
theorem signs12307 : ∀ j, Signs p12307 (bank12307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12308 := params 19
abbrev ray12308 := rays 19
def bank12308 : Fin 2 → Cell := twoBank p12308 ray12308
theorem signs12308 : ∀ j, Signs p12308 (bank12308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12309 := params 20
abbrev ray12309 := rays 20
def bank12309 : Fin 2 → Cell := twoBank p12309 ray12309
theorem signs12309 : ∀ j, Signs p12309 (bank12309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12310 := params 21
abbrev ray12310 := rays 21
def bank12310 : Fin 2 → Cell := twoBank p12310 ray12310
theorem signs12310 : ∀ j, Signs p12310 (bank12310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12311 := params 22
abbrev ray12311 := rays 22
def bank12311 : Fin 2 → Cell := twoBank p12311 ray12311
theorem signs12311 : ∀ j, Signs p12311 (bank12311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12312 := params 23
abbrev ray12312 := rays 23
def bank12312 : Fin 2 → Cell := twoBank p12312 ray12312
theorem signs12312 : ∀ j, Signs p12312 (bank12312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12313 := params 24
abbrev ray12313 := rays 24
def bank12313 : Fin 2 → Cell := twoBank p12313 ray12313
theorem signs12313 : ∀ j, Signs p12313 (bank12313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12314 := params 25
abbrev ray12314 := rays 25
def bank12314 : Fin 2 → Cell := twoBank p12314 ray12314
theorem signs12314 : ∀ j, Signs p12314 (bank12314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12315 := params 26
abbrev ray12315 := rays 26
def bank12315 : Fin 2 → Cell := twoBank p12315 ray12315
theorem signs12315 : ∀ j, Signs p12315 (bank12315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12316 := params 27
abbrev ray12316 := rays 27
def bank12316 : Fin 2 → Cell := twoBank p12316 ray12316
theorem signs12316 : ∀ j, Signs p12316 (bank12316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12317 := params 28
abbrev ray12317 := rays 28
def bank12317 : Fin 2 → Cell := twoBank p12317 ray12317
theorem signs12317 : ∀ j, Signs p12317 (bank12317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12318 := params 29
abbrev ray12318 := rays 29
def bank12318 : Fin 2 → Cell := twoBank p12318 ray12318
theorem signs12318 : ∀ j, Signs p12318 (bank12318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12319 := params 30
abbrev ray12319 := rays 30
def bank12319 : Fin 2 → Cell := twoBank p12319 ray12319
theorem signs12319 : ∀ j, Signs p12319 (bank12319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12320 := params 31
abbrev ray12320 := rays 31
def bank12320 : Fin 2 → Cell := twoBank p12320 ray12320
theorem signs12320 : ∀ j, Signs p12320 (bank12320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12289_12320
