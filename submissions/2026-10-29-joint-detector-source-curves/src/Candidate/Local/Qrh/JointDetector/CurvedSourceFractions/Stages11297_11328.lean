/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11297_11328
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96977715971352,96977323419937,96976930848849,96976538258088,96976145647655,96975753017550,96975360367774,96974967698327,96974575009210,96974182300423,96973789571967,96973396823842,96973004056049,96972611268588,96972218461460,96971825634665,96971432788203,96971039922075,96970647036282,96970254130824,96969861205701,96969468260914,96969075296464,96968682312351,96968289308575,96967896285137,96967503242037,96967110179276,96966717096854,96966323994772,96965930873030,96965537731628,96965144570567]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11296+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11297 := params 0
abbrev ray11297 := rays 0
def bank11297 : Fin 2 → Cell := twoBank p11297 ray11297
theorem signs11297 : ∀ j, Signs p11297 (bank11297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11298 := params 1
abbrev ray11298 := rays 1
def bank11298 : Fin 2 → Cell := twoBank p11298 ray11298
theorem signs11298 : ∀ j, Signs p11298 (bank11298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11299 := params 2
abbrev ray11299 := rays 2
def bank11299 : Fin 2 → Cell := twoBank p11299 ray11299
theorem signs11299 : ∀ j, Signs p11299 (bank11299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11300 := params 3
abbrev ray11300 := rays 3
def bank11300 : Fin 2 → Cell := twoBank p11300 ray11300
theorem signs11300 : ∀ j, Signs p11300 (bank11300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11301 := params 4
abbrev ray11301 := rays 4
def bank11301 : Fin 2 → Cell := twoBank p11301 ray11301
theorem signs11301 : ∀ j, Signs p11301 (bank11301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11302 := params 5
abbrev ray11302 := rays 5
def bank11302 : Fin 2 → Cell := twoBank p11302 ray11302
theorem signs11302 : ∀ j, Signs p11302 (bank11302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11303 := params 6
abbrev ray11303 := rays 6
def bank11303 : Fin 2 → Cell := twoBank p11303 ray11303
theorem signs11303 : ∀ j, Signs p11303 (bank11303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11304 := params 7
abbrev ray11304 := rays 7
def bank11304 : Fin 2 → Cell := twoBank p11304 ray11304
theorem signs11304 : ∀ j, Signs p11304 (bank11304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11305 := params 8
abbrev ray11305 := rays 8
def bank11305 : Fin 2 → Cell := twoBank p11305 ray11305
theorem signs11305 : ∀ j, Signs p11305 (bank11305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11306 := params 9
abbrev ray11306 := rays 9
def bank11306 : Fin 2 → Cell := twoBank p11306 ray11306
theorem signs11306 : ∀ j, Signs p11306 (bank11306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11307 := params 10
abbrev ray11307 := rays 10
def bank11307 : Fin 2 → Cell := twoBank p11307 ray11307
theorem signs11307 : ∀ j, Signs p11307 (bank11307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11308 := params 11
abbrev ray11308 := rays 11
def bank11308 : Fin 2 → Cell := twoBank p11308 ray11308
theorem signs11308 : ∀ j, Signs p11308 (bank11308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11309 := params 12
abbrev ray11309 := rays 12
def bank11309 : Fin 2 → Cell := twoBank p11309 ray11309
theorem signs11309 : ∀ j, Signs p11309 (bank11309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11310 := params 13
abbrev ray11310 := rays 13
def bank11310 : Fin 2 → Cell := twoBank p11310 ray11310
theorem signs11310 : ∀ j, Signs p11310 (bank11310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11311 := params 14
abbrev ray11311 := rays 14
def bank11311 : Fin 2 → Cell := twoBank p11311 ray11311
theorem signs11311 : ∀ j, Signs p11311 (bank11311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11312 := params 15
abbrev ray11312 := rays 15
def bank11312 : Fin 2 → Cell := twoBank p11312 ray11312
theorem signs11312 : ∀ j, Signs p11312 (bank11312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11313 := params 16
abbrev ray11313 := rays 16
def bank11313 : Fin 2 → Cell := twoBank p11313 ray11313
theorem signs11313 : ∀ j, Signs p11313 (bank11313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11314 := params 17
abbrev ray11314 := rays 17
def bank11314 : Fin 2 → Cell := twoBank p11314 ray11314
theorem signs11314 : ∀ j, Signs p11314 (bank11314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11315 := params 18
abbrev ray11315 := rays 18
def bank11315 : Fin 2 → Cell := twoBank p11315 ray11315
theorem signs11315 : ∀ j, Signs p11315 (bank11315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11316 := params 19
abbrev ray11316 := rays 19
def bank11316 : Fin 2 → Cell := twoBank p11316 ray11316
theorem signs11316 : ∀ j, Signs p11316 (bank11316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11317 := params 20
abbrev ray11317 := rays 20
def bank11317 : Fin 2 → Cell := twoBank p11317 ray11317
theorem signs11317 : ∀ j, Signs p11317 (bank11317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11318 := params 21
abbrev ray11318 := rays 21
def bank11318 : Fin 2 → Cell := twoBank p11318 ray11318
theorem signs11318 : ∀ j, Signs p11318 (bank11318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11319 := params 22
abbrev ray11319 := rays 22
def bank11319 : Fin 2 → Cell := twoBank p11319 ray11319
theorem signs11319 : ∀ j, Signs p11319 (bank11319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11320 := params 23
abbrev ray11320 := rays 23
def bank11320 : Fin 2 → Cell := twoBank p11320 ray11320
theorem signs11320 : ∀ j, Signs p11320 (bank11320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11321 := params 24
abbrev ray11321 := rays 24
def bank11321 : Fin 2 → Cell := twoBank p11321 ray11321
theorem signs11321 : ∀ j, Signs p11321 (bank11321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11322 := params 25
abbrev ray11322 := rays 25
def bank11322 : Fin 2 → Cell := twoBank p11322 ray11322
theorem signs11322 : ∀ j, Signs p11322 (bank11322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11323 := params 26
abbrev ray11323 := rays 26
def bank11323 : Fin 2 → Cell := twoBank p11323 ray11323
theorem signs11323 : ∀ j, Signs p11323 (bank11323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11324 := params 27
abbrev ray11324 := rays 27
def bank11324 : Fin 2 → Cell := twoBank p11324 ray11324
theorem signs11324 : ∀ j, Signs p11324 (bank11324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11325 := params 28
abbrev ray11325 := rays 28
def bank11325 : Fin 2 → Cell := twoBank p11325 ray11325
theorem signs11325 : ∀ j, Signs p11325 (bank11325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11326 := params 29
abbrev ray11326 := rays 29
def bank11326 : Fin 2 → Cell := twoBank p11326 ray11326
theorem signs11326 : ∀ j, Signs p11326 (bank11326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11327 := params 30
abbrev ray11327 := rays 30
def bank11327 : Fin 2 → Cell := twoBank p11327 ray11327
theorem signs11327 : ∀ j, Signs p11327 (bank11327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11328 := params 31
abbrev ray11328 := rays 31
def bank11328 : Fin 2 → Cell := twoBank p11328 ray11328
theorem signs11328 : ∀ j, Signs p11328 (bank11328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11297_11328
