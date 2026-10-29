/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10305_10336
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97357357936170,97356985142888,97356612329434,97356239495809,97355866642014,97355493768049,97355120873914,97354747959611,97354375025139,97354002070499,97353629095692,97353256100718,97352883085578,97352510050273,97352136994802,97351763919167,97351390823368,97351017707405,97350644571279,97350271414991,97349898238541,97349525041929,97349151825157,97348778588224,97348405331131,97348032053879,97347658756468,97347285438899,97346912101173,97346538743289,97346165365249,97345791967053,97345418548701]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10304+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10305 := params 0
abbrev ray10305 := rays 0
def bank10305 : Fin 2 → Cell := twoBank p10305 ray10305
theorem signs10305 : ∀ j, Signs p10305 (bank10305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10306 := params 1
abbrev ray10306 := rays 1
def bank10306 : Fin 2 → Cell := twoBank p10306 ray10306
theorem signs10306 : ∀ j, Signs p10306 (bank10306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10307 := params 2
abbrev ray10307 := rays 2
def bank10307 : Fin 2 → Cell := twoBank p10307 ray10307
theorem signs10307 : ∀ j, Signs p10307 (bank10307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10308 := params 3
abbrev ray10308 := rays 3
def bank10308 : Fin 2 → Cell := twoBank p10308 ray10308
theorem signs10308 : ∀ j, Signs p10308 (bank10308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10309 := params 4
abbrev ray10309 := rays 4
def bank10309 : Fin 2 → Cell := twoBank p10309 ray10309
theorem signs10309 : ∀ j, Signs p10309 (bank10309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10310 := params 5
abbrev ray10310 := rays 5
def bank10310 : Fin 2 → Cell := twoBank p10310 ray10310
theorem signs10310 : ∀ j, Signs p10310 (bank10310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10311 := params 6
abbrev ray10311 := rays 6
def bank10311 : Fin 2 → Cell := twoBank p10311 ray10311
theorem signs10311 : ∀ j, Signs p10311 (bank10311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10312 := params 7
abbrev ray10312 := rays 7
def bank10312 : Fin 2 → Cell := twoBank p10312 ray10312
theorem signs10312 : ∀ j, Signs p10312 (bank10312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10313 := params 8
abbrev ray10313 := rays 8
def bank10313 : Fin 2 → Cell := twoBank p10313 ray10313
theorem signs10313 : ∀ j, Signs p10313 (bank10313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10314 := params 9
abbrev ray10314 := rays 9
def bank10314 : Fin 2 → Cell := twoBank p10314 ray10314
theorem signs10314 : ∀ j, Signs p10314 (bank10314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10315 := params 10
abbrev ray10315 := rays 10
def bank10315 : Fin 2 → Cell := twoBank p10315 ray10315
theorem signs10315 : ∀ j, Signs p10315 (bank10315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10316 := params 11
abbrev ray10316 := rays 11
def bank10316 : Fin 2 → Cell := twoBank p10316 ray10316
theorem signs10316 : ∀ j, Signs p10316 (bank10316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10317 := params 12
abbrev ray10317 := rays 12
def bank10317 : Fin 2 → Cell := twoBank p10317 ray10317
theorem signs10317 : ∀ j, Signs p10317 (bank10317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10318 := params 13
abbrev ray10318 := rays 13
def bank10318 : Fin 2 → Cell := twoBank p10318 ray10318
theorem signs10318 : ∀ j, Signs p10318 (bank10318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10319 := params 14
abbrev ray10319 := rays 14
def bank10319 : Fin 2 → Cell := twoBank p10319 ray10319
theorem signs10319 : ∀ j, Signs p10319 (bank10319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10320 := params 15
abbrev ray10320 := rays 15
def bank10320 : Fin 2 → Cell := twoBank p10320 ray10320
theorem signs10320 : ∀ j, Signs p10320 (bank10320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10321 := params 16
abbrev ray10321 := rays 16
def bank10321 : Fin 2 → Cell := twoBank p10321 ray10321
theorem signs10321 : ∀ j, Signs p10321 (bank10321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10322 := params 17
abbrev ray10322 := rays 17
def bank10322 : Fin 2 → Cell := twoBank p10322 ray10322
theorem signs10322 : ∀ j, Signs p10322 (bank10322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10323 := params 18
abbrev ray10323 := rays 18
def bank10323 : Fin 2 → Cell := twoBank p10323 ray10323
theorem signs10323 : ∀ j, Signs p10323 (bank10323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10324 := params 19
abbrev ray10324 := rays 19
def bank10324 : Fin 2 → Cell := twoBank p10324 ray10324
theorem signs10324 : ∀ j, Signs p10324 (bank10324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10325 := params 20
abbrev ray10325 := rays 20
def bank10325 : Fin 2 → Cell := twoBank p10325 ray10325
theorem signs10325 : ∀ j, Signs p10325 (bank10325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10326 := params 21
abbrev ray10326 := rays 21
def bank10326 : Fin 2 → Cell := twoBank p10326 ray10326
theorem signs10326 : ∀ j, Signs p10326 (bank10326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10327 := params 22
abbrev ray10327 := rays 22
def bank10327 : Fin 2 → Cell := twoBank p10327 ray10327
theorem signs10327 : ∀ j, Signs p10327 (bank10327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10328 := params 23
abbrev ray10328 := rays 23
def bank10328 : Fin 2 → Cell := twoBank p10328 ray10328
theorem signs10328 : ∀ j, Signs p10328 (bank10328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10329 := params 24
abbrev ray10329 := rays 24
def bank10329 : Fin 2 → Cell := twoBank p10329 ray10329
theorem signs10329 : ∀ j, Signs p10329 (bank10329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10330 := params 25
abbrev ray10330 := rays 25
def bank10330 : Fin 2 → Cell := twoBank p10330 ray10330
theorem signs10330 : ∀ j, Signs p10330 (bank10330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10331 := params 26
abbrev ray10331 := rays 26
def bank10331 : Fin 2 → Cell := twoBank p10331 ray10331
theorem signs10331 : ∀ j, Signs p10331 (bank10331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10332 := params 27
abbrev ray10332 := rays 27
def bank10332 : Fin 2 → Cell := twoBank p10332 ray10332
theorem signs10332 : ∀ j, Signs p10332 (bank10332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10333 := params 28
abbrev ray10333 := rays 28
def bank10333 : Fin 2 → Cell := twoBank p10333 ray10333
theorem signs10333 : ∀ j, Signs p10333 (bank10333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10334 := params 29
abbrev ray10334 := rays 29
def bank10334 : Fin 2 → Cell := twoBank p10334 ray10334
theorem signs10334 : ∀ j, Signs p10334 (bank10334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10335 := params 30
abbrev ray10335 := rays 30
def bank10335 : Fin 2 → Cell := twoBank p10335 ray10335
theorem signs10335 : ∀ j, Signs p10335 (bank10335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10336 := params 31
abbrev ray10336 := rays 31
def bank10336 : Fin 2 → Cell := twoBank p10336 ray10336
theorem signs10336 : ∀ j, Signs p10336 (bank10336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10305_10336
