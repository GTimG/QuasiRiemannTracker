/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10273_10304
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97369276667441,97368904519930,97368532352230,97368160164342,97367787956266,97367415728003,97367043479554,97366671210919,97366298922099,97365926613094,97365554283904,97365181934530,97364809564973,97364437175233,97364064765311,97363692335208,97363319884923,97362947414458,97362574923813,97362202412988,97361829881984,97361457330802,97361084759442,97360712167904,97360339556190,97359966924299,97359594272232,97359221599990,97358848907573,97358476194982,97358103462218,97357730709280,97357357936170]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10272+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10273 := params 0
abbrev ray10273 := rays 0
def bank10273 : Fin 2 → Cell := twoBank p10273 ray10273
theorem signs10273 : ∀ j, Signs p10273 (bank10273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10274 := params 1
abbrev ray10274 := rays 1
def bank10274 : Fin 2 → Cell := twoBank p10274 ray10274
theorem signs10274 : ∀ j, Signs p10274 (bank10274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10275 := params 2
abbrev ray10275 := rays 2
def bank10275 : Fin 2 → Cell := twoBank p10275 ray10275
theorem signs10275 : ∀ j, Signs p10275 (bank10275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10276 := params 3
abbrev ray10276 := rays 3
def bank10276 : Fin 2 → Cell := twoBank p10276 ray10276
theorem signs10276 : ∀ j, Signs p10276 (bank10276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10277 := params 4
abbrev ray10277 := rays 4
def bank10277 : Fin 2 → Cell := twoBank p10277 ray10277
theorem signs10277 : ∀ j, Signs p10277 (bank10277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10278 := params 5
abbrev ray10278 := rays 5
def bank10278 : Fin 2 → Cell := twoBank p10278 ray10278
theorem signs10278 : ∀ j, Signs p10278 (bank10278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10279 := params 6
abbrev ray10279 := rays 6
def bank10279 : Fin 2 → Cell := twoBank p10279 ray10279
theorem signs10279 : ∀ j, Signs p10279 (bank10279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10280 := params 7
abbrev ray10280 := rays 7
def bank10280 : Fin 2 → Cell := twoBank p10280 ray10280
theorem signs10280 : ∀ j, Signs p10280 (bank10280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10281 := params 8
abbrev ray10281 := rays 8
def bank10281 : Fin 2 → Cell := twoBank p10281 ray10281
theorem signs10281 : ∀ j, Signs p10281 (bank10281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10282 := params 9
abbrev ray10282 := rays 9
def bank10282 : Fin 2 → Cell := twoBank p10282 ray10282
theorem signs10282 : ∀ j, Signs p10282 (bank10282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10283 := params 10
abbrev ray10283 := rays 10
def bank10283 : Fin 2 → Cell := twoBank p10283 ray10283
theorem signs10283 : ∀ j, Signs p10283 (bank10283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10284 := params 11
abbrev ray10284 := rays 11
def bank10284 : Fin 2 → Cell := twoBank p10284 ray10284
theorem signs10284 : ∀ j, Signs p10284 (bank10284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10285 := params 12
abbrev ray10285 := rays 12
def bank10285 : Fin 2 → Cell := twoBank p10285 ray10285
theorem signs10285 : ∀ j, Signs p10285 (bank10285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10286 := params 13
abbrev ray10286 := rays 13
def bank10286 : Fin 2 → Cell := twoBank p10286 ray10286
theorem signs10286 : ∀ j, Signs p10286 (bank10286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10287 := params 14
abbrev ray10287 := rays 14
def bank10287 : Fin 2 → Cell := twoBank p10287 ray10287
theorem signs10287 : ∀ j, Signs p10287 (bank10287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10288 := params 15
abbrev ray10288 := rays 15
def bank10288 : Fin 2 → Cell := twoBank p10288 ray10288
theorem signs10288 : ∀ j, Signs p10288 (bank10288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10289 := params 16
abbrev ray10289 := rays 16
def bank10289 : Fin 2 → Cell := twoBank p10289 ray10289
theorem signs10289 : ∀ j, Signs p10289 (bank10289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10290 := params 17
abbrev ray10290 := rays 17
def bank10290 : Fin 2 → Cell := twoBank p10290 ray10290
theorem signs10290 : ∀ j, Signs p10290 (bank10290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10291 := params 18
abbrev ray10291 := rays 18
def bank10291 : Fin 2 → Cell := twoBank p10291 ray10291
theorem signs10291 : ∀ j, Signs p10291 (bank10291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10292 := params 19
abbrev ray10292 := rays 19
def bank10292 : Fin 2 → Cell := twoBank p10292 ray10292
theorem signs10292 : ∀ j, Signs p10292 (bank10292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10293 := params 20
abbrev ray10293 := rays 20
def bank10293 : Fin 2 → Cell := twoBank p10293 ray10293
theorem signs10293 : ∀ j, Signs p10293 (bank10293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10294 := params 21
abbrev ray10294 := rays 21
def bank10294 : Fin 2 → Cell := twoBank p10294 ray10294
theorem signs10294 : ∀ j, Signs p10294 (bank10294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10295 := params 22
abbrev ray10295 := rays 22
def bank10295 : Fin 2 → Cell := twoBank p10295 ray10295
theorem signs10295 : ∀ j, Signs p10295 (bank10295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10296 := params 23
abbrev ray10296 := rays 23
def bank10296 : Fin 2 → Cell := twoBank p10296 ray10296
theorem signs10296 : ∀ j, Signs p10296 (bank10296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10297 := params 24
abbrev ray10297 := rays 24
def bank10297 : Fin 2 → Cell := twoBank p10297 ray10297
theorem signs10297 : ∀ j, Signs p10297 (bank10297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10298 := params 25
abbrev ray10298 := rays 25
def bank10298 : Fin 2 → Cell := twoBank p10298 ray10298
theorem signs10298 : ∀ j, Signs p10298 (bank10298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10299 := params 26
abbrev ray10299 := rays 26
def bank10299 : Fin 2 → Cell := twoBank p10299 ray10299
theorem signs10299 : ∀ j, Signs p10299 (bank10299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10300 := params 27
abbrev ray10300 := rays 27
def bank10300 : Fin 2 → Cell := twoBank p10300 ray10300
theorem signs10300 : ∀ j, Signs p10300 (bank10300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10301 := params 28
abbrev ray10301 := rays 28
def bank10301 : Fin 2 → Cell := twoBank p10301 ray10301
theorem signs10301 : ∀ j, Signs p10301 (bank10301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10302 := params 29
abbrev ray10302 := rays 29
def bank10302 : Fin 2 → Cell := twoBank p10302 ray10302
theorem signs10302 : ∀ j, Signs p10302 (bank10302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10303 := params 30
abbrev ray10303 := rays 30
def bank10303 : Fin 2 → Cell := twoBank p10303 ray10303
theorem signs10303 : ∀ j, Signs p10303 (bank10303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10304 := params 31
abbrev ray10304 := rays 31
def bank10304 : Fin 2 → Cell := twoBank p10304 ray10304
theorem signs10304 : ∀ j, Signs p10304 (bank10304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10273_10304
