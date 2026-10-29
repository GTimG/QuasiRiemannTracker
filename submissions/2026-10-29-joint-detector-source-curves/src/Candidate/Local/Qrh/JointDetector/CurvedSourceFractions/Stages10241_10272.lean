/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10241_10272
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97381174724992,97380803223800,97380431702402,97380060160799,97379688598991,97379317016979,97378945414764,97378573792345,97378202149724,97377830486901,97377458803876,97377087100650,97376715377224,97376343633598,97375971869773,97375600085749,97375228281527,97374856457107,97374484612490,97374112747676,97373740862666,97373368957460,97372997032059,97372625086464,97372253120675,97371881134692,97371509128516,97371137102148,97370765055588,97370392988837,97370020901895,97369648794763,97369276667441]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10240+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10241 := params 0
abbrev ray10241 := rays 0
def bank10241 : Fin 2 → Cell := twoBank p10241 ray10241
theorem signs10241 : ∀ j, Signs p10241 (bank10241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10242 := params 1
abbrev ray10242 := rays 1
def bank10242 : Fin 2 → Cell := twoBank p10242 ray10242
theorem signs10242 : ∀ j, Signs p10242 (bank10242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10243 := params 2
abbrev ray10243 := rays 2
def bank10243 : Fin 2 → Cell := twoBank p10243 ray10243
theorem signs10243 : ∀ j, Signs p10243 (bank10243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10244 := params 3
abbrev ray10244 := rays 3
def bank10244 : Fin 2 → Cell := twoBank p10244 ray10244
theorem signs10244 : ∀ j, Signs p10244 (bank10244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10245 := params 4
abbrev ray10245 := rays 4
def bank10245 : Fin 2 → Cell := twoBank p10245 ray10245
theorem signs10245 : ∀ j, Signs p10245 (bank10245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10246 := params 5
abbrev ray10246 := rays 5
def bank10246 : Fin 2 → Cell := twoBank p10246 ray10246
theorem signs10246 : ∀ j, Signs p10246 (bank10246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10247 := params 6
abbrev ray10247 := rays 6
def bank10247 : Fin 2 → Cell := twoBank p10247 ray10247
theorem signs10247 : ∀ j, Signs p10247 (bank10247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10248 := params 7
abbrev ray10248 := rays 7
def bank10248 : Fin 2 → Cell := twoBank p10248 ray10248
theorem signs10248 : ∀ j, Signs p10248 (bank10248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10249 := params 8
abbrev ray10249 := rays 8
def bank10249 : Fin 2 → Cell := twoBank p10249 ray10249
theorem signs10249 : ∀ j, Signs p10249 (bank10249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10250 := params 9
abbrev ray10250 := rays 9
def bank10250 : Fin 2 → Cell := twoBank p10250 ray10250
theorem signs10250 : ∀ j, Signs p10250 (bank10250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10251 := params 10
abbrev ray10251 := rays 10
def bank10251 : Fin 2 → Cell := twoBank p10251 ray10251
theorem signs10251 : ∀ j, Signs p10251 (bank10251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10252 := params 11
abbrev ray10252 := rays 11
def bank10252 : Fin 2 → Cell := twoBank p10252 ray10252
theorem signs10252 : ∀ j, Signs p10252 (bank10252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10253 := params 12
abbrev ray10253 := rays 12
def bank10253 : Fin 2 → Cell := twoBank p10253 ray10253
theorem signs10253 : ∀ j, Signs p10253 (bank10253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10254 := params 13
abbrev ray10254 := rays 13
def bank10254 : Fin 2 → Cell := twoBank p10254 ray10254
theorem signs10254 : ∀ j, Signs p10254 (bank10254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10255 := params 14
abbrev ray10255 := rays 14
def bank10255 : Fin 2 → Cell := twoBank p10255 ray10255
theorem signs10255 : ∀ j, Signs p10255 (bank10255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10256 := params 15
abbrev ray10256 := rays 15
def bank10256 : Fin 2 → Cell := twoBank p10256 ray10256
theorem signs10256 : ∀ j, Signs p10256 (bank10256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10257 := params 16
abbrev ray10257 := rays 16
def bank10257 : Fin 2 → Cell := twoBank p10257 ray10257
theorem signs10257 : ∀ j, Signs p10257 (bank10257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10258 := params 17
abbrev ray10258 := rays 17
def bank10258 : Fin 2 → Cell := twoBank p10258 ray10258
theorem signs10258 : ∀ j, Signs p10258 (bank10258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10259 := params 18
abbrev ray10259 := rays 18
def bank10259 : Fin 2 → Cell := twoBank p10259 ray10259
theorem signs10259 : ∀ j, Signs p10259 (bank10259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10260 := params 19
abbrev ray10260 := rays 19
def bank10260 : Fin 2 → Cell := twoBank p10260 ray10260
theorem signs10260 : ∀ j, Signs p10260 (bank10260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10261 := params 20
abbrev ray10261 := rays 20
def bank10261 : Fin 2 → Cell := twoBank p10261 ray10261
theorem signs10261 : ∀ j, Signs p10261 (bank10261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10262 := params 21
abbrev ray10262 := rays 21
def bank10262 : Fin 2 → Cell := twoBank p10262 ray10262
theorem signs10262 : ∀ j, Signs p10262 (bank10262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10263 := params 22
abbrev ray10263 := rays 22
def bank10263 : Fin 2 → Cell := twoBank p10263 ray10263
theorem signs10263 : ∀ j, Signs p10263 (bank10263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10264 := params 23
abbrev ray10264 := rays 23
def bank10264 : Fin 2 → Cell := twoBank p10264 ray10264
theorem signs10264 : ∀ j, Signs p10264 (bank10264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10265 := params 24
abbrev ray10265 := rays 24
def bank10265 : Fin 2 → Cell := twoBank p10265 ray10265
theorem signs10265 : ∀ j, Signs p10265 (bank10265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10266 := params 25
abbrev ray10266 := rays 25
def bank10266 : Fin 2 → Cell := twoBank p10266 ray10266
theorem signs10266 : ∀ j, Signs p10266 (bank10266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10267 := params 26
abbrev ray10267 := rays 26
def bank10267 : Fin 2 → Cell := twoBank p10267 ray10267
theorem signs10267 : ∀ j, Signs p10267 (bank10267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10268 := params 27
abbrev ray10268 := rays 27
def bank10268 : Fin 2 → Cell := twoBank p10268 ray10268
theorem signs10268 : ∀ j, Signs p10268 (bank10268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10269 := params 28
abbrev ray10269 := rays 28
def bank10269 : Fin 2 → Cell := twoBank p10269 ray10269
theorem signs10269 : ∀ j, Signs p10269 (bank10269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10270 := params 29
abbrev ray10270 := rays 29
def bank10270 : Fin 2 → Cell := twoBank p10270 ray10270
theorem signs10270 : ∀ j, Signs p10270 (bank10270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10271 := params 30
abbrev ray10271 := rays 30
def bank10271 : Fin 2 → Cell := twoBank p10271 ray10271
theorem signs10271 : ∀ j, Signs p10271 (bank10271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10272 := params 31
abbrev ray10272 := rays 31
def bank10272 : Fin 2 → Cell := twoBank p10272 ray10272
theorem signs10272 : ∀ j, Signs p10272 (bank10272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10241_10272
