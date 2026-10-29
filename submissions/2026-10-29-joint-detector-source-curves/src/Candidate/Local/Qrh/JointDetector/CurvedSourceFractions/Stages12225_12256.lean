/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12225_12256
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96605027229667,96604616617040,96604205985153,96603795334006,96603384663600,96602973973936,96602563265014,96602152536834,96601741789397,96601331022703,96600920236753,96600509431547,96600098607085,96599687763368,96599276900396,96598866018170,96598455116690,96598044195956,96597633255969,96597222296730,96596811318238,96596400320494,96595989303499,96595578267253,96595167211756,96594756137009,96594345043013,96593933929767,96593522797272,96593111645529,96592700474538,96592289284299,96591878074813]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12224+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12225 := params 0
abbrev ray12225 := rays 0
def bank12225 : Fin 2 → Cell := twoBank p12225 ray12225
theorem signs12225 : ∀ j, Signs p12225 (bank12225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12226 := params 1
abbrev ray12226 := rays 1
def bank12226 : Fin 2 → Cell := twoBank p12226 ray12226
theorem signs12226 : ∀ j, Signs p12226 (bank12226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12227 := params 2
abbrev ray12227 := rays 2
def bank12227 : Fin 2 → Cell := twoBank p12227 ray12227
theorem signs12227 : ∀ j, Signs p12227 (bank12227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12228 := params 3
abbrev ray12228 := rays 3
def bank12228 : Fin 2 → Cell := twoBank p12228 ray12228
theorem signs12228 : ∀ j, Signs p12228 (bank12228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12229 := params 4
abbrev ray12229 := rays 4
def bank12229 : Fin 2 → Cell := twoBank p12229 ray12229
theorem signs12229 : ∀ j, Signs p12229 (bank12229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12230 := params 5
abbrev ray12230 := rays 5
def bank12230 : Fin 2 → Cell := twoBank p12230 ray12230
theorem signs12230 : ∀ j, Signs p12230 (bank12230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12231 := params 6
abbrev ray12231 := rays 6
def bank12231 : Fin 2 → Cell := twoBank p12231 ray12231
theorem signs12231 : ∀ j, Signs p12231 (bank12231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12232 := params 7
abbrev ray12232 := rays 7
def bank12232 : Fin 2 → Cell := twoBank p12232 ray12232
theorem signs12232 : ∀ j, Signs p12232 (bank12232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12233 := params 8
abbrev ray12233 := rays 8
def bank12233 : Fin 2 → Cell := twoBank p12233 ray12233
theorem signs12233 : ∀ j, Signs p12233 (bank12233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12234 := params 9
abbrev ray12234 := rays 9
def bank12234 : Fin 2 → Cell := twoBank p12234 ray12234
theorem signs12234 : ∀ j, Signs p12234 (bank12234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12235 := params 10
abbrev ray12235 := rays 10
def bank12235 : Fin 2 → Cell := twoBank p12235 ray12235
theorem signs12235 : ∀ j, Signs p12235 (bank12235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12236 := params 11
abbrev ray12236 := rays 11
def bank12236 : Fin 2 → Cell := twoBank p12236 ray12236
theorem signs12236 : ∀ j, Signs p12236 (bank12236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12237 := params 12
abbrev ray12237 := rays 12
def bank12237 : Fin 2 → Cell := twoBank p12237 ray12237
theorem signs12237 : ∀ j, Signs p12237 (bank12237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12238 := params 13
abbrev ray12238 := rays 13
def bank12238 : Fin 2 → Cell := twoBank p12238 ray12238
theorem signs12238 : ∀ j, Signs p12238 (bank12238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12239 := params 14
abbrev ray12239 := rays 14
def bank12239 : Fin 2 → Cell := twoBank p12239 ray12239
theorem signs12239 : ∀ j, Signs p12239 (bank12239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12240 := params 15
abbrev ray12240 := rays 15
def bank12240 : Fin 2 → Cell := twoBank p12240 ray12240
theorem signs12240 : ∀ j, Signs p12240 (bank12240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12241 := params 16
abbrev ray12241 := rays 16
def bank12241 : Fin 2 → Cell := twoBank p12241 ray12241
theorem signs12241 : ∀ j, Signs p12241 (bank12241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12242 := params 17
abbrev ray12242 := rays 17
def bank12242 : Fin 2 → Cell := twoBank p12242 ray12242
theorem signs12242 : ∀ j, Signs p12242 (bank12242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12243 := params 18
abbrev ray12243 := rays 18
def bank12243 : Fin 2 → Cell := twoBank p12243 ray12243
theorem signs12243 : ∀ j, Signs p12243 (bank12243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12244 := params 19
abbrev ray12244 := rays 19
def bank12244 : Fin 2 → Cell := twoBank p12244 ray12244
theorem signs12244 : ∀ j, Signs p12244 (bank12244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12245 := params 20
abbrev ray12245 := rays 20
def bank12245 : Fin 2 → Cell := twoBank p12245 ray12245
theorem signs12245 : ∀ j, Signs p12245 (bank12245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12246 := params 21
abbrev ray12246 := rays 21
def bank12246 : Fin 2 → Cell := twoBank p12246 ray12246
theorem signs12246 : ∀ j, Signs p12246 (bank12246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12247 := params 22
abbrev ray12247 := rays 22
def bank12247 : Fin 2 → Cell := twoBank p12247 ray12247
theorem signs12247 : ∀ j, Signs p12247 (bank12247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12248 := params 23
abbrev ray12248 := rays 23
def bank12248 : Fin 2 → Cell := twoBank p12248 ray12248
theorem signs12248 : ∀ j, Signs p12248 (bank12248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12249 := params 24
abbrev ray12249 := rays 24
def bank12249 : Fin 2 → Cell := twoBank p12249 ray12249
theorem signs12249 : ∀ j, Signs p12249 (bank12249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12250 := params 25
abbrev ray12250 := rays 25
def bank12250 : Fin 2 → Cell := twoBank p12250 ray12250
theorem signs12250 : ∀ j, Signs p12250 (bank12250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12251 := params 26
abbrev ray12251 := rays 26
def bank12251 : Fin 2 → Cell := twoBank p12251 ray12251
theorem signs12251 : ∀ j, Signs p12251 (bank12251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12252 := params 27
abbrev ray12252 := rays 27
def bank12252 : Fin 2 → Cell := twoBank p12252 ray12252
theorem signs12252 : ∀ j, Signs p12252 (bank12252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12253 := params 28
abbrev ray12253 := rays 28
def bank12253 : Fin 2 → Cell := twoBank p12253 ray12253
theorem signs12253 : ∀ j, Signs p12253 (bank12253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12254 := params 29
abbrev ray12254 := rays 29
def bank12254 : Fin 2 → Cell := twoBank p12254 ray12254
theorem signs12254 : ∀ j, Signs p12254 (bank12254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12255 := params 30
abbrev ray12255 := rays 30
def bank12255 : Fin 2 → Cell := twoBank p12255 ray12255
theorem signs12255 : ∀ j, Signs p12255 (bank12255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12256 := params 31
abbrev ray12256 := rays 31
def bank12256 : Fin 2 → Cell := twoBank p12256 ray12256
theorem signs12256 : ∀ j, Signs p12256 (bank12256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12225_12256
