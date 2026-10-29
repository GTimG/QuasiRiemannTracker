/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09281_09312
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97728413452091,97728061606300,97727709739756,97727357852460,97727005944413,97726654015615,97726302066066,97725950095767,97725598104719,97725246092923,97724894060379,97724542007087,97724189933049,97723837838264,97723485722734,97723133586459,97722781429440,97722429251677,97722077053171,97721724833922,97721372593931,97721020333199,97720668051726,97720315749513,97719963426560,97719611082868,97719258718438,97718906333270,97718553927365,97718201500724,97717849053347,97717496585234,97717144096387]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9280+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9281 := params 0
abbrev ray9281 := rays 0
def bank9281 : Fin 2 → Cell := twoBank p9281 ray9281
theorem signs9281 : ∀ j, Signs p9281 (bank9281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9282 := params 1
abbrev ray9282 := rays 1
def bank9282 : Fin 2 → Cell := twoBank p9282 ray9282
theorem signs9282 : ∀ j, Signs p9282 (bank9282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9283 := params 2
abbrev ray9283 := rays 2
def bank9283 : Fin 2 → Cell := twoBank p9283 ray9283
theorem signs9283 : ∀ j, Signs p9283 (bank9283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9284 := params 3
abbrev ray9284 := rays 3
def bank9284 : Fin 2 → Cell := twoBank p9284 ray9284
theorem signs9284 : ∀ j, Signs p9284 (bank9284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9285 := params 4
abbrev ray9285 := rays 4
def bank9285 : Fin 2 → Cell := twoBank p9285 ray9285
theorem signs9285 : ∀ j, Signs p9285 (bank9285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9286 := params 5
abbrev ray9286 := rays 5
def bank9286 : Fin 2 → Cell := twoBank p9286 ray9286
theorem signs9286 : ∀ j, Signs p9286 (bank9286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9287 := params 6
abbrev ray9287 := rays 6
def bank9287 : Fin 2 → Cell := twoBank p9287 ray9287
theorem signs9287 : ∀ j, Signs p9287 (bank9287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9288 := params 7
abbrev ray9288 := rays 7
def bank9288 : Fin 2 → Cell := twoBank p9288 ray9288
theorem signs9288 : ∀ j, Signs p9288 (bank9288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9289 := params 8
abbrev ray9289 := rays 8
def bank9289 : Fin 2 → Cell := twoBank p9289 ray9289
theorem signs9289 : ∀ j, Signs p9289 (bank9289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9290 := params 9
abbrev ray9290 := rays 9
def bank9290 : Fin 2 → Cell := twoBank p9290 ray9290
theorem signs9290 : ∀ j, Signs p9290 (bank9290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9291 := params 10
abbrev ray9291 := rays 10
def bank9291 : Fin 2 → Cell := twoBank p9291 ray9291
theorem signs9291 : ∀ j, Signs p9291 (bank9291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9292 := params 11
abbrev ray9292 := rays 11
def bank9292 : Fin 2 → Cell := twoBank p9292 ray9292
theorem signs9292 : ∀ j, Signs p9292 (bank9292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9293 := params 12
abbrev ray9293 := rays 12
def bank9293 : Fin 2 → Cell := twoBank p9293 ray9293
theorem signs9293 : ∀ j, Signs p9293 (bank9293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9294 := params 13
abbrev ray9294 := rays 13
def bank9294 : Fin 2 → Cell := twoBank p9294 ray9294
theorem signs9294 : ∀ j, Signs p9294 (bank9294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9295 := params 14
abbrev ray9295 := rays 14
def bank9295 : Fin 2 → Cell := twoBank p9295 ray9295
theorem signs9295 : ∀ j, Signs p9295 (bank9295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9296 := params 15
abbrev ray9296 := rays 15
def bank9296 : Fin 2 → Cell := twoBank p9296 ray9296
theorem signs9296 : ∀ j, Signs p9296 (bank9296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9297 := params 16
abbrev ray9297 := rays 16
def bank9297 : Fin 2 → Cell := twoBank p9297 ray9297
theorem signs9297 : ∀ j, Signs p9297 (bank9297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9298 := params 17
abbrev ray9298 := rays 17
def bank9298 : Fin 2 → Cell := twoBank p9298 ray9298
theorem signs9298 : ∀ j, Signs p9298 (bank9298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9299 := params 18
abbrev ray9299 := rays 18
def bank9299 : Fin 2 → Cell := twoBank p9299 ray9299
theorem signs9299 : ∀ j, Signs p9299 (bank9299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9300 := params 19
abbrev ray9300 := rays 19
def bank9300 : Fin 2 → Cell := twoBank p9300 ray9300
theorem signs9300 : ∀ j, Signs p9300 (bank9300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9301 := params 20
abbrev ray9301 := rays 20
def bank9301 : Fin 2 → Cell := twoBank p9301 ray9301
theorem signs9301 : ∀ j, Signs p9301 (bank9301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9302 := params 21
abbrev ray9302 := rays 21
def bank9302 : Fin 2 → Cell := twoBank p9302 ray9302
theorem signs9302 : ∀ j, Signs p9302 (bank9302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9303 := params 22
abbrev ray9303 := rays 22
def bank9303 : Fin 2 → Cell := twoBank p9303 ray9303
theorem signs9303 : ∀ j, Signs p9303 (bank9303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9304 := params 23
abbrev ray9304 := rays 23
def bank9304 : Fin 2 → Cell := twoBank p9304 ray9304
theorem signs9304 : ∀ j, Signs p9304 (bank9304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9305 := params 24
abbrev ray9305 := rays 24
def bank9305 : Fin 2 → Cell := twoBank p9305 ray9305
theorem signs9305 : ∀ j, Signs p9305 (bank9305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9306 := params 25
abbrev ray9306 := rays 25
def bank9306 : Fin 2 → Cell := twoBank p9306 ray9306
theorem signs9306 : ∀ j, Signs p9306 (bank9306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9307 := params 26
abbrev ray9307 := rays 26
def bank9307 : Fin 2 → Cell := twoBank p9307 ray9307
theorem signs9307 : ∀ j, Signs p9307 (bank9307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9308 := params 27
abbrev ray9308 := rays 27
def bank9308 : Fin 2 → Cell := twoBank p9308 ray9308
theorem signs9308 : ∀ j, Signs p9308 (bank9308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9309 := params 28
abbrev ray9309 := rays 28
def bank9309 : Fin 2 → Cell := twoBank p9309 ray9309
theorem signs9309 : ∀ j, Signs p9309 (bank9309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9310 := params 29
abbrev ray9310 := rays 29
def bank9310 : Fin 2 → Cell := twoBank p9310 ray9310
theorem signs9310 : ∀ j, Signs p9310 (bank9310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9311 := params 30
abbrev ray9311 := rays 30
def bank9311 : Fin 2 → Cell := twoBank p9311 ray9311
theorem signs9311 : ∀ j, Signs p9311 (bank9311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9312 := params 31
abbrev ray9312 := rays 31
def bank9312 : Fin 2 → Cell := twoBank p9312 ray9312
theorem signs9312 : ∀ j, Signs p9312 (bank9312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09281_09312
