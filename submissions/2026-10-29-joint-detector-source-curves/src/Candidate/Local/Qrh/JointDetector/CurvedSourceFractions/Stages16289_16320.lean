/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16289_16320
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94795970641622,94795492660774,94795014663942,94794536651125,94794058622323,94793580577536,94793102516765,94792624440009,94792146347268,94791668238543,94791190113833,94790711973138,94790233816459,94789755643795,94789277455146,94788799250513,94788321029895,94787842793293,94787364540706,94786886272134,94786407987578,94785929687037,94785451370512,94784973038002,94784494689508,94784016325029,94783537944566,94783059548118,94782581135686,94782102707270,94781624262869,94781145802484,94780667326114]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16288+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16289 := params 0
abbrev ray16289 := rays 0
def bank16289 : Fin 1 → Cell := oneBank p16289 ray16289
theorem signs16289 : ∀ j, Signs p16289 (bank16289 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16290 := params 1
abbrev ray16290 := rays 1
def bank16290 : Fin 1 → Cell := oneBank p16290 ray16290
theorem signs16290 : ∀ j, Signs p16290 (bank16290 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16291 := params 2
abbrev ray16291 := rays 2
def bank16291 : Fin 1 → Cell := oneBank p16291 ray16291
theorem signs16291 : ∀ j, Signs p16291 (bank16291 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16292 := params 3
abbrev ray16292 := rays 3
def bank16292 : Fin 1 → Cell := oneBank p16292 ray16292
theorem signs16292 : ∀ j, Signs p16292 (bank16292 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16293 := params 4
abbrev ray16293 := rays 4
def bank16293 : Fin 1 → Cell := oneBank p16293 ray16293
theorem signs16293 : ∀ j, Signs p16293 (bank16293 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16294 := params 5
abbrev ray16294 := rays 5
def bank16294 : Fin 1 → Cell := oneBank p16294 ray16294
theorem signs16294 : ∀ j, Signs p16294 (bank16294 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16295 := params 6
abbrev ray16295 := rays 6
def bank16295 : Fin 1 → Cell := oneBank p16295 ray16295
theorem signs16295 : ∀ j, Signs p16295 (bank16295 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16296 := params 7
abbrev ray16296 := rays 7
def bank16296 : Fin 1 → Cell := oneBank p16296 ray16296
theorem signs16296 : ∀ j, Signs p16296 (bank16296 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16297 := params 8
abbrev ray16297 := rays 8
def bank16297 : Fin 1 → Cell := oneBank p16297 ray16297
theorem signs16297 : ∀ j, Signs p16297 (bank16297 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16298 := params 9
abbrev ray16298 := rays 9
def bank16298 : Fin 1 → Cell := oneBank p16298 ray16298
theorem signs16298 : ∀ j, Signs p16298 (bank16298 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16299 := params 10
abbrev ray16299 := rays 10
def bank16299 : Fin 1 → Cell := oneBank p16299 ray16299
theorem signs16299 : ∀ j, Signs p16299 (bank16299 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16300 := params 11
abbrev ray16300 := rays 11
def bank16300 : Fin 1 → Cell := oneBank p16300 ray16300
theorem signs16300 : ∀ j, Signs p16300 (bank16300 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16301 := params 12
abbrev ray16301 := rays 12
def bank16301 : Fin 1 → Cell := oneBank p16301 ray16301
theorem signs16301 : ∀ j, Signs p16301 (bank16301 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16302 := params 13
abbrev ray16302 := rays 13
def bank16302 : Fin 1 → Cell := oneBank p16302 ray16302
theorem signs16302 : ∀ j, Signs p16302 (bank16302 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16303 := params 14
abbrev ray16303 := rays 14
def bank16303 : Fin 1 → Cell := oneBank p16303 ray16303
theorem signs16303 : ∀ j, Signs p16303 (bank16303 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16304 := params 15
abbrev ray16304 := rays 15
def bank16304 : Fin 1 → Cell := oneBank p16304 ray16304
theorem signs16304 : ∀ j, Signs p16304 (bank16304 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16305 := params 16
abbrev ray16305 := rays 16
def bank16305 : Fin 1 → Cell := oneBank p16305 ray16305
theorem signs16305 : ∀ j, Signs p16305 (bank16305 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16306 := params 17
abbrev ray16306 := rays 17
def bank16306 : Fin 1 → Cell := oneBank p16306 ray16306
theorem signs16306 : ∀ j, Signs p16306 (bank16306 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16307 := params 18
abbrev ray16307 := rays 18
def bank16307 : Fin 1 → Cell := oneBank p16307 ray16307
theorem signs16307 : ∀ j, Signs p16307 (bank16307 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16308 := params 19
abbrev ray16308 := rays 19
def bank16308 : Fin 1 → Cell := oneBank p16308 ray16308
theorem signs16308 : ∀ j, Signs p16308 (bank16308 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16309 := params 20
abbrev ray16309 := rays 20
def bank16309 : Fin 1 → Cell := oneBank p16309 ray16309
theorem signs16309 : ∀ j, Signs p16309 (bank16309 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16310 := params 21
abbrev ray16310 := rays 21
def bank16310 : Fin 1 → Cell := oneBank p16310 ray16310
theorem signs16310 : ∀ j, Signs p16310 (bank16310 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16311 := params 22
abbrev ray16311 := rays 22
def bank16311 : Fin 1 → Cell := oneBank p16311 ray16311
theorem signs16311 : ∀ j, Signs p16311 (bank16311 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16312 := params 23
abbrev ray16312 := rays 23
def bank16312 : Fin 1 → Cell := oneBank p16312 ray16312
theorem signs16312 : ∀ j, Signs p16312 (bank16312 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16313 := params 24
abbrev ray16313 := rays 24
def bank16313 : Fin 1 → Cell := oneBank p16313 ray16313
theorem signs16313 : ∀ j, Signs p16313 (bank16313 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16314 := params 25
abbrev ray16314 := rays 25
def bank16314 : Fin 1 → Cell := oneBank p16314 ray16314
theorem signs16314 : ∀ j, Signs p16314 (bank16314 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16315 := params 26
abbrev ray16315 := rays 26
def bank16315 : Fin 1 → Cell := oneBank p16315 ray16315
theorem signs16315 : ∀ j, Signs p16315 (bank16315 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16316 := params 27
abbrev ray16316 := rays 27
def bank16316 : Fin 1 → Cell := oneBank p16316 ray16316
theorem signs16316 : ∀ j, Signs p16316 (bank16316 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16317 := params 28
abbrev ray16317 := rays 28
def bank16317 : Fin 1 → Cell := oneBank p16317 ray16317
theorem signs16317 : ∀ j, Signs p16317 (bank16317 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16318 := params 29
abbrev ray16318 := rays 29
def bank16318 : Fin 1 → Cell := oneBank p16318 ray16318
theorem signs16318 : ∀ j, Signs p16318 (bank16318 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16319 := params 30
abbrev ray16319 := rays 30
def bank16319 : Fin 1 → Cell := oneBank p16319 ray16319
theorem signs16319 : ∀ j, Signs p16319 (bank16319 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16320 := params 31
abbrev ray16320 := rays 31
def bank16320 : Fin 1 → Cell := oneBank p16320 ray16320
theorem signs16320 : ∀ j, Signs p16320 (bank16320 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16289_16320
