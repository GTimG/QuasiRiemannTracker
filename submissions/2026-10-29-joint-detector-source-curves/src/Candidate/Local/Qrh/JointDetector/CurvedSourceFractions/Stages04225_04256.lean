/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04225_04256
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99226871830175,99226634392616,99226396930145,99226159442762,99225921930468,99225684393264,99225446831152,99225209244132,99224971632206,99224733995375,99224496333640,99224258647001,99224020935460,99223783199019,99223545437678,99223307651438,99223069840300,99222832004266,99222594143337,99222356257513,99222118346796,99221880411187,99221642450687,99221404465297,99221166455018,99220928419851,99220690359797,99220452274858,99220214165034,99219976030327,99219737870738,99219499686267,99219261476916]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4224+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4225 := params 0
abbrev ray4225 := rays 0
def bank4225 : Fin 2 → Cell := twoBank p4225 ray4225
theorem signs4225 : ∀ j, Signs p4225 (bank4225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4226 := params 1
abbrev ray4226 := rays 1
def bank4226 : Fin 2 → Cell := twoBank p4226 ray4226
theorem signs4226 : ∀ j, Signs p4226 (bank4226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4227 := params 2
abbrev ray4227 := rays 2
def bank4227 : Fin 2 → Cell := twoBank p4227 ray4227
theorem signs4227 : ∀ j, Signs p4227 (bank4227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4228 := params 3
abbrev ray4228 := rays 3
def bank4228 : Fin 2 → Cell := twoBank p4228 ray4228
theorem signs4228 : ∀ j, Signs p4228 (bank4228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4229 := params 4
abbrev ray4229 := rays 4
def bank4229 : Fin 2 → Cell := twoBank p4229 ray4229
theorem signs4229 : ∀ j, Signs p4229 (bank4229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4230 := params 5
abbrev ray4230 := rays 5
def bank4230 : Fin 2 → Cell := twoBank p4230 ray4230
theorem signs4230 : ∀ j, Signs p4230 (bank4230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4231 := params 6
abbrev ray4231 := rays 6
def bank4231 : Fin 2 → Cell := twoBank p4231 ray4231
theorem signs4231 : ∀ j, Signs p4231 (bank4231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4232 := params 7
abbrev ray4232 := rays 7
def bank4232 : Fin 2 → Cell := twoBank p4232 ray4232
theorem signs4232 : ∀ j, Signs p4232 (bank4232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4233 := params 8
abbrev ray4233 := rays 8
def bank4233 : Fin 2 → Cell := twoBank p4233 ray4233
theorem signs4233 : ∀ j, Signs p4233 (bank4233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4234 := params 9
abbrev ray4234 := rays 9
def bank4234 : Fin 2 → Cell := twoBank p4234 ray4234
theorem signs4234 : ∀ j, Signs p4234 (bank4234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4235 := params 10
abbrev ray4235 := rays 10
def bank4235 : Fin 2 → Cell := twoBank p4235 ray4235
theorem signs4235 : ∀ j, Signs p4235 (bank4235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4236 := params 11
abbrev ray4236 := rays 11
def bank4236 : Fin 2 → Cell := twoBank p4236 ray4236
theorem signs4236 : ∀ j, Signs p4236 (bank4236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4237 := params 12
abbrev ray4237 := rays 12
def bank4237 : Fin 2 → Cell := twoBank p4237 ray4237
theorem signs4237 : ∀ j, Signs p4237 (bank4237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4238 := params 13
abbrev ray4238 := rays 13
def bank4238 : Fin 2 → Cell := twoBank p4238 ray4238
theorem signs4238 : ∀ j, Signs p4238 (bank4238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4239 := params 14
abbrev ray4239 := rays 14
def bank4239 : Fin 2 → Cell := twoBank p4239 ray4239
theorem signs4239 : ∀ j, Signs p4239 (bank4239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4240 := params 15
abbrev ray4240 := rays 15
def bank4240 : Fin 2 → Cell := twoBank p4240 ray4240
theorem signs4240 : ∀ j, Signs p4240 (bank4240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4241 := params 16
abbrev ray4241 := rays 16
def bank4241 : Fin 2 → Cell := twoBank p4241 ray4241
theorem signs4241 : ∀ j, Signs p4241 (bank4241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4242 := params 17
abbrev ray4242 := rays 17
def bank4242 : Fin 2 → Cell := twoBank p4242 ray4242
theorem signs4242 : ∀ j, Signs p4242 (bank4242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4243 := params 18
abbrev ray4243 := rays 18
def bank4243 : Fin 2 → Cell := twoBank p4243 ray4243
theorem signs4243 : ∀ j, Signs p4243 (bank4243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4244 := params 19
abbrev ray4244 := rays 19
def bank4244 : Fin 2 → Cell := twoBank p4244 ray4244
theorem signs4244 : ∀ j, Signs p4244 (bank4244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4245 := params 20
abbrev ray4245 := rays 20
def bank4245 : Fin 2 → Cell := twoBank p4245 ray4245
theorem signs4245 : ∀ j, Signs p4245 (bank4245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4246 := params 21
abbrev ray4246 := rays 21
def bank4246 : Fin 2 → Cell := twoBank p4246 ray4246
theorem signs4246 : ∀ j, Signs p4246 (bank4246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4247 := params 22
abbrev ray4247 := rays 22
def bank4247 : Fin 2 → Cell := twoBank p4247 ray4247
theorem signs4247 : ∀ j, Signs p4247 (bank4247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4248 := params 23
abbrev ray4248 := rays 23
def bank4248 : Fin 2 → Cell := twoBank p4248 ray4248
theorem signs4248 : ∀ j, Signs p4248 (bank4248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4249 := params 24
abbrev ray4249 := rays 24
def bank4249 : Fin 2 → Cell := twoBank p4249 ray4249
theorem signs4249 : ∀ j, Signs p4249 (bank4249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4250 := params 25
abbrev ray4250 := rays 25
def bank4250 : Fin 2 → Cell := twoBank p4250 ray4250
theorem signs4250 : ∀ j, Signs p4250 (bank4250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4251 := params 26
abbrev ray4251 := rays 26
def bank4251 : Fin 2 → Cell := twoBank p4251 ray4251
theorem signs4251 : ∀ j, Signs p4251 (bank4251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4252 := params 27
abbrev ray4252 := rays 27
def bank4252 : Fin 2 → Cell := twoBank p4252 ray4252
theorem signs4252 : ∀ j, Signs p4252 (bank4252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4253 := params 28
abbrev ray4253 := rays 28
def bank4253 : Fin 2 → Cell := twoBank p4253 ray4253
theorem signs4253 : ∀ j, Signs p4253 (bank4253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4254 := params 29
abbrev ray4254 := rays 29
def bank4254 : Fin 2 → Cell := twoBank p4254 ray4254
theorem signs4254 : ∀ j, Signs p4254 (bank4254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4255 := params 30
abbrev ray4255 := rays 30
def bank4255 : Fin 2 → Cell := twoBank p4255 ray4255
theorem signs4255 : ∀ j, Signs p4255 (bank4255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4256 := params 31
abbrev ray4256 := rays 31
def bank4256 : Fin 2 → Cell := twoBank p4256 ray4256
theorem signs4256 : ∀ j, Signs p4256 (bank4256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04225_04256
