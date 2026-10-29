/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04289_04320
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99211625647500,99211386617716,99211147563088,99210908483618,99210669379307,99210430250157,99210191096168,99209951917341,99209712713677,99209473485178,99209234231844,99208994953677,99208755650678,99208516322848,99208276970187,99208037592697,99207798190379,99207558763235,99207319311265,99207079834470,99206840332852,99206600806411,99206361255149,99206121679066,99205882078164,99205642452444,99205402801907,99205163126554,99204923426386,99204683701404,99204443951609,99204204177002,99203964377585]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4288+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4289 := params 0
abbrev ray4289 := rays 0
def bank4289 : Fin 2 → Cell := twoBank p4289 ray4289
theorem signs4289 : ∀ j, Signs p4289 (bank4289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4290 := params 1
abbrev ray4290 := rays 1
def bank4290 : Fin 2 → Cell := twoBank p4290 ray4290
theorem signs4290 : ∀ j, Signs p4290 (bank4290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4291 := params 2
abbrev ray4291 := rays 2
def bank4291 : Fin 2 → Cell := twoBank p4291 ray4291
theorem signs4291 : ∀ j, Signs p4291 (bank4291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4292 := params 3
abbrev ray4292 := rays 3
def bank4292 : Fin 2 → Cell := twoBank p4292 ray4292
theorem signs4292 : ∀ j, Signs p4292 (bank4292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4293 := params 4
abbrev ray4293 := rays 4
def bank4293 : Fin 2 → Cell := twoBank p4293 ray4293
theorem signs4293 : ∀ j, Signs p4293 (bank4293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4294 := params 5
abbrev ray4294 := rays 5
def bank4294 : Fin 2 → Cell := twoBank p4294 ray4294
theorem signs4294 : ∀ j, Signs p4294 (bank4294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4295 := params 6
abbrev ray4295 := rays 6
def bank4295 : Fin 2 → Cell := twoBank p4295 ray4295
theorem signs4295 : ∀ j, Signs p4295 (bank4295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4296 := params 7
abbrev ray4296 := rays 7
def bank4296 : Fin 2 → Cell := twoBank p4296 ray4296
theorem signs4296 : ∀ j, Signs p4296 (bank4296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4297 := params 8
abbrev ray4297 := rays 8
def bank4297 : Fin 2 → Cell := twoBank p4297 ray4297
theorem signs4297 : ∀ j, Signs p4297 (bank4297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4298 := params 9
abbrev ray4298 := rays 9
def bank4298 : Fin 2 → Cell := twoBank p4298 ray4298
theorem signs4298 : ∀ j, Signs p4298 (bank4298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4299 := params 10
abbrev ray4299 := rays 10
def bank4299 : Fin 2 → Cell := twoBank p4299 ray4299
theorem signs4299 : ∀ j, Signs p4299 (bank4299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4300 := params 11
abbrev ray4300 := rays 11
def bank4300 : Fin 2 → Cell := twoBank p4300 ray4300
theorem signs4300 : ∀ j, Signs p4300 (bank4300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4301 := params 12
abbrev ray4301 := rays 12
def bank4301 : Fin 2 → Cell := twoBank p4301 ray4301
theorem signs4301 : ∀ j, Signs p4301 (bank4301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4302 := params 13
abbrev ray4302 := rays 13
def bank4302 : Fin 2 → Cell := twoBank p4302 ray4302
theorem signs4302 : ∀ j, Signs p4302 (bank4302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4303 := params 14
abbrev ray4303 := rays 14
def bank4303 : Fin 2 → Cell := twoBank p4303 ray4303
theorem signs4303 : ∀ j, Signs p4303 (bank4303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4304 := params 15
abbrev ray4304 := rays 15
def bank4304 : Fin 2 → Cell := twoBank p4304 ray4304
theorem signs4304 : ∀ j, Signs p4304 (bank4304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4305 := params 16
abbrev ray4305 := rays 16
def bank4305 : Fin 2 → Cell := twoBank p4305 ray4305
theorem signs4305 : ∀ j, Signs p4305 (bank4305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4306 := params 17
abbrev ray4306 := rays 17
def bank4306 : Fin 2 → Cell := twoBank p4306 ray4306
theorem signs4306 : ∀ j, Signs p4306 (bank4306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4307 := params 18
abbrev ray4307 := rays 18
def bank4307 : Fin 2 → Cell := twoBank p4307 ray4307
theorem signs4307 : ∀ j, Signs p4307 (bank4307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4308 := params 19
abbrev ray4308 := rays 19
def bank4308 : Fin 2 → Cell := twoBank p4308 ray4308
theorem signs4308 : ∀ j, Signs p4308 (bank4308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4309 := params 20
abbrev ray4309 := rays 20
def bank4309 : Fin 2 → Cell := twoBank p4309 ray4309
theorem signs4309 : ∀ j, Signs p4309 (bank4309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4310 := params 21
abbrev ray4310 := rays 21
def bank4310 : Fin 2 → Cell := twoBank p4310 ray4310
theorem signs4310 : ∀ j, Signs p4310 (bank4310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4311 := params 22
abbrev ray4311 := rays 22
def bank4311 : Fin 2 → Cell := twoBank p4311 ray4311
theorem signs4311 : ∀ j, Signs p4311 (bank4311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4312 := params 23
abbrev ray4312 := rays 23
def bank4312 : Fin 2 → Cell := twoBank p4312 ray4312
theorem signs4312 : ∀ j, Signs p4312 (bank4312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4313 := params 24
abbrev ray4313 := rays 24
def bank4313 : Fin 2 → Cell := twoBank p4313 ray4313
theorem signs4313 : ∀ j, Signs p4313 (bank4313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4314 := params 25
abbrev ray4314 := rays 25
def bank4314 : Fin 2 → Cell := twoBank p4314 ray4314
theorem signs4314 : ∀ j, Signs p4314 (bank4314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4315 := params 26
abbrev ray4315 := rays 26
def bank4315 : Fin 2 → Cell := twoBank p4315 ray4315
theorem signs4315 : ∀ j, Signs p4315 (bank4315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4316 := params 27
abbrev ray4316 := rays 27
def bank4316 : Fin 2 → Cell := twoBank p4316 ray4316
theorem signs4316 : ∀ j, Signs p4316 (bank4316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4317 := params 28
abbrev ray4317 := rays 28
def bank4317 : Fin 2 → Cell := twoBank p4317 ray4317
theorem signs4317 : ∀ j, Signs p4317 (bank4317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4318 := params 29
abbrev ray4318 := rays 29
def bank4318 : Fin 2 → Cell := twoBank p4318 ray4318
theorem signs4318 : ∀ j, Signs p4318 (bank4318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4319 := params 30
abbrev ray4319 := rays 30
def bank4319 : Fin 2 → Cell := twoBank p4319 ray4319
theorem signs4319 : ∀ j, Signs p4319 (bank4319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4320 := params 31
abbrev ray4320 := rays 31
def bank4320 : Fin 2 → Cell := twoBank p4320 ray4320
theorem signs4320 : ∀ j, Signs p4320 (bank4320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04289_04320
