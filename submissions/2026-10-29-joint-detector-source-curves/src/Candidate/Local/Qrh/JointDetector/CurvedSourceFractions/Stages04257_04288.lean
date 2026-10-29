/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04257_04288
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99219261476916,99219023242686,99218784983578,99218546699593,99218308390733,99218070056998,99217831698389,99217593314908,99217354906555,99217116473332,99216878015240,99216639532280,99216401024453,99216162491760,99215923934202,99215685351780,99215446744495,99215208112349,99214969455342,99214730773476,99214492066751,99214253335169,99214014578731,99213775797438,99213536991291,99213298160291,99213059304439,99212820423736,99212581518184,99212342587783,99212103632535,99211864652440,99211625647500]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4256+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4257 := params 0
abbrev ray4257 := rays 0
def bank4257 : Fin 2 → Cell := twoBank p4257 ray4257
theorem signs4257 : ∀ j, Signs p4257 (bank4257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4258 := params 1
abbrev ray4258 := rays 1
def bank4258 : Fin 2 → Cell := twoBank p4258 ray4258
theorem signs4258 : ∀ j, Signs p4258 (bank4258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4259 := params 2
abbrev ray4259 := rays 2
def bank4259 : Fin 2 → Cell := twoBank p4259 ray4259
theorem signs4259 : ∀ j, Signs p4259 (bank4259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4260 := params 3
abbrev ray4260 := rays 3
def bank4260 : Fin 2 → Cell := twoBank p4260 ray4260
theorem signs4260 : ∀ j, Signs p4260 (bank4260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4261 := params 4
abbrev ray4261 := rays 4
def bank4261 : Fin 2 → Cell := twoBank p4261 ray4261
theorem signs4261 : ∀ j, Signs p4261 (bank4261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4262 := params 5
abbrev ray4262 := rays 5
def bank4262 : Fin 2 → Cell := twoBank p4262 ray4262
theorem signs4262 : ∀ j, Signs p4262 (bank4262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4263 := params 6
abbrev ray4263 := rays 6
def bank4263 : Fin 2 → Cell := twoBank p4263 ray4263
theorem signs4263 : ∀ j, Signs p4263 (bank4263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4264 := params 7
abbrev ray4264 := rays 7
def bank4264 : Fin 2 → Cell := twoBank p4264 ray4264
theorem signs4264 : ∀ j, Signs p4264 (bank4264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4265 := params 8
abbrev ray4265 := rays 8
def bank4265 : Fin 2 → Cell := twoBank p4265 ray4265
theorem signs4265 : ∀ j, Signs p4265 (bank4265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4266 := params 9
abbrev ray4266 := rays 9
def bank4266 : Fin 2 → Cell := twoBank p4266 ray4266
theorem signs4266 : ∀ j, Signs p4266 (bank4266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4267 := params 10
abbrev ray4267 := rays 10
def bank4267 : Fin 2 → Cell := twoBank p4267 ray4267
theorem signs4267 : ∀ j, Signs p4267 (bank4267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4268 := params 11
abbrev ray4268 := rays 11
def bank4268 : Fin 2 → Cell := twoBank p4268 ray4268
theorem signs4268 : ∀ j, Signs p4268 (bank4268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4269 := params 12
abbrev ray4269 := rays 12
def bank4269 : Fin 2 → Cell := twoBank p4269 ray4269
theorem signs4269 : ∀ j, Signs p4269 (bank4269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4270 := params 13
abbrev ray4270 := rays 13
def bank4270 : Fin 2 → Cell := twoBank p4270 ray4270
theorem signs4270 : ∀ j, Signs p4270 (bank4270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4271 := params 14
abbrev ray4271 := rays 14
def bank4271 : Fin 2 → Cell := twoBank p4271 ray4271
theorem signs4271 : ∀ j, Signs p4271 (bank4271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4272 := params 15
abbrev ray4272 := rays 15
def bank4272 : Fin 2 → Cell := twoBank p4272 ray4272
theorem signs4272 : ∀ j, Signs p4272 (bank4272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4273 := params 16
abbrev ray4273 := rays 16
def bank4273 : Fin 2 → Cell := twoBank p4273 ray4273
theorem signs4273 : ∀ j, Signs p4273 (bank4273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4274 := params 17
abbrev ray4274 := rays 17
def bank4274 : Fin 2 → Cell := twoBank p4274 ray4274
theorem signs4274 : ∀ j, Signs p4274 (bank4274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4275 := params 18
abbrev ray4275 := rays 18
def bank4275 : Fin 2 → Cell := twoBank p4275 ray4275
theorem signs4275 : ∀ j, Signs p4275 (bank4275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4276 := params 19
abbrev ray4276 := rays 19
def bank4276 : Fin 2 → Cell := twoBank p4276 ray4276
theorem signs4276 : ∀ j, Signs p4276 (bank4276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4277 := params 20
abbrev ray4277 := rays 20
def bank4277 : Fin 2 → Cell := twoBank p4277 ray4277
theorem signs4277 : ∀ j, Signs p4277 (bank4277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4278 := params 21
abbrev ray4278 := rays 21
def bank4278 : Fin 2 → Cell := twoBank p4278 ray4278
theorem signs4278 : ∀ j, Signs p4278 (bank4278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4279 := params 22
abbrev ray4279 := rays 22
def bank4279 : Fin 2 → Cell := twoBank p4279 ray4279
theorem signs4279 : ∀ j, Signs p4279 (bank4279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4280 := params 23
abbrev ray4280 := rays 23
def bank4280 : Fin 2 → Cell := twoBank p4280 ray4280
theorem signs4280 : ∀ j, Signs p4280 (bank4280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4281 := params 24
abbrev ray4281 := rays 24
def bank4281 : Fin 2 → Cell := twoBank p4281 ray4281
theorem signs4281 : ∀ j, Signs p4281 (bank4281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4282 := params 25
abbrev ray4282 := rays 25
def bank4282 : Fin 2 → Cell := twoBank p4282 ray4282
theorem signs4282 : ∀ j, Signs p4282 (bank4282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4283 := params 26
abbrev ray4283 := rays 26
def bank4283 : Fin 2 → Cell := twoBank p4283 ray4283
theorem signs4283 : ∀ j, Signs p4283 (bank4283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4284 := params 27
abbrev ray4284 := rays 27
def bank4284 : Fin 2 → Cell := twoBank p4284 ray4284
theorem signs4284 : ∀ j, Signs p4284 (bank4284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4285 := params 28
abbrev ray4285 := rays 28
def bank4285 : Fin 2 → Cell := twoBank p4285 ray4285
theorem signs4285 : ∀ j, Signs p4285 (bank4285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4286 := params 29
abbrev ray4286 := rays 29
def bank4286 : Fin 2 → Cell := twoBank p4286 ray4286
theorem signs4286 : ∀ j, Signs p4286 (bank4286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4287 := params 30
abbrev ray4287 := rays 30
def bank4287 : Fin 2 → Cell := twoBank p4287 ray4287
theorem signs4287 : ∀ j, Signs p4287 (bank4287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4288 := params 31
abbrev ray4288 := rays 31
def bank4288 : Fin 2 → Cell := twoBank p4288 ray4288
theorem signs4288 : ∀ j, Signs p4288 (bank4288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04257_04288
