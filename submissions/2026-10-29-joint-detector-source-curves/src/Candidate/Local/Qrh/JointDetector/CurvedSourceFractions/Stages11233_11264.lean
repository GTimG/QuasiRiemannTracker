/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11233_11264
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97002798320346,97002407028991,97002015717932,97001624387170,97001233036706,97000841666540,97000450276672,97000058867103,96999667437834,96999275988865,96998884520196,96998493031828,96998101523761,96997709995996,96997318448534,96996926881374,96996535294518,96996143687965,96995752061717,96995360415773,96994968750134,96994577064801,96994185359774,96993793635054,96993401890641,96993010126535,96992618342737,96992226539248,96991834716068,96991442873197,96991051010636,96990659128386,96990267226446]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11232+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11233 := params 0
abbrev ray11233 := rays 0
def bank11233 : Fin 2 → Cell := twoBank p11233 ray11233
theorem signs11233 : ∀ j, Signs p11233 (bank11233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11234 := params 1
abbrev ray11234 := rays 1
def bank11234 : Fin 2 → Cell := twoBank p11234 ray11234
theorem signs11234 : ∀ j, Signs p11234 (bank11234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11235 := params 2
abbrev ray11235 := rays 2
def bank11235 : Fin 2 → Cell := twoBank p11235 ray11235
theorem signs11235 : ∀ j, Signs p11235 (bank11235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11236 := params 3
abbrev ray11236 := rays 3
def bank11236 : Fin 2 → Cell := twoBank p11236 ray11236
theorem signs11236 : ∀ j, Signs p11236 (bank11236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11237 := params 4
abbrev ray11237 := rays 4
def bank11237 : Fin 2 → Cell := twoBank p11237 ray11237
theorem signs11237 : ∀ j, Signs p11237 (bank11237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11238 := params 5
abbrev ray11238 := rays 5
def bank11238 : Fin 2 → Cell := twoBank p11238 ray11238
theorem signs11238 : ∀ j, Signs p11238 (bank11238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11239 := params 6
abbrev ray11239 := rays 6
def bank11239 : Fin 2 → Cell := twoBank p11239 ray11239
theorem signs11239 : ∀ j, Signs p11239 (bank11239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11240 := params 7
abbrev ray11240 := rays 7
def bank11240 : Fin 2 → Cell := twoBank p11240 ray11240
theorem signs11240 : ∀ j, Signs p11240 (bank11240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11241 := params 8
abbrev ray11241 := rays 8
def bank11241 : Fin 2 → Cell := twoBank p11241 ray11241
theorem signs11241 : ∀ j, Signs p11241 (bank11241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11242 := params 9
abbrev ray11242 := rays 9
def bank11242 : Fin 2 → Cell := twoBank p11242 ray11242
theorem signs11242 : ∀ j, Signs p11242 (bank11242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11243 := params 10
abbrev ray11243 := rays 10
def bank11243 : Fin 2 → Cell := twoBank p11243 ray11243
theorem signs11243 : ∀ j, Signs p11243 (bank11243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11244 := params 11
abbrev ray11244 := rays 11
def bank11244 : Fin 2 → Cell := twoBank p11244 ray11244
theorem signs11244 : ∀ j, Signs p11244 (bank11244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11245 := params 12
abbrev ray11245 := rays 12
def bank11245 : Fin 2 → Cell := twoBank p11245 ray11245
theorem signs11245 : ∀ j, Signs p11245 (bank11245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11246 := params 13
abbrev ray11246 := rays 13
def bank11246 : Fin 2 → Cell := twoBank p11246 ray11246
theorem signs11246 : ∀ j, Signs p11246 (bank11246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11247 := params 14
abbrev ray11247 := rays 14
def bank11247 : Fin 2 → Cell := twoBank p11247 ray11247
theorem signs11247 : ∀ j, Signs p11247 (bank11247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11248 := params 15
abbrev ray11248 := rays 15
def bank11248 : Fin 2 → Cell := twoBank p11248 ray11248
theorem signs11248 : ∀ j, Signs p11248 (bank11248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11249 := params 16
abbrev ray11249 := rays 16
def bank11249 : Fin 2 → Cell := twoBank p11249 ray11249
theorem signs11249 : ∀ j, Signs p11249 (bank11249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11250 := params 17
abbrev ray11250 := rays 17
def bank11250 : Fin 2 → Cell := twoBank p11250 ray11250
theorem signs11250 : ∀ j, Signs p11250 (bank11250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11251 := params 18
abbrev ray11251 := rays 18
def bank11251 : Fin 2 → Cell := twoBank p11251 ray11251
theorem signs11251 : ∀ j, Signs p11251 (bank11251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11252 := params 19
abbrev ray11252 := rays 19
def bank11252 : Fin 2 → Cell := twoBank p11252 ray11252
theorem signs11252 : ∀ j, Signs p11252 (bank11252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11253 := params 20
abbrev ray11253 := rays 20
def bank11253 : Fin 2 → Cell := twoBank p11253 ray11253
theorem signs11253 : ∀ j, Signs p11253 (bank11253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11254 := params 21
abbrev ray11254 := rays 21
def bank11254 : Fin 2 → Cell := twoBank p11254 ray11254
theorem signs11254 : ∀ j, Signs p11254 (bank11254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11255 := params 22
abbrev ray11255 := rays 22
def bank11255 : Fin 2 → Cell := twoBank p11255 ray11255
theorem signs11255 : ∀ j, Signs p11255 (bank11255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11256 := params 23
abbrev ray11256 := rays 23
def bank11256 : Fin 2 → Cell := twoBank p11256 ray11256
theorem signs11256 : ∀ j, Signs p11256 (bank11256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11257 := params 24
abbrev ray11257 := rays 24
def bank11257 : Fin 2 → Cell := twoBank p11257 ray11257
theorem signs11257 : ∀ j, Signs p11257 (bank11257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11258 := params 25
abbrev ray11258 := rays 25
def bank11258 : Fin 2 → Cell := twoBank p11258 ray11258
theorem signs11258 : ∀ j, Signs p11258 (bank11258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11259 := params 26
abbrev ray11259 := rays 26
def bank11259 : Fin 2 → Cell := twoBank p11259 ray11259
theorem signs11259 : ∀ j, Signs p11259 (bank11259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11260 := params 27
abbrev ray11260 := rays 27
def bank11260 : Fin 2 → Cell := twoBank p11260 ray11260
theorem signs11260 : ∀ j, Signs p11260 (bank11260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11261 := params 28
abbrev ray11261 := rays 28
def bank11261 : Fin 2 → Cell := twoBank p11261 ray11261
theorem signs11261 : ∀ j, Signs p11261 (bank11261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11262 := params 29
abbrev ray11262 := rays 29
def bank11262 : Fin 2 → Cell := twoBank p11262 ray11262
theorem signs11262 : ∀ j, Signs p11262 (bank11262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11263 := params 30
abbrev ray11263 := rays 30
def bank11263 : Fin 2 → Cell := twoBank p11263 ray11263
theorem signs11263 : ∀ j, Signs p11263 (bank11263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11264 := params 31
abbrev ray11264 := rays 31
def bank11264 : Fin 2 → Cell := twoBank p11264 ray11264
theorem signs11264 : ∀ j, Signs p11264 (bank11264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11233_11264
