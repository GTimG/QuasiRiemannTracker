/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13217_13248
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96188528853954,96188100408656,96187671946976,96187243468914,96186814974470,96186386463645,96185957936439,96185529392852,96185100832884,96184672256536,96184243663808,96183815054700,96183386429212,96182957787345,96182529129099,96182100454474,96181671763470,96181243056087,96180814332326,96180385592187,96179956835671,96179528062777,96179099273506,96178670467858,96178241645833,96177812807431,96177383952653,96176955081499,96176526193969,96176097290064,96175668369784,96175239433128,96174810480098]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13216+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13217 := params 0
abbrev ray13217 := rays 0
def bank13217 : Fin 1 → Cell := oneBank p13217 ray13217
theorem signs13217 : ∀ j, Signs p13217 (bank13217 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13218 := params 1
abbrev ray13218 := rays 1
def bank13218 : Fin 1 → Cell := oneBank p13218 ray13218
theorem signs13218 : ∀ j, Signs p13218 (bank13218 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13219 := params 2
abbrev ray13219 := rays 2
def bank13219 : Fin 1 → Cell := oneBank p13219 ray13219
theorem signs13219 : ∀ j, Signs p13219 (bank13219 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13220 := params 3
abbrev ray13220 := rays 3
def bank13220 : Fin 1 → Cell := oneBank p13220 ray13220
theorem signs13220 : ∀ j, Signs p13220 (bank13220 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13221 := params 4
abbrev ray13221 := rays 4
def bank13221 : Fin 1 → Cell := oneBank p13221 ray13221
theorem signs13221 : ∀ j, Signs p13221 (bank13221 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13222 := params 5
abbrev ray13222 := rays 5
def bank13222 : Fin 1 → Cell := oneBank p13222 ray13222
theorem signs13222 : ∀ j, Signs p13222 (bank13222 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13223 := params 6
abbrev ray13223 := rays 6
def bank13223 : Fin 1 → Cell := oneBank p13223 ray13223
theorem signs13223 : ∀ j, Signs p13223 (bank13223 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13224 := params 7
abbrev ray13224 := rays 7
def bank13224 : Fin 1 → Cell := oneBank p13224 ray13224
theorem signs13224 : ∀ j, Signs p13224 (bank13224 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13225 := params 8
abbrev ray13225 := rays 8
def bank13225 : Fin 1 → Cell := oneBank p13225 ray13225
theorem signs13225 : ∀ j, Signs p13225 (bank13225 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13226 := params 9
abbrev ray13226 := rays 9
def bank13226 : Fin 1 → Cell := oneBank p13226 ray13226
theorem signs13226 : ∀ j, Signs p13226 (bank13226 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13227 := params 10
abbrev ray13227 := rays 10
def bank13227 : Fin 1 → Cell := oneBank p13227 ray13227
theorem signs13227 : ∀ j, Signs p13227 (bank13227 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13228 := params 11
abbrev ray13228 := rays 11
def bank13228 : Fin 1 → Cell := oneBank p13228 ray13228
theorem signs13228 : ∀ j, Signs p13228 (bank13228 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13229 := params 12
abbrev ray13229 := rays 12
def bank13229 : Fin 1 → Cell := oneBank p13229 ray13229
theorem signs13229 : ∀ j, Signs p13229 (bank13229 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13230 := params 13
abbrev ray13230 := rays 13
def bank13230 : Fin 1 → Cell := oneBank p13230 ray13230
theorem signs13230 : ∀ j, Signs p13230 (bank13230 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13231 := params 14
abbrev ray13231 := rays 14
def bank13231 : Fin 1 → Cell := oneBank p13231 ray13231
theorem signs13231 : ∀ j, Signs p13231 (bank13231 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13232 := params 15
abbrev ray13232 := rays 15
def bank13232 : Fin 1 → Cell := oneBank p13232 ray13232
theorem signs13232 : ∀ j, Signs p13232 (bank13232 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13233 := params 16
abbrev ray13233 := rays 16
def bank13233 : Fin 1 → Cell := oneBank p13233 ray13233
theorem signs13233 : ∀ j, Signs p13233 (bank13233 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13234 := params 17
abbrev ray13234 := rays 17
def bank13234 : Fin 1 → Cell := oneBank p13234 ray13234
theorem signs13234 : ∀ j, Signs p13234 (bank13234 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13235 := params 18
abbrev ray13235 := rays 18
def bank13235 : Fin 1 → Cell := oneBank p13235 ray13235
theorem signs13235 : ∀ j, Signs p13235 (bank13235 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13236 := params 19
abbrev ray13236 := rays 19
def bank13236 : Fin 1 → Cell := oneBank p13236 ray13236
theorem signs13236 : ∀ j, Signs p13236 (bank13236 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13237 := params 20
abbrev ray13237 := rays 20
def bank13237 : Fin 1 → Cell := oneBank p13237 ray13237
theorem signs13237 : ∀ j, Signs p13237 (bank13237 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13238 := params 21
abbrev ray13238 := rays 21
def bank13238 : Fin 1 → Cell := oneBank p13238 ray13238
theorem signs13238 : ∀ j, Signs p13238 (bank13238 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13239 := params 22
abbrev ray13239 := rays 22
def bank13239 : Fin 1 → Cell := oneBank p13239 ray13239
theorem signs13239 : ∀ j, Signs p13239 (bank13239 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13240 := params 23
abbrev ray13240 := rays 23
def bank13240 : Fin 1 → Cell := oneBank p13240 ray13240
theorem signs13240 : ∀ j, Signs p13240 (bank13240 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13241 := params 24
abbrev ray13241 := rays 24
def bank13241 : Fin 1 → Cell := oneBank p13241 ray13241
theorem signs13241 : ∀ j, Signs p13241 (bank13241 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13242 := params 25
abbrev ray13242 := rays 25
def bank13242 : Fin 1 → Cell := oneBank p13242 ray13242
theorem signs13242 : ∀ j, Signs p13242 (bank13242 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13243 := params 26
abbrev ray13243 := rays 26
def bank13243 : Fin 1 → Cell := oneBank p13243 ray13243
theorem signs13243 : ∀ j, Signs p13243 (bank13243 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13244 := params 27
abbrev ray13244 := rays 27
def bank13244 : Fin 1 → Cell := oneBank p13244 ray13244
theorem signs13244 : ∀ j, Signs p13244 (bank13244 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13245 := params 28
abbrev ray13245 := rays 28
def bank13245 : Fin 1 → Cell := oneBank p13245 ray13245
theorem signs13245 : ∀ j, Signs p13245 (bank13245 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13246 := params 29
abbrev ray13246 := rays 29
def bank13246 : Fin 1 → Cell := oneBank p13246 ray13246
theorem signs13246 : ∀ j, Signs p13246 (bank13246 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13247 := params 30
abbrev ray13247 := rays 30
def bank13247 : Fin 1 → Cell := oneBank p13247 ray13247
theorem signs13247 : ∀ j, Signs p13247 (bank13247 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13248 := params 31
abbrev ray13248 := rays 31
def bank13248 : Fin 1 → Cell := oneBank p13248 ray13248
theorem signs13248 : ∀ j, Signs p13248 (bank13248 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13217_13248
