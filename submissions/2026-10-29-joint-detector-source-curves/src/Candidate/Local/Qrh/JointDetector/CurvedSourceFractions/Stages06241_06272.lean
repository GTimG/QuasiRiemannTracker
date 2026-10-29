/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06241_06272
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98699002431695,98698716823073,98698431191498,98698145536970,98697859859490,98697574159059,98697288435678,98697002689348,98696716920070,98696431127844,98696145312672,98695859474554,98695573613491,98695287729484,98695001822534,98694715892641,98694429939807,98694143964032,98693857965318,98693571943665,98693285899074,98692999831546,98692713741081,98692427627681,98692141491346,98691855332077,98691569149876,98691282944743,98690996716678,98690710465683,98690424191759,98690137894906,98689851575125]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6240+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6241 := params 0
abbrev ray6241 := rays 0
def bank6241 : Fin 2 → Cell := twoBank p6241 ray6241
theorem signs6241 : ∀ j, Signs p6241 (bank6241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6242 := params 1
abbrev ray6242 := rays 1
def bank6242 : Fin 2 → Cell := twoBank p6242 ray6242
theorem signs6242 : ∀ j, Signs p6242 (bank6242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6243 := params 2
abbrev ray6243 := rays 2
def bank6243 : Fin 2 → Cell := twoBank p6243 ray6243
theorem signs6243 : ∀ j, Signs p6243 (bank6243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6244 := params 3
abbrev ray6244 := rays 3
def bank6244 : Fin 2 → Cell := twoBank p6244 ray6244
theorem signs6244 : ∀ j, Signs p6244 (bank6244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6245 := params 4
abbrev ray6245 := rays 4
def bank6245 : Fin 2 → Cell := twoBank p6245 ray6245
theorem signs6245 : ∀ j, Signs p6245 (bank6245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6246 := params 5
abbrev ray6246 := rays 5
def bank6246 : Fin 2 → Cell := twoBank p6246 ray6246
theorem signs6246 : ∀ j, Signs p6246 (bank6246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6247 := params 6
abbrev ray6247 := rays 6
def bank6247 : Fin 2 → Cell := twoBank p6247 ray6247
theorem signs6247 : ∀ j, Signs p6247 (bank6247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6248 := params 7
abbrev ray6248 := rays 7
def bank6248 : Fin 2 → Cell := twoBank p6248 ray6248
theorem signs6248 : ∀ j, Signs p6248 (bank6248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6249 := params 8
abbrev ray6249 := rays 8
def bank6249 : Fin 2 → Cell := twoBank p6249 ray6249
theorem signs6249 : ∀ j, Signs p6249 (bank6249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6250 := params 9
abbrev ray6250 := rays 9
def bank6250 : Fin 2 → Cell := twoBank p6250 ray6250
theorem signs6250 : ∀ j, Signs p6250 (bank6250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6251 := params 10
abbrev ray6251 := rays 10
def bank6251 : Fin 2 → Cell := twoBank p6251 ray6251
theorem signs6251 : ∀ j, Signs p6251 (bank6251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6252 := params 11
abbrev ray6252 := rays 11
def bank6252 : Fin 2 → Cell := twoBank p6252 ray6252
theorem signs6252 : ∀ j, Signs p6252 (bank6252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6253 := params 12
abbrev ray6253 := rays 12
def bank6253 : Fin 2 → Cell := twoBank p6253 ray6253
theorem signs6253 : ∀ j, Signs p6253 (bank6253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6254 := params 13
abbrev ray6254 := rays 13
def bank6254 : Fin 2 → Cell := twoBank p6254 ray6254
theorem signs6254 : ∀ j, Signs p6254 (bank6254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6255 := params 14
abbrev ray6255 := rays 14
def bank6255 : Fin 2 → Cell := twoBank p6255 ray6255
theorem signs6255 : ∀ j, Signs p6255 (bank6255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6256 := params 15
abbrev ray6256 := rays 15
def bank6256 : Fin 2 → Cell := twoBank p6256 ray6256
theorem signs6256 : ∀ j, Signs p6256 (bank6256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6257 := params 16
abbrev ray6257 := rays 16
def bank6257 : Fin 2 → Cell := twoBank p6257 ray6257
theorem signs6257 : ∀ j, Signs p6257 (bank6257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6258 := params 17
abbrev ray6258 := rays 17
def bank6258 : Fin 2 → Cell := twoBank p6258 ray6258
theorem signs6258 : ∀ j, Signs p6258 (bank6258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6259 := params 18
abbrev ray6259 := rays 18
def bank6259 : Fin 2 → Cell := twoBank p6259 ray6259
theorem signs6259 : ∀ j, Signs p6259 (bank6259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6260 := params 19
abbrev ray6260 := rays 19
def bank6260 : Fin 2 → Cell := twoBank p6260 ray6260
theorem signs6260 : ∀ j, Signs p6260 (bank6260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6261 := params 20
abbrev ray6261 := rays 20
def bank6261 : Fin 2 → Cell := twoBank p6261 ray6261
theorem signs6261 : ∀ j, Signs p6261 (bank6261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6262 := params 21
abbrev ray6262 := rays 21
def bank6262 : Fin 2 → Cell := twoBank p6262 ray6262
theorem signs6262 : ∀ j, Signs p6262 (bank6262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6263 := params 22
abbrev ray6263 := rays 22
def bank6263 : Fin 2 → Cell := twoBank p6263 ray6263
theorem signs6263 : ∀ j, Signs p6263 (bank6263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6264 := params 23
abbrev ray6264 := rays 23
def bank6264 : Fin 2 → Cell := twoBank p6264 ray6264
theorem signs6264 : ∀ j, Signs p6264 (bank6264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6265 := params 24
abbrev ray6265 := rays 24
def bank6265 : Fin 2 → Cell := twoBank p6265 ray6265
theorem signs6265 : ∀ j, Signs p6265 (bank6265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6266 := params 25
abbrev ray6266 := rays 25
def bank6266 : Fin 2 → Cell := twoBank p6266 ray6266
theorem signs6266 : ∀ j, Signs p6266 (bank6266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6267 := params 26
abbrev ray6267 := rays 26
def bank6267 : Fin 2 → Cell := twoBank p6267 ray6267
theorem signs6267 : ∀ j, Signs p6267 (bank6267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6268 := params 27
abbrev ray6268 := rays 27
def bank6268 : Fin 2 → Cell := twoBank p6268 ray6268
theorem signs6268 : ∀ j, Signs p6268 (bank6268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6269 := params 28
abbrev ray6269 := rays 28
def bank6269 : Fin 2 → Cell := twoBank p6269 ray6269
theorem signs6269 : ∀ j, Signs p6269 (bank6269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6270 := params 29
abbrev ray6270 := rays 29
def bank6270 : Fin 2 → Cell := twoBank p6270 ray6270
theorem signs6270 : ∀ j, Signs p6270 (bank6270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6271 := params 30
abbrev ray6271 := rays 30
def bank6271 : Fin 2 → Cell := twoBank p6271 ray6271
theorem signs6271 : ∀ j, Signs p6271 (bank6271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6272 := params 31
abbrev ray6272 := rays 31
def bank6272 : Fin 2 → Cell := twoBank p6272 ray6272
theorem signs6272 : ∀ j, Signs p6272 (bank6272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06241_06272
