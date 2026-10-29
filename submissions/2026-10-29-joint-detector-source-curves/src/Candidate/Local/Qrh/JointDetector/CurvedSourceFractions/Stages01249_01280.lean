/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01249_01280
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99819111783375,99818950712454,99818789616741,99818628496239,99818467350949,99818306180874,99818144986017,99817983766380,99817822521964,99817661252772,99817499958807,99817338640070,99817177296564,99817015928292,99816854535255,99816693117456,99816531674897,99816370207580,99816208715507,99816047198681,99815885657104,99815724090779,99815562499707,99815400883891,99815239243333,99815077578035,99814915888000,99814754173230,99814592433727,99814430669493,99814268880531,99814107066843,99813945228430]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1248+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(13164443558011518651080/17531224086491775895977:Fraction),(65816426189506547972864/87654370432460629479885:Fraction),(7312292847652899889021/9739180048051375497765:Fraction),(65804846108220386680132/87650870432464129479885:Fraction),(7311006267538296891067/9738791159162875497765:Fraction),(21931088842586913599048/29215790144155876493295:Fraction),(65787477687755216942012/87645620432469379479885:Fraction),(54141308549696373814/72134872783926855539:Fraction),(2436144515125450447316/3246004460461958499255:Fraction),(65770113749285198879558/87640370432474629479885:Fraction),(65764326630418275427877/87638620432476379479885:Fraction),(69585755906870723648/92737429029077385693:Fraction),(21917584357960055159588/29211706810826626493295:Fraction),(13149393571226875216456/17526674086496325895977:Fraction),(4382745497261304231778/5842108028832225298659:Fraction),(7303932986916388274912/9736652270276125497765:Fraction),(65729612346044763017341/87628120432486879479885:Fraction),(4381588590024288648958/5841758028832575298659:Fraction),(13143609035062994681671/17524924086498075895977:Fraction),(65712261320908453338001/87622870432492129479885:Fraction),(2433573278041770001096/3245226682684958499255:Fraction),(1877162728972587458075/2503410583785589413711:Fraction),(164648906169566080289/219593033665406966115:Fraction),(7298792516670086287558/9735096714722125497765:Fraction),(810905574804770497223/1081655807808652833085:Fraction),(4378504685942292299020/5840824695500175298659:Fraction),(132670282949380756600/176991152388897736323:Fraction),(4377734058111107172632/5840591362167075298659:Fraction),(65660231504271470997934/87607120432507879479885:Fraction),(1042134158059820239283/1390561435436660785395:Fraction),(13129734690456680091077/17520724086502275895977:Fraction),(65642894767741017868931/87601870432513129479885:Fraction)]
abbrev p1249 := params 0
abbrev ray1249 := rays 0
def bank1249 : Fin 1 → Cell := oneBank p1249 ray1249
theorem signs1249 : ∀ j, Signs p1249 (bank1249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1250 := params 1
abbrev ray1250 := rays 1
def bank1250 : Fin 1 → Cell := oneBank p1250 ray1250
theorem signs1250 : ∀ j, Signs p1250 (bank1250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1251 := params 2
abbrev ray1251 := rays 2
def bank1251 : Fin 1 → Cell := oneBank p1251 ray1251
theorem signs1251 : ∀ j, Signs p1251 (bank1251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1252 := params 3
abbrev ray1252 := rays 3
def bank1252 : Fin 1 → Cell := oneBank p1252 ray1252
theorem signs1252 : ∀ j, Signs p1252 (bank1252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1253 := params 4
abbrev ray1253 := rays 4
def bank1253 : Fin 1 → Cell := oneBank p1253 ray1253
theorem signs1253 : ∀ j, Signs p1253 (bank1253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1254 := params 5
abbrev ray1254 := rays 5
def bank1254 : Fin 1 → Cell := oneBank p1254 ray1254
theorem signs1254 : ∀ j, Signs p1254 (bank1254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1255 := params 6
abbrev ray1255 := rays 6
def bank1255 : Fin 1 → Cell := oneBank p1255 ray1255
theorem signs1255 : ∀ j, Signs p1255 (bank1255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1256 := params 7
abbrev ray1256 := rays 7
def bank1256 : Fin 1 → Cell := oneBank p1256 ray1256
theorem signs1256 : ∀ j, Signs p1256 (bank1256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1257 := params 8
abbrev ray1257 := rays 8
def bank1257 : Fin 1 → Cell := oneBank p1257 ray1257
theorem signs1257 : ∀ j, Signs p1257 (bank1257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1258 := params 9
abbrev ray1258 := rays 9
def bank1258 : Fin 1 → Cell := oneBank p1258 ray1258
theorem signs1258 : ∀ j, Signs p1258 (bank1258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1259 := params 10
abbrev ray1259 := rays 10
def bank1259 : Fin 1 → Cell := oneBank p1259 ray1259
theorem signs1259 : ∀ j, Signs p1259 (bank1259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1260 := params 11
abbrev ray1260 := rays 11
def bank1260 : Fin 1 → Cell := oneBank p1260 ray1260
theorem signs1260 : ∀ j, Signs p1260 (bank1260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1261 := params 12
abbrev ray1261 := rays 12
def bank1261 : Fin 1 → Cell := oneBank p1261 ray1261
theorem signs1261 : ∀ j, Signs p1261 (bank1261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1262 := params 13
abbrev ray1262 := rays 13
def bank1262 : Fin 1 → Cell := oneBank p1262 ray1262
theorem signs1262 : ∀ j, Signs p1262 (bank1262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1263 := params 14
abbrev ray1263 := rays 14
def bank1263 : Fin 1 → Cell := oneBank p1263 ray1263
theorem signs1263 : ∀ j, Signs p1263 (bank1263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1264 := params 15
abbrev ray1264 := rays 15
def bank1264 : Fin 1 → Cell := oneBank p1264 ray1264
theorem signs1264 : ∀ j, Signs p1264 (bank1264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1265 := params 16
abbrev ray1265 := rays 16
def bank1265 : Fin 1 → Cell := oneBank p1265 ray1265
theorem signs1265 : ∀ j, Signs p1265 (bank1265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1266 := params 17
abbrev ray1266 := rays 17
def bank1266 : Fin 1 → Cell := oneBank p1266 ray1266
theorem signs1266 : ∀ j, Signs p1266 (bank1266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1267 := params 18
abbrev ray1267 := rays 18
def bank1267 : Fin 1 → Cell := oneBank p1267 ray1267
theorem signs1267 : ∀ j, Signs p1267 (bank1267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1268 := params 19
abbrev ray1268 := rays 19
def bank1268 : Fin 1 → Cell := oneBank p1268 ray1268
theorem signs1268 : ∀ j, Signs p1268 (bank1268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1269 := params 20
abbrev ray1269 := rays 20
def bank1269 : Fin 1 → Cell := oneBank p1269 ray1269
theorem signs1269 : ∀ j, Signs p1269 (bank1269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1270 := params 21
abbrev ray1270 := rays 21
def bank1270 : Fin 1 → Cell := oneBank p1270 ray1270
theorem signs1270 : ∀ j, Signs p1270 (bank1270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1271 := params 22
abbrev ray1271 := rays 22
def bank1271 : Fin 1 → Cell := oneBank p1271 ray1271
theorem signs1271 : ∀ j, Signs p1271 (bank1271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1272 := params 23
abbrev ray1272 := rays 23
def bank1272 : Fin 1 → Cell := oneBank p1272 ray1272
theorem signs1272 : ∀ j, Signs p1272 (bank1272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1273 := params 24
abbrev ray1273 := rays 24
def bank1273 : Fin 1 → Cell := oneBank p1273 ray1273
theorem signs1273 : ∀ j, Signs p1273 (bank1273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1274 := params 25
abbrev ray1274 := rays 25
def bank1274 : Fin 1 → Cell := oneBank p1274 ray1274
theorem signs1274 : ∀ j, Signs p1274 (bank1274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1275 := params 26
abbrev ray1275 := rays 26
def bank1275 : Fin 1 → Cell := oneBank p1275 ray1275
theorem signs1275 : ∀ j, Signs p1275 (bank1275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1276 := params 27
abbrev ray1276 := rays 27
def bank1276 : Fin 1 → Cell := oneBank p1276 ray1276
theorem signs1276 : ∀ j, Signs p1276 (bank1276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1277 := params 28
abbrev ray1277 := rays 28
def bank1277 : Fin 1 → Cell := oneBank p1277 ray1277
theorem signs1277 : ∀ j, Signs p1277 (bank1277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1278 := params 29
abbrev ray1278 := rays 29
def bank1278 : Fin 1 → Cell := oneBank p1278 ray1278
theorem signs1278 : ∀ j, Signs p1278 (bank1278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1279 := params 30
abbrev ray1279 := rays 30
def bank1279 : Fin 1 → Cell := oneBank p1279 ray1279
theorem signs1279 : ∀ j, Signs p1279 (bank1279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1280 := params 31
abbrev ray1280 := rays 31
def bank1280 : Fin 1 → Cell := oneBank p1280 ray1280
theorem signs1280 : ∀ j, Signs p1280 (bank1280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01249_01280
