/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01217_01248
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99824252949216,99824092672832,99823932371583,99823772045472,99823611694501,99823451318672,99823290917988,99823130492450,99822970042061,99822809566823,99822649066739,99822488541811,99822327992041,99822167417431,99822006817985,99821846193704,99821685544590,99821524870645,99821364171872,99821203448273,99821042699851,99820881926608,99820721128545,99820560305666,99820399457973,99820238585467,99820077688151,99819916766027,99819755819098,99819594847366,99819433850833,99819272829502,99819111783375]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1216+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(5077519815325874976938/6747086187107913806145:Fraction),(488903350025826554008/649706447647441699851:Fraction),(3142673711733389932616/4176600972971732356185:Fraction),(1199824448691535219766/1594670371498329626907:Fraction),(155991823236748936106/207340710242103733995:Fraction),(2443656948138629145946/3248272978978208499255:Fraction),(13194587001832749418118/17540324086482675895977:Fraction),(4397808897163936336400/5846658028827675298659:Fraction),(13192266345066389634397/17539624086483375895977:Fraction),(1884443708936947402190/2505610583783389413711:Fraction),(814194184434986919034/1082649634968152833085:Fraction),(65943929104707379656323/87692870432422129479885:Fraction),(13187625817971775488580/17538224086484775895977:Fraction),(813979369070359621257/1082584820153402833085:Fraction),(209290570598974725515/278373398198182157079:Fraction),(2441508533422017730126/3247624830830708499255:Fraction),(162752918778583535776/216504001067730566617:Fraction),(4393942323168377727056/5845491362162175298659:Fraction),(65903337409554236437144/87680620432434379479885:Fraction),(7321948865713636478584/9742096714715125497765:Fraction),(65891743212663651480013/87677120432437879479885:Fraction),(1882455647809430280530/2505010583783989413711:Fraction),(488001125584629112849/649434225425491699851:Fraction),(65874356054461209328084/87671870432443129479885:Fraction),(813192113512676011306/1082347165832652833085:Fraction),(7318085263797053271518/9740930048049625497765:Fraction),(4390464891590008098026/5844441362163225298659:Fraction),(7316797688174150395582/9740541159161125497765:Fraction),(21948462017656882039604/29221040144150626493295:Fraction),(65839592732465239752704/87661370432453629479885:Fraction),(13166760090344741216374/17531924086491075895977:Fraction),(7314223245644466579896/9739763381384125497765:Fraction)]
abbrev p1217 := params 0
abbrev ray1217 := rays 0
def bank1217 : Fin 1 → Cell := oneBank p1217 ray1217
theorem signs1217 : ∀ j, Signs p1217 (bank1217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1218 := params 1
abbrev ray1218 := rays 1
def bank1218 : Fin 1 → Cell := oneBank p1218 ray1218
theorem signs1218 : ∀ j, Signs p1218 (bank1218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1219 := params 2
abbrev ray1219 := rays 2
def bank1219 : Fin 1 → Cell := oneBank p1219 ray1219
theorem signs1219 : ∀ j, Signs p1219 (bank1219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1220 := params 3
abbrev ray1220 := rays 3
def bank1220 : Fin 1 → Cell := oneBank p1220 ray1220
theorem signs1220 : ∀ j, Signs p1220 (bank1220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1221 := params 4
abbrev ray1221 := rays 4
def bank1221 : Fin 1 → Cell := oneBank p1221 ray1221
theorem signs1221 : ∀ j, Signs p1221 (bank1221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1222 := params 5
abbrev ray1222 := rays 5
def bank1222 : Fin 1 → Cell := oneBank p1222 ray1222
theorem signs1222 : ∀ j, Signs p1222 (bank1222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1223 := params 6
abbrev ray1223 := rays 6
def bank1223 : Fin 1 → Cell := oneBank p1223 ray1223
theorem signs1223 : ∀ j, Signs p1223 (bank1223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1224 := params 7
abbrev ray1224 := rays 7
def bank1224 : Fin 1 → Cell := oneBank p1224 ray1224
theorem signs1224 : ∀ j, Signs p1224 (bank1224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1225 := params 8
abbrev ray1225 := rays 8
def bank1225 : Fin 1 → Cell := oneBank p1225 ray1225
theorem signs1225 : ∀ j, Signs p1225 (bank1225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1226 := params 9
abbrev ray1226 := rays 9
def bank1226 : Fin 1 → Cell := oneBank p1226 ray1226
theorem signs1226 : ∀ j, Signs p1226 (bank1226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1227 := params 10
abbrev ray1227 := rays 10
def bank1227 : Fin 1 → Cell := oneBank p1227 ray1227
theorem signs1227 : ∀ j, Signs p1227 (bank1227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1228 := params 11
abbrev ray1228 := rays 11
def bank1228 : Fin 1 → Cell := oneBank p1228 ray1228
theorem signs1228 : ∀ j, Signs p1228 (bank1228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1229 := params 12
abbrev ray1229 := rays 12
def bank1229 : Fin 1 → Cell := oneBank p1229 ray1229
theorem signs1229 : ∀ j, Signs p1229 (bank1229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1230 := params 13
abbrev ray1230 := rays 13
def bank1230 : Fin 1 → Cell := oneBank p1230 ray1230
theorem signs1230 : ∀ j, Signs p1230 (bank1230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1231 := params 14
abbrev ray1231 := rays 14
def bank1231 : Fin 1 → Cell := oneBank p1231 ray1231
theorem signs1231 : ∀ j, Signs p1231 (bank1231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1232 := params 15
abbrev ray1232 := rays 15
def bank1232 : Fin 1 → Cell := oneBank p1232 ray1232
theorem signs1232 : ∀ j, Signs p1232 (bank1232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1233 := params 16
abbrev ray1233 := rays 16
def bank1233 : Fin 1 → Cell := oneBank p1233 ray1233
theorem signs1233 : ∀ j, Signs p1233 (bank1233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1234 := params 17
abbrev ray1234 := rays 17
def bank1234 : Fin 1 → Cell := oneBank p1234 ray1234
theorem signs1234 : ∀ j, Signs p1234 (bank1234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1235 := params 18
abbrev ray1235 := rays 18
def bank1235 : Fin 1 → Cell := oneBank p1235 ray1235
theorem signs1235 : ∀ j, Signs p1235 (bank1235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1236 := params 19
abbrev ray1236 := rays 19
def bank1236 : Fin 1 → Cell := oneBank p1236 ray1236
theorem signs1236 : ∀ j, Signs p1236 (bank1236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1237 := params 20
abbrev ray1237 := rays 20
def bank1237 : Fin 1 → Cell := oneBank p1237 ray1237
theorem signs1237 : ∀ j, Signs p1237 (bank1237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1238 := params 21
abbrev ray1238 := rays 21
def bank1238 : Fin 1 → Cell := oneBank p1238 ray1238
theorem signs1238 : ∀ j, Signs p1238 (bank1238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1239 := params 22
abbrev ray1239 := rays 22
def bank1239 : Fin 1 → Cell := oneBank p1239 ray1239
theorem signs1239 : ∀ j, Signs p1239 (bank1239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1240 := params 23
abbrev ray1240 := rays 23
def bank1240 : Fin 1 → Cell := oneBank p1240 ray1240
theorem signs1240 : ∀ j, Signs p1240 (bank1240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1241 := params 24
abbrev ray1241 := rays 24
def bank1241 : Fin 1 → Cell := oneBank p1241 ray1241
theorem signs1241 : ∀ j, Signs p1241 (bank1241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1242 := params 25
abbrev ray1242 := rays 25
def bank1242 : Fin 1 → Cell := oneBank p1242 ray1242
theorem signs1242 : ∀ j, Signs p1242 (bank1242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1243 := params 26
abbrev ray1243 := rays 26
def bank1243 : Fin 1 → Cell := oneBank p1243 ray1243
theorem signs1243 : ∀ j, Signs p1243 (bank1243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1244 := params 27
abbrev ray1244 := rays 27
def bank1244 : Fin 1 → Cell := oneBank p1244 ray1244
theorem signs1244 : ∀ j, Signs p1244 (bank1244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1245 := params 28
abbrev ray1245 := rays 28
def bank1245 : Fin 1 → Cell := oneBank p1245 ray1245
theorem signs1245 : ∀ j, Signs p1245 (bank1245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1246 := params 29
abbrev ray1246 := rays 29
def bank1246 : Fin 1 → Cell := oneBank p1246 ray1246
theorem signs1246 : ∀ j, Signs p1246 (bank1246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1247 := params 30
abbrev ray1247 := rays 30
def bank1247 : Fin 1 → Cell := oneBank p1247 ray1247
theorem signs1247 : ∀ j, Signs p1247 (bank1247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1248 := params 31
abbrev ray1248 := rays 31
def bank1248 : Fin 1 → Cell := oneBank p1248 ray1248
theorem signs1248 : ∀ j, Signs p1248 (bank1248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01217_01248
