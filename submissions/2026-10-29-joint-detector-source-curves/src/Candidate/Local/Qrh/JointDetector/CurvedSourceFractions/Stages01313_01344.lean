/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01313_01344
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99808753358456,99808590705414,99808428027724,99808265325388,99808102598409,99807939846789,99807777070531,99807614269636,99807451444106,99807288593944,99807125719153,99806962819734,99806799895690,99806636947022,99806473973733,99806310975826,99806147953302,99805984906163,99805821834413,99805658738053,99805495617085,99805332471512,99805169301335,99805006106557,99804842887180,99804679643207,99804516374640,99804353081480,99804189763731,99804026421394,99803863054471,99803699662965,99803536246878]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1312+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1768985347910743978984/2366057308988402148105:Fraction),(7271855009083435455488/9726930048063625497765:Fraction),(65440932112633706560712/87540620432574379479885:Fraction),(65435168965356433201024/87538870432576129479885:Fraction),(7269934095619968525379/9726346714730875497765:Fraction),(13084728915538662734678/17507074086515925895977:Fraction),(660786700377636381328/884177984167488681615:Fraction),(161511415159776387602/216128075142180566617:Fraction),(5031258580254295905044/6733086187121913806145:Fraction),(7266733578922523865746/9725374492509625497765:Fraction),(622808025707898167075/833586861262746471237:Fraction),(1767272513794460253008/2365537038718652148105:Fraction),(13076664872854625249272/17504624086518375895977:Fraction),(65443008548788352872/87608979412005635115:Fraction),(1452706839091016494439/1944880454057675099553:Fraction),(65366051020895539048592/87517870432597129479885:Fraction),(21786764701624226553616/29172040144199626493295:Fraction),(21784845670345894419526/29171456810866876493295:Fraction),(65348780960249369592442/87512620432602379479885:Fraction),(21781008243899742679162/29170290144201376493295:Fraction),(13067453909254395189857/17501824086521175895977:Fraction),(65331515404021472599522/87507370432607629479885:Fraction),(161298172501715124210/216063260327430566617:Fraction),(65320006586510116774147/87503870432611129479885:Fraction),(4354283542146793309024/5833474695507525298659:Fraction),(3109928547632457253151/4166684306314982356185:Fraction),(13060549382343673477270/17499724086523275895977:Fraction),(13059398829118215561182/17499374086523625895977:Fraction),(161212944254072247472/216037334401530566617:Fraction),(65285491743694500567416/87493370432621629479885:Fraction),(21759913221999888684229/29163873477541126493295:Fraction),(483511035947193562318/648073114315741699851:Fraction)]
abbrev p1313 := params 0
abbrev ray1313 := rays 0
def bank1313 : Fin 1 → Cell := oneBank p1313 ray1313
theorem signs1313 : ∀ j, Signs p1313 (bank1313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1314 := params 1
abbrev ray1314 := rays 1
def bank1314 : Fin 1 → Cell := oneBank p1314 ray1314
theorem signs1314 : ∀ j, Signs p1314 (bank1314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1315 := params 2
abbrev ray1315 := rays 2
def bank1315 : Fin 1 → Cell := oneBank p1315 ray1315
theorem signs1315 : ∀ j, Signs p1315 (bank1315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1316 := params 3
abbrev ray1316 := rays 3
def bank1316 : Fin 1 → Cell := oneBank p1316 ray1316
theorem signs1316 : ∀ j, Signs p1316 (bank1316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1317 := params 4
abbrev ray1317 := rays 4
def bank1317 : Fin 1 → Cell := oneBank p1317 ray1317
theorem signs1317 : ∀ j, Signs p1317 (bank1317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1318 := params 5
abbrev ray1318 := rays 5
def bank1318 : Fin 1 → Cell := oneBank p1318 ray1318
theorem signs1318 : ∀ j, Signs p1318 (bank1318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1319 := params 6
abbrev ray1319 := rays 6
def bank1319 : Fin 1 → Cell := oneBank p1319 ray1319
theorem signs1319 : ∀ j, Signs p1319 (bank1319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1320 := params 7
abbrev ray1320 := rays 7
def bank1320 : Fin 1 → Cell := oneBank p1320 ray1320
theorem signs1320 : ∀ j, Signs p1320 (bank1320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1321 := params 8
abbrev ray1321 := rays 8
def bank1321 : Fin 1 → Cell := oneBank p1321 ray1321
theorem signs1321 : ∀ j, Signs p1321 (bank1321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1322 := params 9
abbrev ray1322 := rays 9
def bank1322 : Fin 1 → Cell := oneBank p1322 ray1322
theorem signs1322 : ∀ j, Signs p1322 (bank1322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1323 := params 10
abbrev ray1323 := rays 10
def bank1323 : Fin 1 → Cell := oneBank p1323 ray1323
theorem signs1323 : ∀ j, Signs p1323 (bank1323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1324 := params 11
abbrev ray1324 := rays 11
def bank1324 : Fin 1 → Cell := oneBank p1324 ray1324
theorem signs1324 : ∀ j, Signs p1324 (bank1324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1325 := params 12
abbrev ray1325 := rays 12
def bank1325 : Fin 1 → Cell := oneBank p1325 ray1325
theorem signs1325 : ∀ j, Signs p1325 (bank1325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1326 := params 13
abbrev ray1326 := rays 13
def bank1326 : Fin 1 → Cell := oneBank p1326 ray1326
theorem signs1326 : ∀ j, Signs p1326 (bank1326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1327 := params 14
abbrev ray1327 := rays 14
def bank1327 : Fin 1 → Cell := oneBank p1327 ray1327
theorem signs1327 : ∀ j, Signs p1327 (bank1327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1328 := params 15
abbrev ray1328 := rays 15
def bank1328 : Fin 1 → Cell := oneBank p1328 ray1328
theorem signs1328 : ∀ j, Signs p1328 (bank1328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1329 := params 16
abbrev ray1329 := rays 16
def bank1329 : Fin 1 → Cell := oneBank p1329 ray1329
theorem signs1329 : ∀ j, Signs p1329 (bank1329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1330 := params 17
abbrev ray1330 := rays 17
def bank1330 : Fin 1 → Cell := oneBank p1330 ray1330
theorem signs1330 : ∀ j, Signs p1330 (bank1330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1331 := params 18
abbrev ray1331 := rays 18
def bank1331 : Fin 1 → Cell := oneBank p1331 ray1331
theorem signs1331 : ∀ j, Signs p1331 (bank1331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1332 := params 19
abbrev ray1332 := rays 19
def bank1332 : Fin 1 → Cell := oneBank p1332 ray1332
theorem signs1332 : ∀ j, Signs p1332 (bank1332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1333 := params 20
abbrev ray1333 := rays 20
def bank1333 : Fin 1 → Cell := oneBank p1333 ray1333
theorem signs1333 : ∀ j, Signs p1333 (bank1333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1334 := params 21
abbrev ray1334 := rays 21
def bank1334 : Fin 1 → Cell := oneBank p1334 ray1334
theorem signs1334 : ∀ j, Signs p1334 (bank1334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1335 := params 22
abbrev ray1335 := rays 22
def bank1335 : Fin 1 → Cell := oneBank p1335 ray1335
theorem signs1335 : ∀ j, Signs p1335 (bank1335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1336 := params 23
abbrev ray1336 := rays 23
def bank1336 : Fin 1 → Cell := oneBank p1336 ray1336
theorem signs1336 : ∀ j, Signs p1336 (bank1336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1337 := params 24
abbrev ray1337 := rays 24
def bank1337 : Fin 1 → Cell := oneBank p1337 ray1337
theorem signs1337 : ∀ j, Signs p1337 (bank1337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1338 := params 25
abbrev ray1338 := rays 25
def bank1338 : Fin 1 → Cell := oneBank p1338 ray1338
theorem signs1338 : ∀ j, Signs p1338 (bank1338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1339 := params 26
abbrev ray1339 := rays 26
def bank1339 : Fin 1 → Cell := oneBank p1339 ray1339
theorem signs1339 : ∀ j, Signs p1339 (bank1339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1340 := params 27
abbrev ray1340 := rays 27
def bank1340 : Fin 1 → Cell := oneBank p1340 ray1340
theorem signs1340 : ∀ j, Signs p1340 (bank1340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1341 := params 28
abbrev ray1341 := rays 28
def bank1341 : Fin 1 → Cell := oneBank p1341 ray1341
theorem signs1341 : ∀ j, Signs p1341 (bank1341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1342 := params 29
abbrev ray1342 := rays 29
def bank1342 : Fin 1 → Cell := oneBank p1342 ray1342
theorem signs1342 : ∀ j, Signs p1342 (bank1342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1343 := params 30
abbrev ray1343 := rays 30
def bank1343 : Fin 1 → Cell := oneBank p1343 ray1343
theorem signs1343 : ∀ j, Signs p1343 (bank1343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1344 := params 31
abbrev ray1344 := rays 31
def bank1344 : Fin 1 → Cell := oneBank p1344 ray1344
theorem signs1344 : ∀ j, Signs p1344 (bank1344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01313_01344
