/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01345_01376
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99803536246878,99803372806212,99803209340969,99803045851152,99802882336763,99802718797804,99802555234277,99802391646184,99802228033527,99802064396310,99801900734533,99801737048200,99801573337312,99801409601872,99801245841882,99801082057344,99800918248260,99800754414633,99800590556464,99800426673756,99800262766511,99800098834732,99799934878419,99799770897576,99799606892205,99799442862308,99799278807887,99799114728945,99798950625484,99798786497505,99798622345011,99798458168004,99798293966487]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1344+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(34588362407163586568/46363603832870630355:Fraction),(21754163231449942660888/29162123477542876493295:Fraction),(587898563694137229472/788149733627300716035:Fraction),(65250991268384455281128/87482870432632129479885:Fraction),(65245243010465306822753/87481120432633879479885:Fraction),(7248832730581231137188/9719930048070625497765:Fraction),(21744582394606571146324/29159206810879126493295:Fraction),(13045600167256776538966/17495174086527825895977:Fraction),(3105821575731671107921/4165434306316232356185:Fraction),(621109596281360153296/833070194596596471237:Fraction),(9315823135934606282317/12495802918949197068555:Fraction),(945205713073510090/1267940428102429941:Fraction),(65199271325265551083588/87467120432647879479885:Fraction),(13038705271407699561070/17493074086529925895977:Fraction),(2414362312331309644252/3239393349357458499255:Fraction),(21727346110594923573962/29153956810884376493295:Fraction),(13035259054967054531564/17492024086530975895977:Fraction),(255570792317131344133/342974001696692664627:Fraction),(65164809851189969186866/87456620432658379479885:Fraction),(9308438386550494195132/12493552918951447068555:Fraction),(21717775387420990067366/29151040144220626493295:Fraction),(1760745564443324782864/2363550552234152148105:Fraction),(65141844208308876058021/87449620432665379479885:Fraction),(195603918312464031592/262606217515516905345:Fraction),(13026073042192333202293/17489224086533775895977:Fraction),(13024925089410551191004/17488874086534125895977:Fraction),(803936873182010995626/1079538523860152833085:Fraction),(13022629566332619227174/17488174086534825895977:Fraction),(4340493998684038348358/5829274695511725298659:Fraction),(620015923353676202924/832736861263596471237:Fraction),(65095934968765799456054/87435620432679379479885:Fraction),(65090197808723650838416/87433870432681129479885:Fraction)]
abbrev p1345 := params 0
abbrev ray1345 := rays 0
def bank1345 : Fin 1 → Cell := oneBank p1345 ray1345
theorem signs1345 : ∀ j, Signs p1345 (bank1345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1346 := params 1
abbrev ray1346 := rays 1
def bank1346 : Fin 1 → Cell := oneBank p1346 ray1346
theorem signs1346 : ∀ j, Signs p1346 (bank1346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1347 := params 2
abbrev ray1347 := rays 2
def bank1347 : Fin 1 → Cell := oneBank p1347 ray1347
theorem signs1347 : ∀ j, Signs p1347 (bank1347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1348 := params 3
abbrev ray1348 := rays 3
def bank1348 : Fin 1 → Cell := oneBank p1348 ray1348
theorem signs1348 : ∀ j, Signs p1348 (bank1348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1349 := params 4
abbrev ray1349 := rays 4
def bank1349 : Fin 1 → Cell := oneBank p1349 ray1349
theorem signs1349 : ∀ j, Signs p1349 (bank1349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1350 := params 5
abbrev ray1350 := rays 5
def bank1350 : Fin 1 → Cell := oneBank p1350 ray1350
theorem signs1350 : ∀ j, Signs p1350 (bank1350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1351 := params 6
abbrev ray1351 := rays 6
def bank1351 : Fin 1 → Cell := oneBank p1351 ray1351
theorem signs1351 : ∀ j, Signs p1351 (bank1351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1352 := params 7
abbrev ray1352 := rays 7
def bank1352 : Fin 1 → Cell := oneBank p1352 ray1352
theorem signs1352 : ∀ j, Signs p1352 (bank1352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1353 := params 8
abbrev ray1353 := rays 8
def bank1353 : Fin 1 → Cell := oneBank p1353 ray1353
theorem signs1353 : ∀ j, Signs p1353 (bank1353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1354 := params 9
abbrev ray1354 := rays 9
def bank1354 : Fin 1 → Cell := oneBank p1354 ray1354
theorem signs1354 : ∀ j, Signs p1354 (bank1354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1355 := params 10
abbrev ray1355 := rays 10
def bank1355 : Fin 1 → Cell := oneBank p1355 ray1355
theorem signs1355 : ∀ j, Signs p1355 (bank1355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1356 := params 11
abbrev ray1356 := rays 11
def bank1356 : Fin 1 → Cell := oneBank p1356 ray1356
theorem signs1356 : ∀ j, Signs p1356 (bank1356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1357 := params 12
abbrev ray1357 := rays 12
def bank1357 : Fin 1 → Cell := oneBank p1357 ray1357
theorem signs1357 : ∀ j, Signs p1357 (bank1357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1358 := params 13
abbrev ray1358 := rays 13
def bank1358 : Fin 1 → Cell := oneBank p1358 ray1358
theorem signs1358 : ∀ j, Signs p1358 (bank1358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1359 := params 14
abbrev ray1359 := rays 14
def bank1359 : Fin 1 → Cell := oneBank p1359 ray1359
theorem signs1359 : ∀ j, Signs p1359 (bank1359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1360 := params 15
abbrev ray1360 := rays 15
def bank1360 : Fin 1 → Cell := oneBank p1360 ray1360
theorem signs1360 : ∀ j, Signs p1360 (bank1360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1361 := params 16
abbrev ray1361 := rays 16
def bank1361 : Fin 1 → Cell := oneBank p1361 ray1361
theorem signs1361 : ∀ j, Signs p1361 (bank1361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1362 := params 17
abbrev ray1362 := rays 17
def bank1362 : Fin 1 → Cell := oneBank p1362 ray1362
theorem signs1362 : ∀ j, Signs p1362 (bank1362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1363 := params 18
abbrev ray1363 := rays 18
def bank1363 : Fin 1 → Cell := oneBank p1363 ray1363
theorem signs1363 : ∀ j, Signs p1363 (bank1363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1364 := params 19
abbrev ray1364 := rays 19
def bank1364 : Fin 1 → Cell := oneBank p1364 ray1364
theorem signs1364 : ∀ j, Signs p1364 (bank1364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1365 := params 20
abbrev ray1365 := rays 20
def bank1365 : Fin 1 → Cell := oneBank p1365 ray1365
theorem signs1365 : ∀ j, Signs p1365 (bank1365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1366 := params 21
abbrev ray1366 := rays 21
def bank1366 : Fin 1 → Cell := oneBank p1366 ray1366
theorem signs1366 : ∀ j, Signs p1366 (bank1366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1367 := params 22
abbrev ray1367 := rays 22
def bank1367 : Fin 1 → Cell := oneBank p1367 ray1367
theorem signs1367 : ∀ j, Signs p1367 (bank1367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1368 := params 23
abbrev ray1368 := rays 23
def bank1368 : Fin 1 → Cell := oneBank p1368 ray1368
theorem signs1368 : ∀ j, Signs p1368 (bank1368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1369 := params 24
abbrev ray1369 := rays 24
def bank1369 : Fin 1 → Cell := oneBank p1369 ray1369
theorem signs1369 : ∀ j, Signs p1369 (bank1369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1370 := params 25
abbrev ray1370 := rays 25
def bank1370 : Fin 1 → Cell := oneBank p1370 ray1370
theorem signs1370 : ∀ j, Signs p1370 (bank1370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1371 := params 26
abbrev ray1371 := rays 26
def bank1371 : Fin 1 → Cell := oneBank p1371 ray1371
theorem signs1371 : ∀ j, Signs p1371 (bank1371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1372 := params 27
abbrev ray1372 := rays 27
def bank1372 : Fin 1 → Cell := oneBank p1372 ray1372
theorem signs1372 : ∀ j, Signs p1372 (bank1372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1373 := params 28
abbrev ray1373 := rays 28
def bank1373 : Fin 1 → Cell := oneBank p1373 ray1373
theorem signs1373 : ∀ j, Signs p1373 (bank1373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1374 := params 29
abbrev ray1374 := rays 29
def bank1374 : Fin 1 → Cell := oneBank p1374 ray1374
theorem signs1374 : ∀ j, Signs p1374 (bank1374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1375 := params 30
abbrev ray1375 := rays 30
def bank1375 : Fin 1 → Cell := oneBank p1375 ray1375
theorem signs1375 : ∀ j, Signs p1375 (bank1375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1376 := params 31
abbrev ray1376 := rays 31
def bank1376 : Fin 1 → Cell := oneBank p1376 ray1376
theorem signs1376 : ∀ j, Signs p1376 (bank1376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01345_01376
