/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01377_01408
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99798293966487,99798129740462,99797965489931,99797801214895,99797636915358,99797472591321,99797308242787,99797143869757,99796979472234,99796815050220,99796650603717,99796486132728,99796321637254,99796157117299,99795992572863,99795828003950,99795663410561,99795498792699,99795334150365,99795169483563,99795004792294,99794840076560,99794675336364,99794510571707,99794345782592,99794180969021,99794016130997,99793851268521,99793686381596,99793521470223,99793356534405,99793191574144,99793026589443]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1376+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(482107123655659856993/647645336538391699851:Fraction),(9296960771668951488016/12490052918954947068555:Fraction),(7230332239417877181922/9714291159187375497765:Fraction),(4337816982084341917970/5828458028845875298659:Fraction),(65061520352757201368744/87425120432689879479885:Fraction),(65055785797725352416016/87423370432691629479885:Fraction),(481852239168580710874/647567558760691699851:Fraction),(65044318601316468968308/87419870432695129479885:Fraction),(21679528653338825914292/29139373477565626493295:Fraction),(1445174514273146137564/1942586009615525099553:Fraction),(13005424273957128538510/17482924086540075895977:Fraction),(9288769917272121387964/12487552918957447068555:Fraction),(2407987352493335040256/3237448904914958499255:Fraction),(13001985487482084890492/17481874086541125895977:Fraction),(21668065800957934158058/29135873477569126493295:Fraction),(619033020876774069760/832436861263896471237:Fraction),(12998547605339973706777/17480824086542175895977:Fraction),(64987008685111462480486/87402370432712629479885:Fraction),(481342817696675267626/647412003205291699851:Fraction),(64975551916813876543582/87398870432716129479885:Fraction),(481257959186539190624/647386077279391699851:Fraction),(1443646597498277620688/1942119342949325099553:Fraction),(64958370330346476778772/87393620432721379479885:Fraction),(12990528719438025599156/17478374086544625895977:Fraction),(7216324212199446228214/9710013381413875497765:Fraction),(9277313149481365471498/12484052918960947068555:Fraction),(4329031148585559843130/5825774695515225298659:Fraction),(7214415803912861387246/9709430048081125497765:Fraction),(64924018287564337446794/87383120432731879479885:Fraction),(9274042023425755787116/12483052918961947068555:Fraction),(480833859899180710910/647256447649891699851:Fraction),(64906847832915828940624/87377870432737129479885:Fraction)]
abbrev p1377 := params 0
abbrev ray1377 := rays 0
def bank1377 : Fin 1 → Cell := oneBank p1377 ray1377
theorem signs1377 : ∀ j, Signs p1377 (bank1377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1378 := params 1
abbrev ray1378 := rays 1
def bank1378 : Fin 1 → Cell := oneBank p1378 ray1378
theorem signs1378 : ∀ j, Signs p1378 (bank1378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1379 := params 2
abbrev ray1379 := rays 2
def bank1379 : Fin 1 → Cell := oneBank p1379 ray1379
theorem signs1379 : ∀ j, Signs p1379 (bank1379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1380 := params 3
abbrev ray1380 := rays 3
def bank1380 : Fin 1 → Cell := oneBank p1380 ray1380
theorem signs1380 : ∀ j, Signs p1380 (bank1380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1381 := params 4
abbrev ray1381 := rays 4
def bank1381 : Fin 1 → Cell := oneBank p1381 ray1381
theorem signs1381 : ∀ j, Signs p1381 (bank1381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1382 := params 5
abbrev ray1382 := rays 5
def bank1382 : Fin 1 → Cell := oneBank p1382 ray1382
theorem signs1382 : ∀ j, Signs p1382 (bank1382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1383 := params 6
abbrev ray1383 := rays 6
def bank1383 : Fin 1 → Cell := oneBank p1383 ray1383
theorem signs1383 : ∀ j, Signs p1383 (bank1383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1384 := params 7
abbrev ray1384 := rays 7
def bank1384 : Fin 1 → Cell := oneBank p1384 ray1384
theorem signs1384 : ∀ j, Signs p1384 (bank1384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1385 := params 8
abbrev ray1385 := rays 8
def bank1385 : Fin 1 → Cell := oneBank p1385 ray1385
theorem signs1385 : ∀ j, Signs p1385 (bank1385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1386 := params 9
abbrev ray1386 := rays 9
def bank1386 : Fin 1 → Cell := oneBank p1386 ray1386
theorem signs1386 : ∀ j, Signs p1386 (bank1386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1387 := params 10
abbrev ray1387 := rays 10
def bank1387 : Fin 1 → Cell := oneBank p1387 ray1387
theorem signs1387 : ∀ j, Signs p1387 (bank1387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1388 := params 11
abbrev ray1388 := rays 11
def bank1388 : Fin 1 → Cell := oneBank p1388 ray1388
theorem signs1388 : ∀ j, Signs p1388 (bank1388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1389 := params 12
abbrev ray1389 := rays 12
def bank1389 : Fin 1 → Cell := oneBank p1389 ray1389
theorem signs1389 : ∀ j, Signs p1389 (bank1389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1390 := params 13
abbrev ray1390 := rays 13
def bank1390 : Fin 1 → Cell := oneBank p1390 ray1390
theorem signs1390 : ∀ j, Signs p1390 (bank1390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1391 := params 14
abbrev ray1391 := rays 14
def bank1391 : Fin 1 → Cell := oneBank p1391 ray1391
theorem signs1391 : ∀ j, Signs p1391 (bank1391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1392 := params 15
abbrev ray1392 := rays 15
def bank1392 : Fin 1 → Cell := oneBank p1392 ray1392
theorem signs1392 : ∀ j, Signs p1392 (bank1392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1393 := params 16
abbrev ray1393 := rays 16
def bank1393 : Fin 1 → Cell := oneBank p1393 ray1393
theorem signs1393 : ∀ j, Signs p1393 (bank1393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1394 := params 17
abbrev ray1394 := rays 17
def bank1394 : Fin 1 → Cell := oneBank p1394 ray1394
theorem signs1394 : ∀ j, Signs p1394 (bank1394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1395 := params 18
abbrev ray1395 := rays 18
def bank1395 : Fin 1 → Cell := oneBank p1395 ray1395
theorem signs1395 : ∀ j, Signs p1395 (bank1395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1396 := params 19
abbrev ray1396 := rays 19
def bank1396 : Fin 1 → Cell := oneBank p1396 ray1396
theorem signs1396 : ∀ j, Signs p1396 (bank1396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1397 := params 20
abbrev ray1397 := rays 20
def bank1397 : Fin 1 → Cell := oneBank p1397 ray1397
theorem signs1397 : ∀ j, Signs p1397 (bank1397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1398 := params 21
abbrev ray1398 := rays 21
def bank1398 : Fin 1 → Cell := oneBank p1398 ray1398
theorem signs1398 : ∀ j, Signs p1398 (bank1398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1399 := params 22
abbrev ray1399 := rays 22
def bank1399 : Fin 1 → Cell := oneBank p1399 ray1399
theorem signs1399 : ∀ j, Signs p1399 (bank1399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1400 := params 23
abbrev ray1400 := rays 23
def bank1400 : Fin 1 → Cell := oneBank p1400 ray1400
theorem signs1400 : ∀ j, Signs p1400 (bank1400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1401 := params 24
abbrev ray1401 := rays 24
def bank1401 : Fin 1 → Cell := oneBank p1401 ray1401
theorem signs1401 : ∀ j, Signs p1401 (bank1401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1402 := params 25
abbrev ray1402 := rays 25
def bank1402 : Fin 1 → Cell := oneBank p1402 ray1402
theorem signs1402 : ∀ j, Signs p1402 (bank1402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1403 := params 26
abbrev ray1403 := rays 26
def bank1403 : Fin 1 → Cell := oneBank p1403 ray1403
theorem signs1403 : ∀ j, Signs p1403 (bank1403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1404 := params 27
abbrev ray1404 := rays 27
def bank1404 : Fin 1 → Cell := oneBank p1404 ray1404
theorem signs1404 : ∀ j, Signs p1404 (bank1404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1405 := params 28
abbrev ray1405 := rays 28
def bank1405 : Fin 1 → Cell := oneBank p1405 ray1405
theorem signs1405 : ∀ j, Signs p1405 (bank1405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1406 := params 29
abbrev ray1406 := rays 29
def bank1406 : Fin 1 → Cell := oneBank p1406 ray1406
theorem signs1406 : ∀ j, Signs p1406 (bank1406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1407 := params 30
abbrev ray1407 := rays 30
def bank1407 : Fin 1 → Cell := oneBank p1407 ray1407
theorem signs1407 : ∀ j, Signs p1407 (bank1407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1408 := params 31
abbrev ray1408 := rays 31
def bank1408 : Fin 1 → Cell := oneBank p1408 ray1408
theorem signs1408 : ∀ j, Signs p1408 (bank1408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01377_01408
