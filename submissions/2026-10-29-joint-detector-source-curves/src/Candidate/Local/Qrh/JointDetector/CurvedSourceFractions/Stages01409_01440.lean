/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01409_01440
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99793026589443,99792861580303,99792696546727,99792531488716,99792366406273,99792201299400,99792036168100,99791871012374,99791705832225,99791540627655,99791375398666,99791210145260,99791044867439,99790879565206,99790714238562,99790548887510,99790383512052,99790218112190,99790052687926,99789887239263,99789721766203,99789556268748,99789390746900,99789225200661,99789059630033,99788894035018,99788728415619,99788562771838,99788397103677,99788231411138,99788065694223,99787899952934,99787734187274]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1408+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(21633708541837813664233/29125373477579626493295:Fraction),(1442120072050604780206/1941652676283125099553:Fraction),(64889681905189068432266/87372620432742379479885:Fraction),(64883960392315909690516/87370870432744129479885:Fraction),(1441738665014838211921/1941536009616575099553:Fraction),(12974503856656889864000/17473474086549525895977:Fraction),(564059117088500752090/759701047241298951999:Fraction),(1029540951038691429952/1386728102107160785395:Fraction),(12971071993599238206710/17472424086550575895977:Fraction),(12969928213391809968265/17472074086550925895977:Fraction),(7204880356930954933108/9706513381417375497765:Fraction),(4322547012147371385106/5823791362183875298659:Fraction),(64832488198576078452538/87355120432759879479885:Fraction),(4321784735960260881296/5823558028850775298659:Fraction),(64821054926842113878908/87351620432763379479885:Fraction),(1851866818251183252688/2495710583793289413711:Fraction),(366156057487356884822/493492205834841127005:Fraction),(617180076005966505784/831870194597796471237:Fraction),(9256884626913451979264/12477802918967197068555:Fraction),(194572005534391744124/262290902200516905345:Fraction),(21595588114784589732091/29113706810924626493295:Fraction),(21593683556804521311068/29113123477591876493295:Fraction),(4318355869559545381000/5822508028851825298659:Fraction),(1750530411921081363662/2360428930615652148105:Fraction),(64763913485763442099799/87334120432780879479885:Fraction),(799483969817318699456/1078177412750402833085:Fraction),(64752489449409579216719/87330620432784379479885:Fraction),(9249539770102169453464/12475552918969447068555:Fraction),(2397817347376742034512/3234337793806958499255:Fraction),(64735358192483366501164/87325370432789629479885:Fraction),(1438436645622726375811/1940524898506475099553:Fraction),(1961331507226217921696/2646117285842216044845:Fraction)]
abbrev p1409 := params 0
abbrev ray1409 := rays 0
def bank1409 : Fin 1 → Cell := oneBank p1409 ray1409
theorem signs1409 : ∀ j, Signs p1409 (bank1409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1410 := params 1
abbrev ray1410 := rays 1
def bank1410 : Fin 1 → Cell := oneBank p1410 ray1410
theorem signs1410 : ∀ j, Signs p1410 (bank1410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1411 := params 2
abbrev ray1411 := rays 2
def bank1411 : Fin 1 → Cell := oneBank p1411 ray1411
theorem signs1411 : ∀ j, Signs p1411 (bank1411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1412 := params 3
abbrev ray1412 := rays 3
def bank1412 : Fin 1 → Cell := oneBank p1412 ray1412
theorem signs1412 : ∀ j, Signs p1412 (bank1412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1413 := params 4
abbrev ray1413 := rays 4
def bank1413 : Fin 1 → Cell := oneBank p1413 ray1413
theorem signs1413 : ∀ j, Signs p1413 (bank1413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1414 := params 5
abbrev ray1414 := rays 5
def bank1414 : Fin 1 → Cell := oneBank p1414 ray1414
theorem signs1414 : ∀ j, Signs p1414 (bank1414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1415 := params 6
abbrev ray1415 := rays 6
def bank1415 : Fin 1 → Cell := oneBank p1415 ray1415
theorem signs1415 : ∀ j, Signs p1415 (bank1415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1416 := params 7
abbrev ray1416 := rays 7
def bank1416 : Fin 1 → Cell := oneBank p1416 ray1416
theorem signs1416 : ∀ j, Signs p1416 (bank1416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1417 := params 8
abbrev ray1417 := rays 8
def bank1417 : Fin 1 → Cell := oneBank p1417 ray1417
theorem signs1417 : ∀ j, Signs p1417 (bank1417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1418 := params 9
abbrev ray1418 := rays 9
def bank1418 : Fin 1 → Cell := oneBank p1418 ray1418
theorem signs1418 : ∀ j, Signs p1418 (bank1418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1419 := params 10
abbrev ray1419 := rays 10
def bank1419 : Fin 1 → Cell := oneBank p1419 ray1419
theorem signs1419 : ∀ j, Signs p1419 (bank1419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1420 := params 11
abbrev ray1420 := rays 11
def bank1420 : Fin 1 → Cell := oneBank p1420 ray1420
theorem signs1420 : ∀ j, Signs p1420 (bank1420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1421 := params 12
abbrev ray1421 := rays 12
def bank1421 : Fin 1 → Cell := oneBank p1421 ray1421
theorem signs1421 : ∀ j, Signs p1421 (bank1421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1422 := params 13
abbrev ray1422 := rays 13
def bank1422 : Fin 1 → Cell := oneBank p1422 ray1422
theorem signs1422 : ∀ j, Signs p1422 (bank1422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1423 := params 14
abbrev ray1423 := rays 14
def bank1423 : Fin 1 → Cell := oneBank p1423 ray1423
theorem signs1423 : ∀ j, Signs p1423 (bank1423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1424 := params 15
abbrev ray1424 := rays 15
def bank1424 : Fin 1 → Cell := oneBank p1424 ray1424
theorem signs1424 : ∀ j, Signs p1424 (bank1424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1425 := params 16
abbrev ray1425 := rays 16
def bank1425 : Fin 1 → Cell := oneBank p1425 ray1425
theorem signs1425 : ∀ j, Signs p1425 (bank1425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1426 := params 17
abbrev ray1426 := rays 17
def bank1426 : Fin 1 → Cell := oneBank p1426 ray1426
theorem signs1426 : ∀ j, Signs p1426 (bank1426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1427 := params 18
abbrev ray1427 := rays 18
def bank1427 : Fin 1 → Cell := oneBank p1427 ray1427
theorem signs1427 : ∀ j, Signs p1427 (bank1427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1428 := params 19
abbrev ray1428 := rays 19
def bank1428 : Fin 1 → Cell := oneBank p1428 ray1428
theorem signs1428 : ∀ j, Signs p1428 (bank1428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1429 := params 20
abbrev ray1429 := rays 20
def bank1429 : Fin 1 → Cell := oneBank p1429 ray1429
theorem signs1429 : ∀ j, Signs p1429 (bank1429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1430 := params 21
abbrev ray1430 := rays 21
def bank1430 : Fin 1 → Cell := oneBank p1430 ray1430
theorem signs1430 : ∀ j, Signs p1430 (bank1430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1431 := params 22
abbrev ray1431 := rays 22
def bank1431 : Fin 1 → Cell := oneBank p1431 ray1431
theorem signs1431 : ∀ j, Signs p1431 (bank1431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1432 := params 23
abbrev ray1432 := rays 23
def bank1432 : Fin 1 → Cell := oneBank p1432 ray1432
theorem signs1432 : ∀ j, Signs p1432 (bank1432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1433 := params 24
abbrev ray1433 := rays 24
def bank1433 : Fin 1 → Cell := oneBank p1433 ray1433
theorem signs1433 : ∀ j, Signs p1433 (bank1433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1434 := params 25
abbrev ray1434 := rays 25
def bank1434 : Fin 1 → Cell := oneBank p1434 ray1434
theorem signs1434 : ∀ j, Signs p1434 (bank1434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1435 := params 26
abbrev ray1435 := rays 26
def bank1435 : Fin 1 → Cell := oneBank p1435 ray1435
theorem signs1435 : ∀ j, Signs p1435 (bank1435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1436 := params 27
abbrev ray1436 := rays 27
def bank1436 : Fin 1 → Cell := oneBank p1436 ray1436
theorem signs1436 : ∀ j, Signs p1436 (bank1436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1437 := params 28
abbrev ray1437 := rays 28
def bank1437 : Fin 1 → Cell := oneBank p1437 ray1437
theorem signs1437 : ∀ j, Signs p1437 (bank1437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1438 := params 29
abbrev ray1438 := rays 29
def bank1438 : Fin 1 → Cell := oneBank p1438 ray1438
theorem signs1438 : ∀ j, Signs p1438 (bank1438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1439 := params 30
abbrev ray1439 := rays 30
def bank1439 : Fin 1 → Cell := oneBank p1439 ray1439
theorem signs1439 : ∀ j, Signs p1439 (bank1439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1440 := params 31
abbrev ray1440 := rays 31
def bank1440 : Fin 1 → Cell := oneBank p1440 ray1440
theorem signs1440 : ∀ j, Signs p1440 (bank1440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01409_01440
