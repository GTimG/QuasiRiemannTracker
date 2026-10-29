/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01473_01504
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99782416830896,99782250262184,99782083669173,99781917051866,99781750410265,99781583744371,99781417054187,99781250339716,99781083600959,99780916837918,99780750050596,99780583238994,99780416403115,99780249542961,99780082658534,99779915749837,99779748816871,99779581859638,99779414878141,99779247872382,99779080842362,99778913788085,99778746709552,99778579606765,99778412479726,99778245328437,99778078152902,99777910953121,99777743729097,99777576480832,99777409208328,99777241911587,99777074590611]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1472+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(21511925938525056782368/29088040144283626493295:Fraction),(64530083346424433071262/87262370432852629479885:Fraction),(7169376522557696770114/9695624492539375497765:Fraction),(21506231702750871466744/29086290144285376493295:Fraction),(1843228644633620956507/2493060583795939413711:Fraction),(64507309841933233057204/87255370432859629479885:Fraction),(1433369265500744104021/1938969342952475099553:Fraction),(21498641700642136832974/29083956810954376493295:Fraction),(3793543122483035861473/5132360025462639969405:Fraction),(796105458164998641056/1077140375714402833085:Fraction),(7164316909937734382744/9694068936985375497765:Fraction),(43416270770029202000/58750754500249245441:Fraction),(477536828322500127116/646245336539791699851:Fraction),(64461782602603853705659/87241370432873629479885:Fraction),(64456093207709081862976/87239620432875379479885:Fraction),(104797406279535094304/141850195825816470699:Fraction),(64444717565269981794007/87236120432878879479885:Fraction),(7159892096852664238256/9692707825875625497765:Fraction),(7159260272263329264859/9692513381431375497765:Fraction),(9203950836463019764424/12461552918983447068555:Fraction),(197009079774607452092/266755719978244279755:Fraction),(4294418891112159628094/5815158028859175298659:Fraction),(12882119494660408275806/17445124086577875895977:Fraction),(12880982525865455987095/17444774086578225895977:Fraction),(4293281840775657267976/5814808028859525298659:Fraction),(64393543643424457723082/87220370432894629479885:Fraction),(64387860724750486326656/87218620432896379479885:Fraction),(1021939308082985388133/1384394768776160785395:Fraction),(64376494366520843430914/87215120432899879479885:Fraction),(12874162430046426039590/17442674086580325895977:Fraction),(2383893694828598623232/3230060016033458499255:Fraction),(21453149473408179484438/29069956810968376493295:Fraction)]
abbrev p1473 := params 0
abbrev ray1473 := rays 0
def bank1473 : Fin 1 → Cell := oneBank p1473 ray1473
theorem signs1473 : ∀ j, Signs p1473 (bank1473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1474 := params 1
abbrev ray1474 := rays 1
def bank1474 : Fin 1 → Cell := oneBank p1474 ray1474
theorem signs1474 : ∀ j, Signs p1474 (bank1474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1475 := params 2
abbrev ray1475 := rays 2
def bank1475 : Fin 1 → Cell := oneBank p1475 ray1475
theorem signs1475 : ∀ j, Signs p1475 (bank1475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1476 := params 3
abbrev ray1476 := rays 3
def bank1476 : Fin 1 → Cell := oneBank p1476 ray1476
theorem signs1476 : ∀ j, Signs p1476 (bank1476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1477 := params 4
abbrev ray1477 := rays 4
def bank1477 : Fin 1 → Cell := oneBank p1477 ray1477
theorem signs1477 : ∀ j, Signs p1477 (bank1477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1478 := params 5
abbrev ray1478 := rays 5
def bank1478 : Fin 1 → Cell := oneBank p1478 ray1478
theorem signs1478 : ∀ j, Signs p1478 (bank1478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1479 := params 6
abbrev ray1479 := rays 6
def bank1479 : Fin 1 → Cell := oneBank p1479 ray1479
theorem signs1479 : ∀ j, Signs p1479 (bank1479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1480 := params 7
abbrev ray1480 := rays 7
def bank1480 : Fin 1 → Cell := oneBank p1480 ray1480
theorem signs1480 : ∀ j, Signs p1480 (bank1480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1481 := params 8
abbrev ray1481 := rays 8
def bank1481 : Fin 1 → Cell := oneBank p1481 ray1481
theorem signs1481 : ∀ j, Signs p1481 (bank1481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1482 := params 9
abbrev ray1482 := rays 9
def bank1482 : Fin 1 → Cell := oneBank p1482 ray1482
theorem signs1482 : ∀ j, Signs p1482 (bank1482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1483 := params 10
abbrev ray1483 := rays 10
def bank1483 : Fin 1 → Cell := oneBank p1483 ray1483
theorem signs1483 : ∀ j, Signs p1483 (bank1483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1484 := params 11
abbrev ray1484 := rays 11
def bank1484 : Fin 1 → Cell := oneBank p1484 ray1484
theorem signs1484 : ∀ j, Signs p1484 (bank1484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1485 := params 12
abbrev ray1485 := rays 12
def bank1485 : Fin 1 → Cell := oneBank p1485 ray1485
theorem signs1485 : ∀ j, Signs p1485 (bank1485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1486 := params 13
abbrev ray1486 := rays 13
def bank1486 : Fin 1 → Cell := oneBank p1486 ray1486
theorem signs1486 : ∀ j, Signs p1486 (bank1486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1487 := params 14
abbrev ray1487 := rays 14
def bank1487 : Fin 1 → Cell := oneBank p1487 ray1487
theorem signs1487 : ∀ j, Signs p1487 (bank1487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1488 := params 15
abbrev ray1488 := rays 15
def bank1488 : Fin 1 → Cell := oneBank p1488 ray1488
theorem signs1488 : ∀ j, Signs p1488 (bank1488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1489 := params 16
abbrev ray1489 := rays 16
def bank1489 : Fin 1 → Cell := oneBank p1489 ray1489
theorem signs1489 : ∀ j, Signs p1489 (bank1489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1490 := params 17
abbrev ray1490 := rays 17
def bank1490 : Fin 1 → Cell := oneBank p1490 ray1490
theorem signs1490 : ∀ j, Signs p1490 (bank1490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1491 := params 18
abbrev ray1491 := rays 18
def bank1491 : Fin 1 → Cell := oneBank p1491 ray1491
theorem signs1491 : ∀ j, Signs p1491 (bank1491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1492 := params 19
abbrev ray1492 := rays 19
def bank1492 : Fin 1 → Cell := oneBank p1492 ray1492
theorem signs1492 : ∀ j, Signs p1492 (bank1492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1493 := params 20
abbrev ray1493 := rays 20
def bank1493 : Fin 1 → Cell := oneBank p1493 ray1493
theorem signs1493 : ∀ j, Signs p1493 (bank1493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1494 := params 21
abbrev ray1494 := rays 21
def bank1494 : Fin 1 → Cell := oneBank p1494 ray1494
theorem signs1494 : ∀ j, Signs p1494 (bank1494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1495 := params 22
abbrev ray1495 := rays 22
def bank1495 : Fin 1 → Cell := oneBank p1495 ray1495
theorem signs1495 : ∀ j, Signs p1495 (bank1495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1496 := params 23
abbrev ray1496 := rays 23
def bank1496 : Fin 1 → Cell := oneBank p1496 ray1496
theorem signs1496 : ∀ j, Signs p1496 (bank1496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1497 := params 24
abbrev ray1497 := rays 24
def bank1497 : Fin 1 → Cell := oneBank p1497 ray1497
theorem signs1497 : ∀ j, Signs p1497 (bank1497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1498 := params 25
abbrev ray1498 := rays 25
def bank1498 : Fin 1 → Cell := oneBank p1498 ray1498
theorem signs1498 : ∀ j, Signs p1498 (bank1498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1499 := params 26
abbrev ray1499 := rays 26
def bank1499 : Fin 1 → Cell := oneBank p1499 ray1499
theorem signs1499 : ∀ j, Signs p1499 (bank1499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1500 := params 27
abbrev ray1500 := rays 27
def bank1500 : Fin 1 → Cell := oneBank p1500 ray1500
theorem signs1500 : ∀ j, Signs p1500 (bank1500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1501 := params 28
abbrev ray1501 := rays 28
def bank1501 : Fin 1 → Cell := oneBank p1501 ray1501
theorem signs1501 : ∀ j, Signs p1501 (bank1501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1502 := params 29
abbrev ray1502 := rays 29
def bank1502 : Fin 1 → Cell := oneBank p1502 ray1502
theorem signs1502 : ∀ j, Signs p1502 (bank1502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1503 := params 30
abbrev ray1503 := rays 30
def bank1503 : Fin 1 → Cell := oneBank p1503 ray1503
theorem signs1503 : ∀ j, Signs p1503 (bank1503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1504 := params 31
abbrev ray1504 := rays 31
def bank1504 : Fin 1 → Cell := oneBank p1504 ray1504
theorem signs1504 : ∀ j, Signs p1504 (bank1504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01473_01504
