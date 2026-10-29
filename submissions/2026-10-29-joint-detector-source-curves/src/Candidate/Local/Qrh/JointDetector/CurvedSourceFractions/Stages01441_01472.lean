/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01441_01472
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99787734187274,99787568397245,99787402582849,99787236744088,99787070880964,99786904993479,99786739081635,99786573145435,99786407184881,99786241199975,99786075190719,99785909157115,99785743099165,99785577016872,99785410910238,99785244779264,99785078623953,99784912444308,99784746240330,99784580012021,99784413759384,99784247482421,99784081181133,99783914855523,99783748505593,99783582131346,99783415732783,99783249309906,99783082862718,99782916391221,99782749895417,99782583375308,99782416830896]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1440+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(64718230248822320180236/87320120432794879479885:Fraction),(12942504361301926293718/17463674086559325895977:Fraction),(21568938137193168403558/29105540144266126493295:Fraction),(116578570885857749468/157324090869910143207:Fraction),(12939080063836374678674/17462624086560375895977:Fraction),(116558006525699175604/157317784563610143207:Fraction),(479140642588184268455/646737929131891699851:Fraction),(1437295131657958529723/1940174898506825099553:Fraction),(3079646483210722653098/4157434306324232356185:Fraction),(12933374239078199677525/17460874086562125895977:Fraction),(1959429274803512515036/2645533952509466044845:Fraction),(1436788071375577866497/1940019342951425099553:Fraction),(12929951791592491559947/17459824086563175895977:Fraction),(64644055751816477708476/87297370432817629479885:Fraction),(7182039288168378303616/9699513381424375497765:Fraction),(64632651260509030608052/87293870432821129479885:Fraction),(64626948752808766612444/87292120432822879479885:Fraction),(341911361338917877378/461853811813886928465:Fraction),(12923109376260077070956/17457724086565275895977:Fraction),(64609846294938335473853/87286870432828129479885:Fraction),(4306943035598715538514/5819008028855325298659:Fraction),(64598445821123363166368/87283370432831629479885:Fraction),(64592747156417431556426/87281620432833379479885:Fraction),(7176338701911428038492/9697763381426125497765:Fraction),(1845181408671140368210/2493660583795339413711:Fraction),(12915130267606305651692/17455274086567725895977:Fraction),(7174439380097654628317/9697180048093375497765:Fraction),(64564257329314771293532/87272870432842129479885:Fraction),(64558560063350556647704/87271120432843879479885:Fraction),(87827025640536144578/118733837323599495891:Fraction),(64547168676697589557876/87267620432847379479885:Fraction),(64541473333287866312708/87265870432849129479885:Fraction)]
abbrev p1441 := params 0
abbrev ray1441 := rays 0
def bank1441 : Fin 1 → Cell := oneBank p1441 ray1441
theorem signs1441 : ∀ j, Signs p1441 (bank1441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1442 := params 1
abbrev ray1442 := rays 1
def bank1442 : Fin 1 → Cell := oneBank p1442 ray1442
theorem signs1442 : ∀ j, Signs p1442 (bank1442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1443 := params 2
abbrev ray1443 := rays 2
def bank1443 : Fin 1 → Cell := oneBank p1443 ray1443
theorem signs1443 : ∀ j, Signs p1443 (bank1443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1444 := params 3
abbrev ray1444 := rays 3
def bank1444 : Fin 1 → Cell := oneBank p1444 ray1444
theorem signs1444 : ∀ j, Signs p1444 (bank1444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1445 := params 4
abbrev ray1445 := rays 4
def bank1445 : Fin 1 → Cell := oneBank p1445 ray1445
theorem signs1445 : ∀ j, Signs p1445 (bank1445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1446 := params 5
abbrev ray1446 := rays 5
def bank1446 : Fin 1 → Cell := oneBank p1446 ray1446
theorem signs1446 : ∀ j, Signs p1446 (bank1446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1447 := params 6
abbrev ray1447 := rays 6
def bank1447 : Fin 1 → Cell := oneBank p1447 ray1447
theorem signs1447 : ∀ j, Signs p1447 (bank1447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1448 := params 7
abbrev ray1448 := rays 7
def bank1448 : Fin 1 → Cell := oneBank p1448 ray1448
theorem signs1448 : ∀ j, Signs p1448 (bank1448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1449 := params 8
abbrev ray1449 := rays 8
def bank1449 : Fin 1 → Cell := oneBank p1449 ray1449
theorem signs1449 : ∀ j, Signs p1449 (bank1449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1450 := params 9
abbrev ray1450 := rays 9
def bank1450 : Fin 1 → Cell := oneBank p1450 ray1450
theorem signs1450 : ∀ j, Signs p1450 (bank1450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1451 := params 10
abbrev ray1451 := rays 10
def bank1451 : Fin 1 → Cell := oneBank p1451 ray1451
theorem signs1451 : ∀ j, Signs p1451 (bank1451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1452 := params 11
abbrev ray1452 := rays 11
def bank1452 : Fin 1 → Cell := oneBank p1452 ray1452
theorem signs1452 : ∀ j, Signs p1452 (bank1452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1453 := params 12
abbrev ray1453 := rays 12
def bank1453 : Fin 1 → Cell := oneBank p1453 ray1453
theorem signs1453 : ∀ j, Signs p1453 (bank1453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1454 := params 13
abbrev ray1454 := rays 13
def bank1454 : Fin 1 → Cell := oneBank p1454 ray1454
theorem signs1454 : ∀ j, Signs p1454 (bank1454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1455 := params 14
abbrev ray1455 := rays 14
def bank1455 : Fin 1 → Cell := oneBank p1455 ray1455
theorem signs1455 : ∀ j, Signs p1455 (bank1455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1456 := params 15
abbrev ray1456 := rays 15
def bank1456 : Fin 1 → Cell := oneBank p1456 ray1456
theorem signs1456 : ∀ j, Signs p1456 (bank1456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1457 := params 16
abbrev ray1457 := rays 16
def bank1457 : Fin 1 → Cell := oneBank p1457 ray1457
theorem signs1457 : ∀ j, Signs p1457 (bank1457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1458 := params 17
abbrev ray1458 := rays 17
def bank1458 : Fin 1 → Cell := oneBank p1458 ray1458
theorem signs1458 : ∀ j, Signs p1458 (bank1458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1459 := params 18
abbrev ray1459 := rays 18
def bank1459 : Fin 1 → Cell := oneBank p1459 ray1459
theorem signs1459 : ∀ j, Signs p1459 (bank1459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1460 := params 19
abbrev ray1460 := rays 19
def bank1460 : Fin 1 → Cell := oneBank p1460 ray1460
theorem signs1460 : ∀ j, Signs p1460 (bank1460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1461 := params 20
abbrev ray1461 := rays 20
def bank1461 : Fin 1 → Cell := oneBank p1461 ray1461
theorem signs1461 : ∀ j, Signs p1461 (bank1461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1462 := params 21
abbrev ray1462 := rays 21
def bank1462 : Fin 1 → Cell := oneBank p1462 ray1462
theorem signs1462 : ∀ j, Signs p1462 (bank1462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1463 := params 22
abbrev ray1463 := rays 22
def bank1463 : Fin 1 → Cell := oneBank p1463 ray1463
theorem signs1463 : ∀ j, Signs p1463 (bank1463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1464 := params 23
abbrev ray1464 := rays 23
def bank1464 : Fin 1 → Cell := oneBank p1464 ray1464
theorem signs1464 : ∀ j, Signs p1464 (bank1464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1465 := params 24
abbrev ray1465 := rays 24
def bank1465 : Fin 1 → Cell := oneBank p1465 ray1465
theorem signs1465 : ∀ j, Signs p1465 (bank1465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1466 := params 25
abbrev ray1466 := rays 25
def bank1466 : Fin 1 → Cell := oneBank p1466 ray1466
theorem signs1466 : ∀ j, Signs p1466 (bank1466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1467 := params 26
abbrev ray1467 := rays 26
def bank1467 : Fin 1 → Cell := oneBank p1467 ray1467
theorem signs1467 : ∀ j, Signs p1467 (bank1467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1468 := params 27
abbrev ray1468 := rays 27
def bank1468 : Fin 1 → Cell := oneBank p1468 ray1468
theorem signs1468 : ∀ j, Signs p1468 (bank1468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1469 := params 28
abbrev ray1469 := rays 28
def bank1469 : Fin 1 → Cell := oneBank p1469 ray1469
theorem signs1469 : ∀ j, Signs p1469 (bank1469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1470 := params 29
abbrev ray1470 := rays 29
def bank1470 : Fin 1 → Cell := oneBank p1470 ray1470
theorem signs1470 : ∀ j, Signs p1470 (bank1470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1471 := params 30
abbrev ray1471 := rays 30
def bank1471 : Fin 1 → Cell := oneBank p1471 ray1471
theorem signs1471 : ∀ j, Signs p1471 (bank1471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1472 := params 31
abbrev ray1472 := rays 31
def bank1472 : Fin 1 → Cell := oneBank p1472 ray1472
theorem signs1472 : ∀ j, Signs p1472 (bank1472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01441_01472
