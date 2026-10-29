/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01505_01536
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99777074590611,99776907245403,99776739875964,99776572482297,99776405064404,99776237622287,99776070155948,99775902665389,99775735150612,99775567611620,99775400048414,99775232460997,99775064849370,99774897213536,99774729553497,99774561869255,99774394160812,99774226428170,99774058671331,99773890890298,99773723085072,99773555255656,99773387402052,99773219524262,99773051622287,99772883696131,99772715745795,99772547771281,99772379772592,99772211749730,99772043702696,99771875631493,99771707536122]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1504+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(64353766906554075963716/87208120432906879479885:Fraction),(7149787382519271761687/9689596714767625497765:Fraction),(64342405805318384818124/87204620432910379479885:Fraction),(64336726217829529814674/87202870432912129479885:Fraction),(21443682152305248922724/29067040144304626493295:Fraction),(476484205525515055853/645921262466041699851:Fraction),(64319688861596779791176/87197620432917379479885:Fraction),(476400081683466281482/645895336540141699851:Fraction),(64308333019610958600176/87194120432920879479885:Fraction),(12860531212410067082978/17438474086584525895977:Fraction),(7144108770134436300496/9687846714769375497765:Fraction),(21430434283514071540814/29062956810975376493295:Fraction),(12857125319328616098424/17437424086585575895977:Fraction),(7142216821443662529358/9687263381436625497765:Fraction),(64274276016160881070376/87183620432931379479885:Fraction),(347397846971103376730/471253353691530429621:Fraction),(21420975730004583393848/29060040144311626493295:Fraction),(4283816916051666617780/5811891362195775298659:Fraction),(64251580118450967439298/87176620432938379479885:Fraction),(192930653293110959512/261786397696516905345:Fraction),(64240234801723979088212/87173120432941879479885:Fraction),(1736069273172899976718/2355982984674152148105:Fraction),(21409630413361029606184/29056540144315126493295:Fraction),(7135913380377826078016/9685318936994125497765:Fraction),(64217549433777458872976/87166120432948879479885:Fraction),(21403959423742181382218/29054790144316876493295:Fraction),(12841241876611683365398/17432524086590475895977:Fraction),(64200539098372694862539/87160870432954129479885:Fraction),(21398289954832092229358/29053040144318626493295:Fraction),(1833977190899464285048/2490210583798789413711:Fraction),(4278902221711458964618/5810374695530625298659:Fraction),(475391600154075060797/645584225429341699851:Fraction)]
abbrev p1505 := params 0
abbrev ray1505 := rays 0
def bank1505 : Fin 1 → Cell := oneBank p1505 ray1505
theorem signs1505 : ∀ j, Signs p1505 (bank1505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1506 := params 1
abbrev ray1506 := rays 1
def bank1506 : Fin 1 → Cell := oneBank p1506 ray1506
theorem signs1506 : ∀ j, Signs p1506 (bank1506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1507 := params 2
abbrev ray1507 := rays 2
def bank1507 : Fin 1 → Cell := oneBank p1507 ray1507
theorem signs1507 : ∀ j, Signs p1507 (bank1507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1508 := params 3
abbrev ray1508 := rays 3
def bank1508 : Fin 1 → Cell := oneBank p1508 ray1508
theorem signs1508 : ∀ j, Signs p1508 (bank1508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1509 := params 4
abbrev ray1509 := rays 4
def bank1509 : Fin 1 → Cell := oneBank p1509 ray1509
theorem signs1509 : ∀ j, Signs p1509 (bank1509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1510 := params 5
abbrev ray1510 := rays 5
def bank1510 : Fin 1 → Cell := oneBank p1510 ray1510
theorem signs1510 : ∀ j, Signs p1510 (bank1510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1511 := params 6
abbrev ray1511 := rays 6
def bank1511 : Fin 1 → Cell := oneBank p1511 ray1511
theorem signs1511 : ∀ j, Signs p1511 (bank1511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1512 := params 7
abbrev ray1512 := rays 7
def bank1512 : Fin 1 → Cell := oneBank p1512 ray1512
theorem signs1512 : ∀ j, Signs p1512 (bank1512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1513 := params 8
abbrev ray1513 := rays 8
def bank1513 : Fin 1 → Cell := oneBank p1513 ray1513
theorem signs1513 : ∀ j, Signs p1513 (bank1513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1514 := params 9
abbrev ray1514 := rays 9
def bank1514 : Fin 1 → Cell := oneBank p1514 ray1514
theorem signs1514 : ∀ j, Signs p1514 (bank1514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1515 := params 10
abbrev ray1515 := rays 10
def bank1515 : Fin 1 → Cell := oneBank p1515 ray1515
theorem signs1515 : ∀ j, Signs p1515 (bank1515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1516 := params 11
abbrev ray1516 := rays 11
def bank1516 : Fin 1 → Cell := oneBank p1516 ray1516
theorem signs1516 : ∀ j, Signs p1516 (bank1516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1517 := params 12
abbrev ray1517 := rays 12
def bank1517 : Fin 1 → Cell := oneBank p1517 ray1517
theorem signs1517 : ∀ j, Signs p1517 (bank1517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1518 := params 13
abbrev ray1518 := rays 13
def bank1518 : Fin 1 → Cell := oneBank p1518 ray1518
theorem signs1518 : ∀ j, Signs p1518 (bank1518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1519 := params 14
abbrev ray1519 := rays 14
def bank1519 : Fin 1 → Cell := oneBank p1519 ray1519
theorem signs1519 : ∀ j, Signs p1519 (bank1519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1520 := params 15
abbrev ray1520 := rays 15
def bank1520 : Fin 1 → Cell := oneBank p1520 ray1520
theorem signs1520 : ∀ j, Signs p1520 (bank1520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1521 := params 16
abbrev ray1521 := rays 16
def bank1521 : Fin 1 → Cell := oneBank p1521 ray1521
theorem signs1521 : ∀ j, Signs p1521 (bank1521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1522 := params 17
abbrev ray1522 := rays 17
def bank1522 : Fin 1 → Cell := oneBank p1522 ray1522
theorem signs1522 : ∀ j, Signs p1522 (bank1522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1523 := params 18
abbrev ray1523 := rays 18
def bank1523 : Fin 1 → Cell := oneBank p1523 ray1523
theorem signs1523 : ∀ j, Signs p1523 (bank1523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1524 := params 19
abbrev ray1524 := rays 19
def bank1524 : Fin 1 → Cell := oneBank p1524 ray1524
theorem signs1524 : ∀ j, Signs p1524 (bank1524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1525 := params 20
abbrev ray1525 := rays 20
def bank1525 : Fin 1 → Cell := oneBank p1525 ray1525
theorem signs1525 : ∀ j, Signs p1525 (bank1525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1526 := params 21
abbrev ray1526 := rays 21
def bank1526 : Fin 1 → Cell := oneBank p1526 ray1526
theorem signs1526 : ∀ j, Signs p1526 (bank1526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1527 := params 22
abbrev ray1527 := rays 22
def bank1527 : Fin 1 → Cell := oneBank p1527 ray1527
theorem signs1527 : ∀ j, Signs p1527 (bank1527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1528 := params 23
abbrev ray1528 := rays 23
def bank1528 : Fin 1 → Cell := oneBank p1528 ray1528
theorem signs1528 : ∀ j, Signs p1528 (bank1528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1529 := params 24
abbrev ray1529 := rays 24
def bank1529 : Fin 1 → Cell := oneBank p1529 ray1529
theorem signs1529 : ∀ j, Signs p1529 (bank1529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1530 := params 25
abbrev ray1530 := rays 25
def bank1530 : Fin 1 → Cell := oneBank p1530 ray1530
theorem signs1530 : ∀ j, Signs p1530 (bank1530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1531 := params 26
abbrev ray1531 := rays 26
def bank1531 : Fin 1 → Cell := oneBank p1531 ray1531
theorem signs1531 : ∀ j, Signs p1531 (bank1531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1532 := params 27
abbrev ray1532 := rays 27
def bank1532 : Fin 1 → Cell := oneBank p1532 ray1532
theorem signs1532 : ∀ j, Signs p1532 (bank1532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1533 := params 28
abbrev ray1533 := rays 28
def bank1533 : Fin 1 → Cell := oneBank p1533 ray1533
theorem signs1533 : ∀ j, Signs p1533 (bank1533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1534 := params 29
abbrev ray1534 := rays 29
def bank1534 : Fin 1 → Cell := oneBank p1534 ray1534
theorem signs1534 : ∀ j, Signs p1534 (bank1534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1535 := params 30
abbrev ray1535 := rays 30
def bank1535 : Fin 1 → Cell := oneBank p1535 ray1535
theorem signs1535 : ∀ j, Signs p1535 (bank1535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1536 := params 31
abbrev ray1536 := rays 31
def bank1536 : Fin 1 → Cell := oneBank p1536 ray1536
theorem signs1536 : ∀ j, Signs p1536 (bank1536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01505_01536
