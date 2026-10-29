/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01537_01568
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99771707536122,99771539416586,99771371272887,99771203105027,99771034913009,99770866696834,99770698456504,99770530192022,99770361903389,99770193590608,99770025253681,99769856892610,99769688507396,99769520098043,99769351664552,99769183206925,99769014725164,99768846219272,99768677689250,99768509135101,99768340556827,99768171954430,99768003327911,99767834677273,99767666002518,99767497303649,99767328580666,99767159833573,99766991062371,99766822267063,99766653447651,99766484604136,99766315736521]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1536+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(12834439708636463864924/17430424086592575895977:Fraction),(475307636243183031868/645558299503441699851:Fraction),(7128985057475294483381/9683180048107375497765:Fraction),(64155198745290436578316/87146870432968129479885:Fraction),(12829906604883696034016/17429024086593975895977:Fraction),(21381289451570914162484/29047790144323876493295:Fraction),(21379401170802273199148/29047206810991126493295:Fraction),(38518041874681318912/52336258518303381069:Fraction),(1017886916789365529182/1383144768777410785395:Fraction),(21373737207191656269128/29045456810992876493295:Fraction),(9159364076680527604259/12447802918997197068555:Fraction),(1424664144518849881972/1936286009621825099553:Fraction),(754167344676203635034/1025072005093927993881:Fraction),(64098561919163231070323/87129370432985629479885:Fraction),(1017347628449924362712/1382978102110910785395:Fraction),(1831064009059295736190/2489310583799689413711:Fraction),(339055978145224874704/460974182185136928465:Fraction),(21358640157814996586762/29040790144330876493295:Fraction),(12814052181026542088840/17424124086598875895977:Fraction),(1123940371307401714483/1528401235666598762805:Fraction),(7117660275070736899733/9679680048110875497765:Fraction),(12810656967705784946672/17423074086599925895977:Fraction),(64047627029207819385643/87113620433001379479885:Fraction),(338846397077695996948/460909367370386928465:Fraction),(64036312118039005151648/87110120433004879479885:Fraction),(64030656240324301609471/87108370433006629479885:Fraction),(1016269844293532307104/1382644768777910785395:Fraction),(12803868793711205004409/17420974086602025895977:Fraction),(21337896266216466720253/29034373477670626493295:Fraction),(21336011152228727445553/29033790144337876493295:Fraction),(21334126388943335352776/29033206811005126493295:Fraction),(21332241976377250928108/29032623477672376493295:Fraction)]
abbrev p1537 := params 0
abbrev ray1537 := rays 0
def bank1537 : Fin 1 → Cell := oneBank p1537 ray1537
theorem signs1537 : ∀ j, Signs p1537 (bank1537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1538 := params 1
abbrev ray1538 := rays 1
def bank1538 : Fin 1 → Cell := oneBank p1538 ray1538
theorem signs1538 : ∀ j, Signs p1538 (bank1538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1539 := params 2
abbrev ray1539 := rays 2
def bank1539 : Fin 1 → Cell := oneBank p1539 ray1539
theorem signs1539 : ∀ j, Signs p1539 (bank1539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1540 := params 3
abbrev ray1540 := rays 3
def bank1540 : Fin 1 → Cell := oneBank p1540 ray1540
theorem signs1540 : ∀ j, Signs p1540 (bank1540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1541 := params 4
abbrev ray1541 := rays 4
def bank1541 : Fin 1 → Cell := oneBank p1541 ray1541
theorem signs1541 : ∀ j, Signs p1541 (bank1541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1542 := params 5
abbrev ray1542 := rays 5
def bank1542 : Fin 1 → Cell := oneBank p1542 ray1542
theorem signs1542 : ∀ j, Signs p1542 (bank1542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1543 := params 6
abbrev ray1543 := rays 6
def bank1543 : Fin 1 → Cell := oneBank p1543 ray1543
theorem signs1543 : ∀ j, Signs p1543 (bank1543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1544 := params 7
abbrev ray1544 := rays 7
def bank1544 : Fin 1 → Cell := oneBank p1544 ray1544
theorem signs1544 : ∀ j, Signs p1544 (bank1544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1545 := params 8
abbrev ray1545 := rays 8
def bank1545 : Fin 1 → Cell := oneBank p1545 ray1545
theorem signs1545 : ∀ j, Signs p1545 (bank1545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1546 := params 9
abbrev ray1546 := rays 9
def bank1546 : Fin 1 → Cell := oneBank p1546 ray1546
theorem signs1546 : ∀ j, Signs p1546 (bank1546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1547 := params 10
abbrev ray1547 := rays 10
def bank1547 : Fin 1 → Cell := oneBank p1547 ray1547
theorem signs1547 : ∀ j, Signs p1547 (bank1547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1548 := params 11
abbrev ray1548 := rays 11
def bank1548 : Fin 1 → Cell := oneBank p1548 ray1548
theorem signs1548 : ∀ j, Signs p1548 (bank1548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1549 := params 12
abbrev ray1549 := rays 12
def bank1549 : Fin 1 → Cell := oneBank p1549 ray1549
theorem signs1549 : ∀ j, Signs p1549 (bank1549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1550 := params 13
abbrev ray1550 := rays 13
def bank1550 : Fin 1 → Cell := oneBank p1550 ray1550
theorem signs1550 : ∀ j, Signs p1550 (bank1550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1551 := params 14
abbrev ray1551 := rays 14
def bank1551 : Fin 1 → Cell := oneBank p1551 ray1551
theorem signs1551 : ∀ j, Signs p1551 (bank1551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1552 := params 15
abbrev ray1552 := rays 15
def bank1552 : Fin 1 → Cell := oneBank p1552 ray1552
theorem signs1552 : ∀ j, Signs p1552 (bank1552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1553 := params 16
abbrev ray1553 := rays 16
def bank1553 : Fin 1 → Cell := oneBank p1553 ray1553
theorem signs1553 : ∀ j, Signs p1553 (bank1553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1554 := params 17
abbrev ray1554 := rays 17
def bank1554 : Fin 1 → Cell := oneBank p1554 ray1554
theorem signs1554 : ∀ j, Signs p1554 (bank1554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1555 := params 18
abbrev ray1555 := rays 18
def bank1555 : Fin 1 → Cell := oneBank p1555 ray1555
theorem signs1555 : ∀ j, Signs p1555 (bank1555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1556 := params 19
abbrev ray1556 := rays 19
def bank1556 : Fin 1 → Cell := oneBank p1556 ray1556
theorem signs1556 : ∀ j, Signs p1556 (bank1556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1557 := params 20
abbrev ray1557 := rays 20
def bank1557 : Fin 1 → Cell := oneBank p1557 ray1557
theorem signs1557 : ∀ j, Signs p1557 (bank1557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1558 := params 21
abbrev ray1558 := rays 21
def bank1558 : Fin 1 → Cell := oneBank p1558 ray1558
theorem signs1558 : ∀ j, Signs p1558 (bank1558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1559 := params 22
abbrev ray1559 := rays 22
def bank1559 : Fin 1 → Cell := oneBank p1559 ray1559
theorem signs1559 : ∀ j, Signs p1559 (bank1559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1560 := params 23
abbrev ray1560 := rays 23
def bank1560 : Fin 1 → Cell := oneBank p1560 ray1560
theorem signs1560 : ∀ j, Signs p1560 (bank1560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1561 := params 24
abbrev ray1561 := rays 24
def bank1561 : Fin 1 → Cell := oneBank p1561 ray1561
theorem signs1561 : ∀ j, Signs p1561 (bank1561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1562 := params 25
abbrev ray1562 := rays 25
def bank1562 : Fin 1 → Cell := oneBank p1562 ray1562
theorem signs1562 : ∀ j, Signs p1562 (bank1562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1563 := params 26
abbrev ray1563 := rays 26
def bank1563 : Fin 1 → Cell := oneBank p1563 ray1563
theorem signs1563 : ∀ j, Signs p1563 (bank1563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1564 := params 27
abbrev ray1564 := rays 27
def bank1564 : Fin 1 → Cell := oneBank p1564 ray1564
theorem signs1564 : ∀ j, Signs p1564 (bank1564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1565 := params 28
abbrev ray1565 := rays 28
def bank1565 : Fin 1 → Cell := oneBank p1565 ray1565
theorem signs1565 : ∀ j, Signs p1565 (bank1565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1566 := params 29
abbrev ray1566 := rays 29
def bank1566 : Fin 1 → Cell := oneBank p1566 ray1566
theorem signs1566 : ∀ j, Signs p1566 (bank1566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1567 := params 30
abbrev ray1567 := rays 30
def bank1567 : Fin 1 → Cell := oneBank p1567 ray1567
theorem signs1567 : ∀ j, Signs p1567 (bank1567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1568 := params 31
abbrev ray1568 := rays 31
def bank1568 : Fin 1 → Cell := oneBank p1568 ray1568
theorem signs1568 : ∀ j, Signs p1568 (bank1568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01537_01568
