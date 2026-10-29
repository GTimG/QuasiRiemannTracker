/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01569_01600
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99766315736521,99766146844807,99765977928998,99765808989094,99765640025098,99765471037013,99765302024840,99765132988581,99764963928238,99764794843814,99764625735311,99764456602730,99764287446073,99764118265344,99763949060543,99763779831673,99763610578736,99763441301734,99763272000669,99763102675543,99762933326359,99762763953118,99762594555823,99762425134475,99762255689077,99762086219630,99761916726137,99761747208599,99761577667019,99761408101399,99761238511741,99761068898047,99760899260319]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1568+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4270341843140678724/5812220249117042341:Fraction),(21328472979277657924274/29031456811006876493295:Fraction),(63979766408463099478304/87092620433022379479885:Fraction),(1421646971270665239680/1935352676289425099553:Fraction),(63968462058231923132704/87089120433025879479885:Fraction),(63962811461672119068671/87087370433027629479885:Fraction),(609115816126535669908/829386861266946471237:Fraction),(12790301950616880756761/17416774086606225895977:Fraction),(12789171973073946530312/17416424086606575895977:Fraction),(67661597678188666592/92148540140777385693:Fraction),(63934560798971108222306/87078620433036379479885:Fraction),(12785782324066829738212/17415374086607625895977:Fraction),(546352679438772110491/744231798572990422905:Fraction),(63917616421031800697348/87073370433041629479885:Fraction),(63911967951716828077282/87071620433043379479885:Fraction),(21302107253177593042468/29023290144348376493295:Fraction),(7100075043973798128188/9674235603671875497765:Fraction),(63895028860421125329664/87066370433048629479885:Fraction),(21296461125982065589043/29021540144350126493295:Fraction),(63883737723944862422198/87062870433052129479885:Fraction),(21292697707629564505606/29020373477684626493295:Fraction),(7096938705594907347536/9673263381450625497765:Fraction),(4257786975389382254201/5803841362203825298659:Fraction),(12772232147979396352880/17411174086611825895977:Fraction),(608147789543335655770/829086861267246471237:Fraction),(982305767581864867936/1339267237431732761229:Fraction),(21281410978921703871623/29016873477688126493295:Fraction),(2364392252199064405142/3224032238261708499255:Fraction),(3039664273106342230274/4145100973003232356185:Fraction),(63827308489806474522034/87045370433069629479885:Fraction),(7091296477522718881513/9671513381452375497765:Fraction),(3753883996139135839228/5120110025474889969405:Fraction)]
abbrev p1569 := params 0
abbrev ray1569 := rays 0
def bank1569 : Fin 1 → Cell := oneBank p1569 ray1569
theorem signs1569 : ∀ j, Signs p1569 (bank1569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1570 := params 1
abbrev ray1570 := rays 1
def bank1570 : Fin 1 → Cell := oneBank p1570 ray1570
theorem signs1570 : ∀ j, Signs p1570 (bank1570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1571 := params 2
abbrev ray1571 := rays 2
def bank1571 : Fin 1 → Cell := oneBank p1571 ray1571
theorem signs1571 : ∀ j, Signs p1571 (bank1571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1572 := params 3
abbrev ray1572 := rays 3
def bank1572 : Fin 1 → Cell := oneBank p1572 ray1572
theorem signs1572 : ∀ j, Signs p1572 (bank1572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1573 := params 4
abbrev ray1573 := rays 4
def bank1573 : Fin 1 → Cell := oneBank p1573 ray1573
theorem signs1573 : ∀ j, Signs p1573 (bank1573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1574 := params 5
abbrev ray1574 := rays 5
def bank1574 : Fin 1 → Cell := oneBank p1574 ray1574
theorem signs1574 : ∀ j, Signs p1574 (bank1574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1575 := params 6
abbrev ray1575 := rays 6
def bank1575 : Fin 1 → Cell := oneBank p1575 ray1575
theorem signs1575 : ∀ j, Signs p1575 (bank1575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1576 := params 7
abbrev ray1576 := rays 7
def bank1576 : Fin 1 → Cell := oneBank p1576 ray1576
theorem signs1576 : ∀ j, Signs p1576 (bank1576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1577 := params 8
abbrev ray1577 := rays 8
def bank1577 : Fin 1 → Cell := oneBank p1577 ray1577
theorem signs1577 : ∀ j, Signs p1577 (bank1577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1578 := params 9
abbrev ray1578 := rays 9
def bank1578 : Fin 1 → Cell := oneBank p1578 ray1578
theorem signs1578 : ∀ j, Signs p1578 (bank1578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1579 := params 10
abbrev ray1579 := rays 10
def bank1579 : Fin 1 → Cell := oneBank p1579 ray1579
theorem signs1579 : ∀ j, Signs p1579 (bank1579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1580 := params 11
abbrev ray1580 := rays 11
def bank1580 : Fin 1 → Cell := oneBank p1580 ray1580
theorem signs1580 : ∀ j, Signs p1580 (bank1580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1581 := params 12
abbrev ray1581 := rays 12
def bank1581 : Fin 1 → Cell := oneBank p1581 ray1581
theorem signs1581 : ∀ j, Signs p1581 (bank1581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1582 := params 13
abbrev ray1582 := rays 13
def bank1582 : Fin 1 → Cell := oneBank p1582 ray1582
theorem signs1582 : ∀ j, Signs p1582 (bank1582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1583 := params 14
abbrev ray1583 := rays 14
def bank1583 : Fin 1 → Cell := oneBank p1583 ray1583
theorem signs1583 : ∀ j, Signs p1583 (bank1583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1584 := params 15
abbrev ray1584 := rays 15
def bank1584 : Fin 1 → Cell := oneBank p1584 ray1584
theorem signs1584 : ∀ j, Signs p1584 (bank1584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1585 := params 16
abbrev ray1585 := rays 16
def bank1585 : Fin 1 → Cell := oneBank p1585 ray1585
theorem signs1585 : ∀ j, Signs p1585 (bank1585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1586 := params 17
abbrev ray1586 := rays 17
def bank1586 : Fin 1 → Cell := oneBank p1586 ray1586
theorem signs1586 : ∀ j, Signs p1586 (bank1586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1587 := params 18
abbrev ray1587 := rays 18
def bank1587 : Fin 1 → Cell := oneBank p1587 ray1587
theorem signs1587 : ∀ j, Signs p1587 (bank1587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1588 := params 19
abbrev ray1588 := rays 19
def bank1588 : Fin 1 → Cell := oneBank p1588 ray1588
theorem signs1588 : ∀ j, Signs p1588 (bank1588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1589 := params 20
abbrev ray1589 := rays 20
def bank1589 : Fin 1 → Cell := oneBank p1589 ray1589
theorem signs1589 : ∀ j, Signs p1589 (bank1589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1590 := params 21
abbrev ray1590 := rays 21
def bank1590 : Fin 1 → Cell := oneBank p1590 ray1590
theorem signs1590 : ∀ j, Signs p1590 (bank1590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1591 := params 22
abbrev ray1591 := rays 22
def bank1591 : Fin 1 → Cell := oneBank p1591 ray1591
theorem signs1591 : ∀ j, Signs p1591 (bank1591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1592 := params 23
abbrev ray1592 := rays 23
def bank1592 : Fin 1 → Cell := oneBank p1592 ray1592
theorem signs1592 : ∀ j, Signs p1592 (bank1592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1593 := params 24
abbrev ray1593 := rays 24
def bank1593 : Fin 1 → Cell := oneBank p1593 ray1593
theorem signs1593 : ∀ j, Signs p1593 (bank1593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1594 := params 25
abbrev ray1594 := rays 25
def bank1594 : Fin 1 → Cell := oneBank p1594 ray1594
theorem signs1594 : ∀ j, Signs p1594 (bank1594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1595 := params 26
abbrev ray1595 := rays 26
def bank1595 : Fin 1 → Cell := oneBank p1595 ray1595
theorem signs1595 : ∀ j, Signs p1595 (bank1595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1596 := params 27
abbrev ray1596 := rays 27
def bank1596 : Fin 1 → Cell := oneBank p1596 ray1596
theorem signs1596 : ∀ j, Signs p1596 (bank1596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1597 := params 28
abbrev ray1597 := rays 28
def bank1597 : Fin 1 → Cell := oneBank p1597 ray1597
theorem signs1597 : ∀ j, Signs p1597 (bank1597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1598 := params 29
abbrev ray1598 := rays 29
def bank1598 : Fin 1 → Cell := oneBank p1598 ray1598
theorem signs1598 : ∀ j, Signs p1598 (bank1598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1599 := params 30
abbrev ray1599 := rays 30
def bank1599 : Fin 1 → Cell := oneBank p1599 ray1599
theorem signs1599 : ∀ j, Signs p1599 (bank1599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1600 := params 31
abbrev ray1600 := rays 31
def bank1600 : Fin 1 → Cell := oneBank p1600 ray1600
theorem signs1600 : ∀ j, Signs p1600 (bank1600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01569_01600
