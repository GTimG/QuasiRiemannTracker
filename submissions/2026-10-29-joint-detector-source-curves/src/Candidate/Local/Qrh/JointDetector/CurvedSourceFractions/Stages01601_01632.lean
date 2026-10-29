/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01601_01632
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99760899260319,99760729598559,99760559912769,99760390202951,99760220469108,99760050711241,99759880929353,99759711123445,99759541293520,99759371439580,99759201561626,99759031659661,99758861733687,99758691783705,99758521809718,99758351811728,99758181789737,99758011743748,99757841673762,99757671579781,99757501461807,99757331319842,99757161153889,99756990963949,99756820750025,99756650512118,99756480250231,99756309964366,99756139654524,99755969320708,99755798962919,99755628581160,99755458175433]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1600+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(472669545366123947530/644741632837591699851:Fraction),(7089416571477666230992/9670930048119625497765:Fraction),(157528668433698048369/214905235637230566617:Fraction),(63793472116855249663918/87034870433080129479885:Fraction),(21262611523872063116372/29011040144360626493295:Fraction),(63782196855283933893026/87031370433083629479885:Fraction),(12755311793573925642902/17405924086617075895977:Fraction),(1417131630196281906296/1933952676290825099553:Fraction),(12753057270810073019074/17405224086617775895977:Fraction),(12751930080599420477122/17404874086618125895977:Fraction),(21251338501907882742008/29007540144364126493295:Fraction),(9106911491071710874933/12431552919013447068555:Fraction),(63742746423137018533693/87019120433095879479885:Fraction),(1416380271952682087003/1933719342957725099553:Fraction),(12746295576342826656560/17403124086619875895977:Fraction),(1158651741897286171706/1582070371510929626907:Fraction),(786669288041015910148/1074223709050652833085:Fraction),(21238193304109067189644/29003456811034876493295:Fraction),(12741789709483240795036/17401724086621275895977:Fraction),(21234439003916237550092/29002290144369376493295:Fraction),(21232561768444918605113/29001706811036626493295:Fraction),(2769219767526287536316/3782755236222244759995:Fraction),(573751577073073721248/783798382280300716035:Fraction),(12736159057291414005595/17399974086623025895977:Fraction),(4245011104807694540875/5799874695541125298659:Fraction),(21223179229053658595728/28998790144372876493295:Fraction),(63663908631604852898867/86994620433120379479885:Fraction),(63658280630460870759152/86992870433122129479885:Fraction),(7072517075975525007188/9665680048124875497765:Fraction),(9092432366654662807036/12427052919017947068555:Fraction),(12728279855775707036854/17397524086625475895977:Fraction),(606054981387981034294/828436861267896471237:Fraction)]
abbrev p1601 := params 0
abbrev ray1601 := rays 0
def bank1601 : Fin 1 → Cell := oneBank p1601 ray1601
theorem signs1601 : ∀ j, Signs p1601 (bank1601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1602 := params 1
abbrev ray1602 := rays 1
def bank1602 : Fin 1 → Cell := oneBank p1602 ray1602
theorem signs1602 : ∀ j, Signs p1602 (bank1602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1603 := params 2
abbrev ray1603 := rays 2
def bank1603 : Fin 1 → Cell := oneBank p1603 ray1603
theorem signs1603 : ∀ j, Signs p1603 (bank1603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1604 := params 3
abbrev ray1604 := rays 3
def bank1604 : Fin 1 → Cell := oneBank p1604 ray1604
theorem signs1604 : ∀ j, Signs p1604 (bank1604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1605 := params 4
abbrev ray1605 := rays 4
def bank1605 : Fin 1 → Cell := oneBank p1605 ray1605
theorem signs1605 : ∀ j, Signs p1605 (bank1605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1606 := params 5
abbrev ray1606 := rays 5
def bank1606 : Fin 1 → Cell := oneBank p1606 ray1606
theorem signs1606 : ∀ j, Signs p1606 (bank1606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1607 := params 6
abbrev ray1607 := rays 6
def bank1607 : Fin 1 → Cell := oneBank p1607 ray1607
theorem signs1607 : ∀ j, Signs p1607 (bank1607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1608 := params 7
abbrev ray1608 := rays 7
def bank1608 : Fin 1 → Cell := oneBank p1608 ray1608
theorem signs1608 : ∀ j, Signs p1608 (bank1608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1609 := params 8
abbrev ray1609 := rays 8
def bank1609 : Fin 1 → Cell := oneBank p1609 ray1609
theorem signs1609 : ∀ j, Signs p1609 (bank1609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1610 := params 9
abbrev ray1610 := rays 9
def bank1610 : Fin 1 → Cell := oneBank p1610 ray1610
theorem signs1610 : ∀ j, Signs p1610 (bank1610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1611 := params 10
abbrev ray1611 := rays 10
def bank1611 : Fin 1 → Cell := oneBank p1611 ray1611
theorem signs1611 : ∀ j, Signs p1611 (bank1611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1612 := params 11
abbrev ray1612 := rays 11
def bank1612 : Fin 1 → Cell := oneBank p1612 ray1612
theorem signs1612 : ∀ j, Signs p1612 (bank1612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1613 := params 12
abbrev ray1613 := rays 12
def bank1613 : Fin 1 → Cell := oneBank p1613 ray1613
theorem signs1613 : ∀ j, Signs p1613 (bank1613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1614 := params 13
abbrev ray1614 := rays 13
def bank1614 : Fin 1 → Cell := oneBank p1614 ray1614
theorem signs1614 : ∀ j, Signs p1614 (bank1614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1615 := params 14
abbrev ray1615 := rays 14
def bank1615 : Fin 1 → Cell := oneBank p1615 ray1615
theorem signs1615 : ∀ j, Signs p1615 (bank1615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1616 := params 15
abbrev ray1616 := rays 15
def bank1616 : Fin 1 → Cell := oneBank p1616 ray1616
theorem signs1616 : ∀ j, Signs p1616 (bank1616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1617 := params 16
abbrev ray1617 := rays 16
def bank1617 : Fin 1 → Cell := oneBank p1617 ray1617
theorem signs1617 : ∀ j, Signs p1617 (bank1617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1618 := params 17
abbrev ray1618 := rays 17
def bank1618 : Fin 1 → Cell := oneBank p1618 ray1618
theorem signs1618 : ∀ j, Signs p1618 (bank1618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1619 := params 18
abbrev ray1619 := rays 18
def bank1619 : Fin 1 → Cell := oneBank p1619 ray1619
theorem signs1619 : ∀ j, Signs p1619 (bank1619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1620 := params 19
abbrev ray1620 := rays 19
def bank1620 : Fin 1 → Cell := oneBank p1620 ray1620
theorem signs1620 : ∀ j, Signs p1620 (bank1620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1621 := params 20
abbrev ray1621 := rays 20
def bank1621 : Fin 1 → Cell := oneBank p1621 ray1621
theorem signs1621 : ∀ j, Signs p1621 (bank1621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1622 := params 21
abbrev ray1622 := rays 21
def bank1622 : Fin 1 → Cell := oneBank p1622 ray1622
theorem signs1622 : ∀ j, Signs p1622 (bank1622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1623 := params 22
abbrev ray1623 := rays 22
def bank1623 : Fin 1 → Cell := oneBank p1623 ray1623
theorem signs1623 : ∀ j, Signs p1623 (bank1623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1624 := params 23
abbrev ray1624 := rays 23
def bank1624 : Fin 1 → Cell := oneBank p1624 ray1624
theorem signs1624 : ∀ j, Signs p1624 (bank1624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1625 := params 24
abbrev ray1625 := rays 24
def bank1625 : Fin 1 → Cell := oneBank p1625 ray1625
theorem signs1625 : ∀ j, Signs p1625 (bank1625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1626 := params 25
abbrev ray1626 := rays 25
def bank1626 : Fin 1 → Cell := oneBank p1626 ray1626
theorem signs1626 : ∀ j, Signs p1626 (bank1626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1627 := params 26
abbrev ray1627 := rays 26
def bank1627 : Fin 1 → Cell := oneBank p1627 ray1627
theorem signs1627 : ∀ j, Signs p1627 (bank1627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1628 := params 27
abbrev ray1628 := rays 27
def bank1628 : Fin 1 → Cell := oneBank p1628 ray1628
theorem signs1628 : ∀ j, Signs p1628 (bank1628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1629 := params 28
abbrev ray1629 := rays 28
def bank1629 : Fin 1 → Cell := oneBank p1629 ray1629
theorem signs1629 : ∀ j, Signs p1629 (bank1629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1630 := params 29
abbrev ray1630 := rays 29
def bank1630 : Fin 1 → Cell := oneBank p1630 ray1630
theorem signs1630 : ∀ j, Signs p1630 (bank1630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1631 := params 30
abbrev ray1631 := rays 30
def bank1631 : Fin 1 → Cell := oneBank p1631 ray1631
theorem signs1631 : ∀ j, Signs p1631 (bank1631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1632 := params 31
abbrev ray1632 := rays 31
def bank1632 : Fin 1 → Cell := oneBank p1632 ray1632
theorem signs1632 : ∀ j, Signs p1632 (bank1632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01601_01632
