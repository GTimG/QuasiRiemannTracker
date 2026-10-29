/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01697_01728
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99744502448428,99744330489136,99744158506011,99743986499053,99743814468265,99743642413649,99743470335207,99743298232941,99743126106852,99742953956943,99742781783216,99742609585673,99742437364316,99742265119146,99742092850166,99741920557378,99741748240784,99741575900386,99741403536186,99741231148186,99741058736388,99740886300793,99740713841404,99740541358223,99740368851252,99740196320494,99740023765949,99739851187620,99739678585509,99739505959618,99739333309949,99739160636503,99738987939283]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1696+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(12654198731467831517758/17374424086648575895977:Fraction),(781054264708140817804/1072473709052402833085:Fraction),(9037114040351843673032/12409802919035197068555:Fraction),(21084733651564680799034/28955623477749376493295:Fraction),(4216573645605513175405/5791008028883325298659:Fraction),(63243008244647644635424/86863370433251629479885:Fraction),(63237412862445451030676/86861620433253379479885:Fraction),(21077272845842556430457/28953290144418376493295:Fraction),(9032317545399411287378/12408302919036697068555:Fraction),(1708665658959037368923/2347469471169152148105:Fraction),(7023892864053550294034/9650513381473375497765:Fraction),(37513021960117789885/51544730227455269721:Fraction),(12640769857314763624196/17370224086652775895977:Fraction),(1404405697815879294068/1929986009628125099553:Fraction),(780156352770239955696/1072192844855152833085:Fraction),(63187072578478323704636/86845870433269129479885:Fraction),(780018291854032316076/1072149634978652833085:Fraction),(63175890533336450721716/86842370433272629479885:Fraction),(5742754589470997138924/7894601857570398134535:Fraction),(779811237858451076652/1072084820163902833085:Fraction),(21053040368882686068476/28945706811092626493295:Fraction),(12630706355663410350187/17367074086655925895977:Fraction),(3007044870550117597016/4134934306346732356185:Fraction),(341310027399618958357/469361461801530429621:Fraction),(12627353292330335069590/17366024086656975895977:Fraction),(21043726712873180391496/28942790144428876493295:Fraction),(63125592420951183957992/86826620433288379479885:Fraction),(4208000384086150529980/5788324695552675298659:Fraction),(21038140053231416996749/28941040144430626493295:Fraction),(63108834389842727109808/86821370433293629479885:Fraction),(1802949990803638219060/2480560583808439413711:Fraction),(21032554932734937270844/28939290144432376493295:Fraction)]
abbrev p1697 := params 0
abbrev ray1697 := rays 0
def bank1697 : Fin 1 → Cell := oneBank p1697 ray1697
theorem signs1697 : ∀ j, Signs p1697 (bank1697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1698 := params 1
abbrev ray1698 := rays 1
def bank1698 : Fin 1 → Cell := oneBank p1698 ray1698
theorem signs1698 : ∀ j, Signs p1698 (bank1698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1699 := params 2
abbrev ray1699 := rays 2
def bank1699 : Fin 1 → Cell := oneBank p1699 ray1699
theorem signs1699 : ∀ j, Signs p1699 (bank1699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1700 := params 3
abbrev ray1700 := rays 3
def bank1700 : Fin 1 → Cell := oneBank p1700 ray1700
theorem signs1700 : ∀ j, Signs p1700 (bank1700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1701 := params 4
abbrev ray1701 := rays 4
def bank1701 : Fin 1 → Cell := oneBank p1701 ray1701
theorem signs1701 : ∀ j, Signs p1701 (bank1701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1702 := params 5
abbrev ray1702 := rays 5
def bank1702 : Fin 1 → Cell := oneBank p1702 ray1702
theorem signs1702 : ∀ j, Signs p1702 (bank1702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1703 := params 6
abbrev ray1703 := rays 6
def bank1703 : Fin 1 → Cell := oneBank p1703 ray1703
theorem signs1703 : ∀ j, Signs p1703 (bank1703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1704 := params 7
abbrev ray1704 := rays 7
def bank1704 : Fin 1 → Cell := oneBank p1704 ray1704
theorem signs1704 : ∀ j, Signs p1704 (bank1704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1705 := params 8
abbrev ray1705 := rays 8
def bank1705 : Fin 1 → Cell := oneBank p1705 ray1705
theorem signs1705 : ∀ j, Signs p1705 (bank1705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1706 := params 9
abbrev ray1706 := rays 9
def bank1706 : Fin 1 → Cell := oneBank p1706 ray1706
theorem signs1706 : ∀ j, Signs p1706 (bank1706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1707 := params 10
abbrev ray1707 := rays 10
def bank1707 : Fin 1 → Cell := oneBank p1707 ray1707
theorem signs1707 : ∀ j, Signs p1707 (bank1707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1708 := params 11
abbrev ray1708 := rays 11
def bank1708 : Fin 1 → Cell := oneBank p1708 ray1708
theorem signs1708 : ∀ j, Signs p1708 (bank1708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1709 := params 12
abbrev ray1709 := rays 12
def bank1709 : Fin 1 → Cell := oneBank p1709 ray1709
theorem signs1709 : ∀ j, Signs p1709 (bank1709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1710 := params 13
abbrev ray1710 := rays 13
def bank1710 : Fin 1 → Cell := oneBank p1710 ray1710
theorem signs1710 : ∀ j, Signs p1710 (bank1710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1711 := params 14
abbrev ray1711 := rays 14
def bank1711 : Fin 1 → Cell := oneBank p1711 ray1711
theorem signs1711 : ∀ j, Signs p1711 (bank1711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1712 := params 15
abbrev ray1712 := rays 15
def bank1712 : Fin 1 → Cell := oneBank p1712 ray1712
theorem signs1712 : ∀ j, Signs p1712 (bank1712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1713 := params 16
abbrev ray1713 := rays 16
def bank1713 : Fin 1 → Cell := oneBank p1713 ray1713
theorem signs1713 : ∀ j, Signs p1713 (bank1713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1714 := params 17
abbrev ray1714 := rays 17
def bank1714 : Fin 1 → Cell := oneBank p1714 ray1714
theorem signs1714 : ∀ j, Signs p1714 (bank1714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1715 := params 18
abbrev ray1715 := rays 18
def bank1715 : Fin 1 → Cell := oneBank p1715 ray1715
theorem signs1715 : ∀ j, Signs p1715 (bank1715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1716 := params 19
abbrev ray1716 := rays 19
def bank1716 : Fin 1 → Cell := oneBank p1716 ray1716
theorem signs1716 : ∀ j, Signs p1716 (bank1716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1717 := params 20
abbrev ray1717 := rays 20
def bank1717 : Fin 1 → Cell := oneBank p1717 ray1717
theorem signs1717 : ∀ j, Signs p1717 (bank1717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1718 := params 21
abbrev ray1718 := rays 21
def bank1718 : Fin 1 → Cell := oneBank p1718 ray1718
theorem signs1718 : ∀ j, Signs p1718 (bank1718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1719 := params 22
abbrev ray1719 := rays 22
def bank1719 : Fin 1 → Cell := oneBank p1719 ray1719
theorem signs1719 : ∀ j, Signs p1719 (bank1719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1720 := params 23
abbrev ray1720 := rays 23
def bank1720 : Fin 1 → Cell := oneBank p1720 ray1720
theorem signs1720 : ∀ j, Signs p1720 (bank1720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1721 := params 24
abbrev ray1721 := rays 24
def bank1721 : Fin 1 → Cell := oneBank p1721 ray1721
theorem signs1721 : ∀ j, Signs p1721 (bank1721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1722 := params 25
abbrev ray1722 := rays 25
def bank1722 : Fin 1 → Cell := oneBank p1722 ray1722
theorem signs1722 : ∀ j, Signs p1722 (bank1722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1723 := params 26
abbrev ray1723 := rays 26
def bank1723 : Fin 1 → Cell := oneBank p1723 ray1723
theorem signs1723 : ∀ j, Signs p1723 (bank1723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1724 := params 27
abbrev ray1724 := rays 27
def bank1724 : Fin 1 → Cell := oneBank p1724 ray1724
theorem signs1724 : ∀ j, Signs p1724 (bank1724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1725 := params 28
abbrev ray1725 := rays 28
def bank1725 : Fin 1 → Cell := oneBank p1725 ray1725
theorem signs1725 : ∀ j, Signs p1725 (bank1725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1726 := params 29
abbrev ray1726 := rays 29
def bank1726 : Fin 1 → Cell := oneBank p1726 ray1726
theorem signs1726 : ∀ j, Signs p1726 (bank1726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1727 := params 30
abbrev ray1727 := rays 30
def bank1727 : Fin 1 → Cell := oneBank p1727 ray1727
theorem signs1727 : ∀ j, Signs p1727 (bank1727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1728 := params 31
abbrev ray1728 := rays 31
def bank1728 : Fin 1 → Cell := oneBank p1728 ray1728
theorem signs1728 : ∀ j, Signs p1728 (bank1728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01697_01728
