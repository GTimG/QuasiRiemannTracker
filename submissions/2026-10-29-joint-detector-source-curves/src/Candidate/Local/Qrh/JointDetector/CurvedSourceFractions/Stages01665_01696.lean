/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01665_01696
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99749992549213,99749821353682,99749650134252,99749478890925,99749307623703,99749136332589,99748965017584,99748793678690,99748622315910,99748450929245,99748279518697,99748108084269,99747936625962,99747765143778,99747593637720,99747422107790,99747250553989,99747078976319,99746907374783,99746735749382,99746564100119,99746392426996,99746220730014,99746049009176,99745877264484,99745705495939,99745533703543,99745361887299,99745190047209,99745018183275,99744846295499,99744674383883,99744502448428]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1664+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(21150116267597446349803/28976040144395626493295:Fraction),(63444737617583255730124/86926370433188629479885:Fraction),(63439126262729569199042/86924620433190379479885:Fraction),(183865263663192994070/251950349081716317333:Fraction),(21142635165092234461891/28973706811064626493295:Fraction),(63422294857165965959864/86919370433195629479885:Fraction),(1006614071439402412054/1379644768780910785395:Fraction),(469711679622750618836/643821262468141699851:Fraction),(4227031203570797530624/5794274695546725298659:Fraction),(4226657360946986667532/5794158028880175298659:Fraction),(63394252605393822548654/86910620433204379479885:Fraction),(63388645852811620231019/86908870433206129479885:Fraction),(1408511976240517313792/1931269342960175099553:Fraction),(9053918834205533572556/12415052919029947068555:Fraction),(12674365160876453949806/17380724086642275895977:Fraction),(1408138240571233570880/1931152676293625099553:Fraction),(63360615677717939342539/86900120433214879479885:Fraction),(91421373140237284739/125394473929605525945:Fraction),(4223293821692590721663/5793108028881225298659:Fraction),(63343802895340047397504/86894870433220129479885:Fraction),(12667639904369129849290/17378624086644375895977:Fraction),(3015837962140822618324/4137684306343982356185:Fraction),(7036332746544557149808/9654402270358375497765:Fraction),(63321392063687871709772/86887870433227129479885:Fraction),(7035087829464442537442/9654013381469875497765:Fraction),(21103396641142619769779/28961456811076876493295:Fraction),(63304587986723088563854/86882620433232379479885:Fraction),(468881395057160561411/643562003209141699851:Fraction),(63293388509686311005068/86879120433235879479885:Fraction),(12657557703528380756975/17375474086647525895977:Fraction),(7031354398058769982867/9652846714804375497765:Fraction),(63276591704398966601908/86873870433241129479885:Fraction)]
abbrev p1665 := params 0
abbrev ray1665 := rays 0
def bank1665 : Fin 1 → Cell := oneBank p1665 ray1665
theorem signs1665 : ∀ j, Signs p1665 (bank1665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1666 := params 1
abbrev ray1666 := rays 1
def bank1666 : Fin 1 → Cell := oneBank p1666 ray1666
theorem signs1666 : ∀ j, Signs p1666 (bank1666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1667 := params 2
abbrev ray1667 := rays 2
def bank1667 : Fin 1 → Cell := oneBank p1667 ray1667
theorem signs1667 : ∀ j, Signs p1667 (bank1667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1668 := params 3
abbrev ray1668 := rays 3
def bank1668 : Fin 1 → Cell := oneBank p1668 ray1668
theorem signs1668 : ∀ j, Signs p1668 (bank1668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1669 := params 4
abbrev ray1669 := rays 4
def bank1669 : Fin 1 → Cell := oneBank p1669 ray1669
theorem signs1669 : ∀ j, Signs p1669 (bank1669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1670 := params 5
abbrev ray1670 := rays 5
def bank1670 : Fin 1 → Cell := oneBank p1670 ray1670
theorem signs1670 : ∀ j, Signs p1670 (bank1670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1671 := params 6
abbrev ray1671 := rays 6
def bank1671 : Fin 1 → Cell := oneBank p1671 ray1671
theorem signs1671 : ∀ j, Signs p1671 (bank1671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1672 := params 7
abbrev ray1672 := rays 7
def bank1672 : Fin 1 → Cell := oneBank p1672 ray1672
theorem signs1672 : ∀ j, Signs p1672 (bank1672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1673 := params 8
abbrev ray1673 := rays 8
def bank1673 : Fin 1 → Cell := oneBank p1673 ray1673
theorem signs1673 : ∀ j, Signs p1673 (bank1673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1674 := params 9
abbrev ray1674 := rays 9
def bank1674 : Fin 1 → Cell := oneBank p1674 ray1674
theorem signs1674 : ∀ j, Signs p1674 (bank1674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1675 := params 10
abbrev ray1675 := rays 10
def bank1675 : Fin 1 → Cell := oneBank p1675 ray1675
theorem signs1675 : ∀ j, Signs p1675 (bank1675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1676 := params 11
abbrev ray1676 := rays 11
def bank1676 : Fin 1 → Cell := oneBank p1676 ray1676
theorem signs1676 : ∀ j, Signs p1676 (bank1676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1677 := params 12
abbrev ray1677 := rays 12
def bank1677 : Fin 1 → Cell := oneBank p1677 ray1677
theorem signs1677 : ∀ j, Signs p1677 (bank1677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1678 := params 13
abbrev ray1678 := rays 13
def bank1678 : Fin 1 → Cell := oneBank p1678 ray1678
theorem signs1678 : ∀ j, Signs p1678 (bank1678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1679 := params 14
abbrev ray1679 := rays 14
def bank1679 : Fin 1 → Cell := oneBank p1679 ray1679
theorem signs1679 : ∀ j, Signs p1679 (bank1679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1680 := params 15
abbrev ray1680 := rays 15
def bank1680 : Fin 1 → Cell := oneBank p1680 ray1680
theorem signs1680 : ∀ j, Signs p1680 (bank1680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1681 := params 16
abbrev ray1681 := rays 16
def bank1681 : Fin 1 → Cell := oneBank p1681 ray1681
theorem signs1681 : ∀ j, Signs p1681 (bank1681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1682 := params 17
abbrev ray1682 := rays 17
def bank1682 : Fin 1 → Cell := oneBank p1682 ray1682
theorem signs1682 : ∀ j, Signs p1682 (bank1682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1683 := params 18
abbrev ray1683 := rays 18
def bank1683 : Fin 1 → Cell := oneBank p1683 ray1683
theorem signs1683 : ∀ j, Signs p1683 (bank1683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1684 := params 19
abbrev ray1684 := rays 19
def bank1684 : Fin 1 → Cell := oneBank p1684 ray1684
theorem signs1684 : ∀ j, Signs p1684 (bank1684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1685 := params 20
abbrev ray1685 := rays 20
def bank1685 : Fin 1 → Cell := oneBank p1685 ray1685
theorem signs1685 : ∀ j, Signs p1685 (bank1685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1686 := params 21
abbrev ray1686 := rays 21
def bank1686 : Fin 1 → Cell := oneBank p1686 ray1686
theorem signs1686 : ∀ j, Signs p1686 (bank1686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1687 := params 22
abbrev ray1687 := rays 22
def bank1687 : Fin 1 → Cell := oneBank p1687 ray1687
theorem signs1687 : ∀ j, Signs p1687 (bank1687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1688 := params 23
abbrev ray1688 := rays 23
def bank1688 : Fin 1 → Cell := oneBank p1688 ray1688
theorem signs1688 : ∀ j, Signs p1688 (bank1688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1689 := params 24
abbrev ray1689 := rays 24
def bank1689 : Fin 1 → Cell := oneBank p1689 ray1689
theorem signs1689 : ∀ j, Signs p1689 (bank1689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1690 := params 25
abbrev ray1690 := rays 25
def bank1690 : Fin 1 → Cell := oneBank p1690 ray1690
theorem signs1690 : ∀ j, Signs p1690 (bank1690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1691 := params 26
abbrev ray1691 := rays 26
def bank1691 : Fin 1 → Cell := oneBank p1691 ray1691
theorem signs1691 : ∀ j, Signs p1691 (bank1691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1692 := params 27
abbrev ray1692 := rays 27
def bank1692 : Fin 1 → Cell := oneBank p1692 ray1692
theorem signs1692 : ∀ j, Signs p1692 (bank1692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1693 := params 28
abbrev ray1693 := rays 28
def bank1693 : Fin 1 → Cell := oneBank p1693 ray1693
theorem signs1693 : ∀ j, Signs p1693 (bank1693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1694 := params 29
abbrev ray1694 := rays 29
def bank1694 : Fin 1 → Cell := oneBank p1694 ray1694
theorem signs1694 : ∀ j, Signs p1694 (bank1694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1695 := params 30
abbrev ray1695 := rays 30
def bank1695 : Fin 1 → Cell := oneBank p1695 ray1695
theorem signs1695 : ∀ j, Signs p1695 (bank1695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1696 := params 31
abbrev ray1696 := rays 31
def bank1696 : Fin 1 → Cell := oneBank p1696 ray1696
theorem signs1696 : ∀ j, Signs p1696 (bank1696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01665_01696
