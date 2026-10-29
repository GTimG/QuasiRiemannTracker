/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01633_01664
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99755458175433,99755287745740,99755117292083,99754946814464,99754776312885,99754605787348,99754435237856,99754264664409,99754094067010,99753923445662,99753752800366,99753582131125,99753411437940,99753240720813,99753069979747,99752899214743,99752728425803,99752557612930,99752386776126,99752215915393,99752045030732,99751874122146,99751703189637,99751532233207,99751361252857,99751190248590,99751019220408,99750848168313,99750677092307,99750505992392,99750334868570,99750163720843,99749992549213]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1632+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(12726029573442566844539/17396824086626175895977:Fraction),(12724904258636021512796/17396474086626525895977:Fraction),(573143216206413028163/783609193091300716035:Fraction),(49122218173182409024/67165150913618632803:Fraction),(12721529579853646023293/17395424086627575895977:Fraction),(7066891591006210528058/9663930048126625497765:Fraction),(49109190574275721384/67161096859568632803:Fraction),(63590779098040442031839/86971870433143129479885:Fraction),(1413003471825047307496/1932669342958775099553:Fraction),(2354797571153958926944/3221050756783208499255:Fraction),(572737949909619621616/783483066965300716035:Fraction),(12726384687446924945/17410384471101127023:Fraction),(12712534083491187858016/17392624086630375895977:Fraction),(63557050376207763510728/86961370433153629479885:Fraction),(3026258637624080115517/4140934306340732356185:Fraction),(63545812233918154858258/86957870433157129479885:Fraction),(63540192907655163188843/86956120433158879479885:Fraction),(114476711057005013492/156674541321010143207:Fraction),(21176318731864604418616/28984206811054126493295:Fraction),(343369398972276013262/470004705044130429621:Fraction),(21172573751389470803458/28983040144388626493295:Fraction),(12702420950772515592764/17389474086633525895977:Fraction),(63506488083625702408871/86945620433169379479885:Fraction),(21166957489620409629998/28981290144390376493295:Fraction),(3023583651629161285117/4140100973008232356185:Fraction),(12697928391022304653928/17388074086634925895977:Fraction),(571928171677253440258/783230814713300716035:Fraction),(5770764837532934916146/7903351857561648134535:Fraction),(9067542742823093208863/12419302919025697068555:Fraction),(4231145749490674625158/5795558028878775298659:Fraction),(4230771541014569188796/5795441362212225298659:Fraction),(12691192208770319847170/17385974086637025895977:Fraction)]
abbrev p1633 := params 0
abbrev ray1633 := rays 0
def bank1633 : Fin 1 → Cell := oneBank p1633 ray1633
theorem signs1633 : ∀ j, Signs p1633 (bank1633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1634 := params 1
abbrev ray1634 := rays 1
def bank1634 : Fin 1 → Cell := oneBank p1634 ray1634
theorem signs1634 : ∀ j, Signs p1634 (bank1634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1635 := params 2
abbrev ray1635 := rays 2
def bank1635 : Fin 1 → Cell := oneBank p1635 ray1635
theorem signs1635 : ∀ j, Signs p1635 (bank1635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1636 := params 3
abbrev ray1636 := rays 3
def bank1636 : Fin 1 → Cell := oneBank p1636 ray1636
theorem signs1636 : ∀ j, Signs p1636 (bank1636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1637 := params 4
abbrev ray1637 := rays 4
def bank1637 : Fin 1 → Cell := oneBank p1637 ray1637
theorem signs1637 : ∀ j, Signs p1637 (bank1637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1638 := params 5
abbrev ray1638 := rays 5
def bank1638 : Fin 1 → Cell := oneBank p1638 ray1638
theorem signs1638 : ∀ j, Signs p1638 (bank1638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1639 := params 6
abbrev ray1639 := rays 6
def bank1639 : Fin 1 → Cell := oneBank p1639 ray1639
theorem signs1639 : ∀ j, Signs p1639 (bank1639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1640 := params 7
abbrev ray1640 := rays 7
def bank1640 : Fin 1 → Cell := oneBank p1640 ray1640
theorem signs1640 : ∀ j, Signs p1640 (bank1640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1641 := params 8
abbrev ray1641 := rays 8
def bank1641 : Fin 1 → Cell := oneBank p1641 ray1641
theorem signs1641 : ∀ j, Signs p1641 (bank1641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1642 := params 9
abbrev ray1642 := rays 9
def bank1642 : Fin 1 → Cell := oneBank p1642 ray1642
theorem signs1642 : ∀ j, Signs p1642 (bank1642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1643 := params 10
abbrev ray1643 := rays 10
def bank1643 : Fin 1 → Cell := oneBank p1643 ray1643
theorem signs1643 : ∀ j, Signs p1643 (bank1643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1644 := params 11
abbrev ray1644 := rays 11
def bank1644 : Fin 1 → Cell := oneBank p1644 ray1644
theorem signs1644 : ∀ j, Signs p1644 (bank1644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1645 := params 12
abbrev ray1645 := rays 12
def bank1645 : Fin 1 → Cell := oneBank p1645 ray1645
theorem signs1645 : ∀ j, Signs p1645 (bank1645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1646 := params 13
abbrev ray1646 := rays 13
def bank1646 : Fin 1 → Cell := oneBank p1646 ray1646
theorem signs1646 : ∀ j, Signs p1646 (bank1646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1647 := params 14
abbrev ray1647 := rays 14
def bank1647 : Fin 1 → Cell := oneBank p1647 ray1647
theorem signs1647 : ∀ j, Signs p1647 (bank1647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1648 := params 15
abbrev ray1648 := rays 15
def bank1648 : Fin 1 → Cell := oneBank p1648 ray1648
theorem signs1648 : ∀ j, Signs p1648 (bank1648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1649 := params 16
abbrev ray1649 := rays 16
def bank1649 : Fin 1 → Cell := oneBank p1649 ray1649
theorem signs1649 : ∀ j, Signs p1649 (bank1649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1650 := params 17
abbrev ray1650 := rays 17
def bank1650 : Fin 1 → Cell := oneBank p1650 ray1650
theorem signs1650 : ∀ j, Signs p1650 (bank1650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1651 := params 18
abbrev ray1651 := rays 18
def bank1651 : Fin 1 → Cell := oneBank p1651 ray1651
theorem signs1651 : ∀ j, Signs p1651 (bank1651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1652 := params 19
abbrev ray1652 := rays 19
def bank1652 : Fin 1 → Cell := oneBank p1652 ray1652
theorem signs1652 : ∀ j, Signs p1652 (bank1652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1653 := params 20
abbrev ray1653 := rays 20
def bank1653 : Fin 1 → Cell := oneBank p1653 ray1653
theorem signs1653 : ∀ j, Signs p1653 (bank1653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1654 := params 21
abbrev ray1654 := rays 21
def bank1654 : Fin 1 → Cell := oneBank p1654 ray1654
theorem signs1654 : ∀ j, Signs p1654 (bank1654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1655 := params 22
abbrev ray1655 := rays 22
def bank1655 : Fin 1 → Cell := oneBank p1655 ray1655
theorem signs1655 : ∀ j, Signs p1655 (bank1655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1656 := params 23
abbrev ray1656 := rays 23
def bank1656 : Fin 1 → Cell := oneBank p1656 ray1656
theorem signs1656 : ∀ j, Signs p1656 (bank1656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1657 := params 24
abbrev ray1657 := rays 24
def bank1657 : Fin 1 → Cell := oneBank p1657 ray1657
theorem signs1657 : ∀ j, Signs p1657 (bank1657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1658 := params 25
abbrev ray1658 := rays 25
def bank1658 : Fin 1 → Cell := oneBank p1658 ray1658
theorem signs1658 : ∀ j, Signs p1658 (bank1658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1659 := params 26
abbrev ray1659 := rays 26
def bank1659 : Fin 1 → Cell := oneBank p1659 ray1659
theorem signs1659 : ∀ j, Signs p1659 (bank1659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1660 := params 27
abbrev ray1660 := rays 27
def bank1660 : Fin 1 → Cell := oneBank p1660 ray1660
theorem signs1660 : ∀ j, Signs p1660 (bank1660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1661 := params 28
abbrev ray1661 := rays 28
def bank1661 : Fin 1 → Cell := oneBank p1661 ray1661
theorem signs1661 : ∀ j, Signs p1661 (bank1661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1662 := params 29
abbrev ray1662 := rays 29
def bank1662 : Fin 1 → Cell := oneBank p1662 ray1662
theorem signs1662 : ∀ j, Signs p1662 (bank1662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1663 := params 30
abbrev ray1663 := rays 30
def bank1663 : Fin 1 → Cell := oneBank p1663 ray1663
theorem signs1663 : ∀ j, Signs p1663 (bank1663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1664 := params 31
abbrev ray1664 := rays 31
def bank1664 : Fin 1 → Cell := oneBank p1664 ray1664
theorem signs1664 : ∀ j, Signs p1664 (bank1664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01633_01664
