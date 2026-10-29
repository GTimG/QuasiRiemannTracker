/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01761_01792
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99733449087424,99733275606774,99733102102418,99732928574356,99732755022592,99732581447128,99732407847965,99732234225105,99732060578550,99731886908303,99731713214365,99731539496738,99731365755424,99731191990425,99731018201743,99730844389381,99730670553339,99730496693620,99730322810226,99730148903159,99729974972421,99729801018014,99729627039940,99729453038200,99729279012798,99729104963734,99728930891011,99728756794631,99728582674595,99728408530906,99728234363566,99728060172576,99727885957938]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1760+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(2330133723189969880508/3213337793827958499255:Fraction),(8986862795248704348448/12394052919050947068555:Fraction),(4193497977787546446188/5783774695557225298659:Fraction),(776504948474014813262/1071047783127902833085:Fraction),(20963777272877935636426/28917706811120626493295:Fraction),(62885763870459318025556/86751370433363629479885:Fraction),(155259742604907789635/214196593662630566617:Fraction),(12574925739835364582819/17349574086673425895977:Fraction),(4191270765074407131280/5783074695557925298659:Fraction),(6521786006099418166/8999312214272292715:Fraction),(4190528598817724935483/5782841362224825298659:Fraction),(20950787494848879895088/28913623477791376493295:Fraction),(4189786551578621656858/5782608028891725298659:Fraction),(1396471837081396430195/1927497120741725099553:Fraction),(62835668123555766124384/86735620433379379479885:Fraction),(20943368212803503682472/28911290144460376493295:Fraction),(62824540986203373816176/86732120433382879479885:Fraction),(12563795433389041182608/17346074086676925895977:Fraction),(20937805211615643400424/28909540144462126493295:Fraction),(62807852708658143472119/86726870433388129479885:Fraction),(62802290842603612337351/86725120433389879479885:Fraction),(20932243345578216279296/28907790144463876493295:Fraction),(12558233812789319707274/17344324086678675895977:Fraction),(17862192866073443380/24671371389301601559:Fraction),(20926682614944960766736/28906040144465626493295:Fraction),(20924829199519478961184/28905456811132876493295:Fraction),(3692289906625941033323/5100860025494139969405:Fraction),(4184224685808923854867/5780858028893475298659:Fraction),(12551562398969640487531/17342224086680775895977:Fraction),(62752253535794862359668/86709370433405629479885:Fraction),(995979303765877936736/1376311435450910785395:Fraction),(62741138571984194516518/86705870433409129479885:Fraction)]
abbrev p1761 := params 0
abbrev ray1761 := rays 0
def bank1761 : Fin 1 → Cell := oneBank p1761 ray1761
theorem signs1761 : ∀ j, Signs p1761 (bank1761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1762 := params 1
abbrev ray1762 := rays 1
def bank1762 : Fin 1 → Cell := oneBank p1762 ray1762
theorem signs1762 : ∀ j, Signs p1762 (bank1762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1763 := params 2
abbrev ray1763 := rays 2
def bank1763 : Fin 1 → Cell := oneBank p1763 ray1763
theorem signs1763 : ∀ j, Signs p1763 (bank1763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1764 := params 3
abbrev ray1764 := rays 3
def bank1764 : Fin 1 → Cell := oneBank p1764 ray1764
theorem signs1764 : ∀ j, Signs p1764 (bank1764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1765 := params 4
abbrev ray1765 := rays 4
def bank1765 : Fin 1 → Cell := oneBank p1765 ray1765
theorem signs1765 : ∀ j, Signs p1765 (bank1765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1766 := params 5
abbrev ray1766 := rays 5
def bank1766 : Fin 1 → Cell := oneBank p1766 ray1766
theorem signs1766 : ∀ j, Signs p1766 (bank1766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1767 := params 6
abbrev ray1767 := rays 6
def bank1767 : Fin 1 → Cell := oneBank p1767 ray1767
theorem signs1767 : ∀ j, Signs p1767 (bank1767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1768 := params 7
abbrev ray1768 := rays 7
def bank1768 : Fin 1 → Cell := oneBank p1768 ray1768
theorem signs1768 : ∀ j, Signs p1768 (bank1768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1769 := params 8
abbrev ray1769 := rays 8
def bank1769 : Fin 1 → Cell := oneBank p1769 ray1769
theorem signs1769 : ∀ j, Signs p1769 (bank1769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1770 := params 9
abbrev ray1770 := rays 9
def bank1770 : Fin 1 → Cell := oneBank p1770 ray1770
theorem signs1770 : ∀ j, Signs p1770 (bank1770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1771 := params 10
abbrev ray1771 := rays 10
def bank1771 : Fin 1 → Cell := oneBank p1771 ray1771
theorem signs1771 : ∀ j, Signs p1771 (bank1771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1772 := params 11
abbrev ray1772 := rays 11
def bank1772 : Fin 1 → Cell := oneBank p1772 ray1772
theorem signs1772 : ∀ j, Signs p1772 (bank1772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1773 := params 12
abbrev ray1773 := rays 12
def bank1773 : Fin 1 → Cell := oneBank p1773 ray1773
theorem signs1773 : ∀ j, Signs p1773 (bank1773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1774 := params 13
abbrev ray1774 := rays 13
def bank1774 : Fin 1 → Cell := oneBank p1774 ray1774
theorem signs1774 : ∀ j, Signs p1774 (bank1774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1775 := params 14
abbrev ray1775 := rays 14
def bank1775 : Fin 1 → Cell := oneBank p1775 ray1775
theorem signs1775 : ∀ j, Signs p1775 (bank1775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1776 := params 15
abbrev ray1776 := rays 15
def bank1776 : Fin 1 → Cell := oneBank p1776 ray1776
theorem signs1776 : ∀ j, Signs p1776 (bank1776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1777 := params 16
abbrev ray1777 := rays 16
def bank1777 : Fin 1 → Cell := oneBank p1777 ray1777
theorem signs1777 : ∀ j, Signs p1777 (bank1777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1778 := params 17
abbrev ray1778 := rays 17
def bank1778 : Fin 1 → Cell := oneBank p1778 ray1778
theorem signs1778 : ∀ j, Signs p1778 (bank1778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1779 := params 18
abbrev ray1779 := rays 18
def bank1779 : Fin 1 → Cell := oneBank p1779 ray1779
theorem signs1779 : ∀ j, Signs p1779 (bank1779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1780 := params 19
abbrev ray1780 := rays 19
def bank1780 : Fin 1 → Cell := oneBank p1780 ray1780
theorem signs1780 : ∀ j, Signs p1780 (bank1780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1781 := params 20
abbrev ray1781 := rays 20
def bank1781 : Fin 1 → Cell := oneBank p1781 ray1781
theorem signs1781 : ∀ j, Signs p1781 (bank1781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1782 := params 21
abbrev ray1782 := rays 21
def bank1782 : Fin 1 → Cell := oneBank p1782 ray1782
theorem signs1782 : ∀ j, Signs p1782 (bank1782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1783 := params 22
abbrev ray1783 := rays 22
def bank1783 : Fin 1 → Cell := oneBank p1783 ray1783
theorem signs1783 : ∀ j, Signs p1783 (bank1783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1784 := params 23
abbrev ray1784 := rays 23
def bank1784 : Fin 1 → Cell := oneBank p1784 ray1784
theorem signs1784 : ∀ j, Signs p1784 (bank1784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1785 := params 24
abbrev ray1785 := rays 24
def bank1785 : Fin 1 → Cell := oneBank p1785 ray1785
theorem signs1785 : ∀ j, Signs p1785 (bank1785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1786 := params 25
abbrev ray1786 := rays 25
def bank1786 : Fin 1 → Cell := oneBank p1786 ray1786
theorem signs1786 : ∀ j, Signs p1786 (bank1786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1787 := params 26
abbrev ray1787 := rays 26
def bank1787 : Fin 1 → Cell := oneBank p1787 ray1787
theorem signs1787 : ∀ j, Signs p1787 (bank1787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1788 := params 27
abbrev ray1788 := rays 27
def bank1788 : Fin 1 → Cell := oneBank p1788 ray1788
theorem signs1788 : ∀ j, Signs p1788 (bank1788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1789 := params 28
abbrev ray1789 := rays 28
def bank1789 : Fin 1 → Cell := oneBank p1789 ray1789
theorem signs1789 : ∀ j, Signs p1789 (bank1789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1790 := params 29
abbrev ray1790 := rays 29
def bank1790 : Fin 1 → Cell := oneBank p1790 ray1790
theorem signs1790 : ∀ j, Signs p1790 (bank1790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1791 := params 30
abbrev ray1791 := rays 30
def bank1791 : Fin 1 → Cell := oneBank p1791 ray1791
theorem signs1791 : ∀ j, Signs p1791 (bank1791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1792 := params 31
abbrev ray1792 := rays 31
def bank1792 : Fin 1 → Cell := oneBank p1792 ray1792
theorem signs1792 : ∀ j, Signs p1792 (bank1792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01761_01792
