/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00769_00800
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99893520330794,99893371433957,99893222511163,99893073562415,99892924587715,99892775587065,99892626560468,99892477507927,99892328429444,99892179325022,99892030194664,99891881038372,99891731856149,99891582647997,99891433413918,99891284153916,99891134867993,99890985556152,99890836218395,99890686854725,99890537465144,99890388049655,99890238608260,99890089140962,99889939647764,99889790128669,99889640583678,99889491012795,99889341416022,99889191793361,99889042144816,99888892470388,99888742770081]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (768+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1525583157489442126828/1966580454035975099553:Fraction),(68645246617146015244447/88494370431620629479885:Fraction),(7626583439448572706239/9832513381291375497765:Fraction),(13726651262721379622162/17698174086324825895977:Fraction),(13725452538581983390526/17697824086325175895977:Fraction),(72615099343996079350/93637429028177385693:Fraction),(68615274875118770862964/88485620431629379479885:Fraction),(68609283103956726753476/88483870431631129479885:Fraction),(846954196639319153318/1092371857180652833085:Fraction),(2540640658242107080792/3277050756727208499255:Fraction),(68591306638268682544412/88478620431636379479885:Fraction),(692780962747717912682/893705761935738681615:Fraction),(68579325006840953366599/88475120431639879479885:Fraction),(3265396881415925213531/4213017639601982356185:Fraction),(507906250523822493032/655345336530691699851:Fraction),(68561354152867944328388/88469870431645129479885:Fraction),(3264541214583084763736/4212767639602232356185:Fraction),(22849792222601787304444/29488790143882876493295:Fraction),(4569559256711504806363/5897641362110025298659:Fraction),(13707480168355298833640/17692574086330425895977:Fraction),(22843804618089577528856/29487040143884626493295:Fraction),(370407711757030478224/478158759090030429621:Fraction),(1522654233717834142550/1965724898481275099553:Fraction),(22837818055965682417448/29485290143886376493295:Fraction),(68507467626846871974986/88454120431660879479885:Fraction),(68501483320588485163282/88452370431662629479885:Fraction),(22831832536513209979936/29483540143888126493295:Fraction),(13697902584030464217935/17689774086333225895977:Fraction),(13696705850496228542576/17689424086333575895977:Fraction),(1521723230962474494377/1965452676259325099553:Fraction),(1850582771782175766248/2390368119774902148105:Fraction),(9780797075303420964338/12634552918810447068555:Fraction)]
abbrev p769 := params 0
abbrev ray769 := rays 0
def bank769 : Fin 1 → Cell := oneBank p769 ray769
theorem signs769 : ∀ j, Signs p769 (bank769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p770 := params 1
abbrev ray770 := rays 1
def bank770 : Fin 1 → Cell := oneBank p770 ray770
theorem signs770 : ∀ j, Signs p770 (bank770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p771 := params 2
abbrev ray771 := rays 2
def bank771 : Fin 1 → Cell := oneBank p771 ray771
theorem signs771 : ∀ j, Signs p771 (bank771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p772 := params 3
abbrev ray772 := rays 3
def bank772 : Fin 1 → Cell := oneBank p772 ray772
theorem signs772 : ∀ j, Signs p772 (bank772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p773 := params 4
abbrev ray773 := rays 4
def bank773 : Fin 1 → Cell := oneBank p773 ray773
theorem signs773 : ∀ j, Signs p773 (bank773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p774 := params 5
abbrev ray774 := rays 5
def bank774 : Fin 1 → Cell := oneBank p774 ray774
theorem signs774 : ∀ j, Signs p774 (bank774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p775 := params 6
abbrev ray775 := rays 6
def bank775 : Fin 1 → Cell := oneBank p775 ray775
theorem signs775 : ∀ j, Signs p775 (bank775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p776 := params 7
abbrev ray776 := rays 7
def bank776 : Fin 1 → Cell := oneBank p776 ray776
theorem signs776 : ∀ j, Signs p776 (bank776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p777 := params 8
abbrev ray777 := rays 8
def bank777 : Fin 1 → Cell := oneBank p777 ray777
theorem signs777 : ∀ j, Signs p777 (bank777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p778 := params 9
abbrev ray778 := rays 9
def bank778 : Fin 1 → Cell := oneBank p778 ray778
theorem signs778 : ∀ j, Signs p778 (bank778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p779 := params 10
abbrev ray779 := rays 10
def bank779 : Fin 1 → Cell := oneBank p779 ray779
theorem signs779 : ∀ j, Signs p779 (bank779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p780 := params 11
abbrev ray780 := rays 11
def bank780 : Fin 1 → Cell := oneBank p780 ray780
theorem signs780 : ∀ j, Signs p780 (bank780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p781 := params 12
abbrev ray781 := rays 12
def bank781 : Fin 1 → Cell := oneBank p781 ray781
theorem signs781 : ∀ j, Signs p781 (bank781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p782 := params 13
abbrev ray782 := rays 13
def bank782 : Fin 1 → Cell := oneBank p782 ray782
theorem signs782 : ∀ j, Signs p782 (bank782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p783 := params 14
abbrev ray783 := rays 14
def bank783 : Fin 1 → Cell := oneBank p783 ray783
theorem signs783 : ∀ j, Signs p783 (bank783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p784 := params 15
abbrev ray784 := rays 15
def bank784 : Fin 1 → Cell := oneBank p784 ray784
theorem signs784 : ∀ j, Signs p784 (bank784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p785 := params 16
abbrev ray785 := rays 16
def bank785 : Fin 1 → Cell := oneBank p785 ray785
theorem signs785 : ∀ j, Signs p785 (bank785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p786 := params 17
abbrev ray786 := rays 17
def bank786 : Fin 1 → Cell := oneBank p786 ray786
theorem signs786 : ∀ j, Signs p786 (bank786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p787 := params 18
abbrev ray787 := rays 18
def bank787 : Fin 1 → Cell := oneBank p787 ray787
theorem signs787 : ∀ j, Signs p787 (bank787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p788 := params 19
abbrev ray788 := rays 19
def bank788 : Fin 1 → Cell := oneBank p788 ray788
theorem signs788 : ∀ j, Signs p788 (bank788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p789 := params 20
abbrev ray789 := rays 20
def bank789 : Fin 1 → Cell := oneBank p789 ray789
theorem signs789 : ∀ j, Signs p789 (bank789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p790 := params 21
abbrev ray790 := rays 21
def bank790 : Fin 1 → Cell := oneBank p790 ray790
theorem signs790 : ∀ j, Signs p790 (bank790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p791 := params 22
abbrev ray791 := rays 22
def bank791 : Fin 1 → Cell := oneBank p791 ray791
theorem signs791 : ∀ j, Signs p791 (bank791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p792 := params 23
abbrev ray792 := rays 23
def bank792 : Fin 1 → Cell := oneBank p792 ray792
theorem signs792 : ∀ j, Signs p792 (bank792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p793 := params 24
abbrev ray793 := rays 24
def bank793 : Fin 1 → Cell := oneBank p793 ray793
theorem signs793 : ∀ j, Signs p793 (bank793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p794 := params 25
abbrev ray794 := rays 25
def bank794 : Fin 1 → Cell := oneBank p794 ray794
theorem signs794 : ∀ j, Signs p794 (bank794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p795 := params 26
abbrev ray795 := rays 26
def bank795 : Fin 1 → Cell := oneBank p795 ray795
theorem signs795 : ∀ j, Signs p795 (bank795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p796 := params 27
abbrev ray796 := rays 27
def bank796 : Fin 1 → Cell := oneBank p796 ray796
theorem signs796 : ∀ j, Signs p796 (bank796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p797 := params 28
abbrev ray797 := rays 28
def bank797 : Fin 1 → Cell := oneBank p797 ray797
theorem signs797 : ∀ j, Signs p797 (bank797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p798 := params 29
abbrev ray798 := rays 29
def bank798 : Fin 1 → Cell := oneBank p798 ray798
theorem signs798 : ∀ j, Signs p798 (bank798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p799 := params 30
abbrev ray799 := rays 30
def bank799 : Fin 1 → Cell := oneBank p799 ray799
theorem signs799 : ∀ j, Signs p799 (bank799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p800 := params 31
abbrev ray800 := rays 31
def bank800 : Fin 1 → Cell := oneBank p800 ray800
theorem signs800 : ∀ j, Signs p800 (bank800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00769_00800
