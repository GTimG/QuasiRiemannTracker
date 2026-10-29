/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00673_00704
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99907693172569,99907546779826,99907400360873,99907253915713,99907107444348,99906960946781,99906814423016,99906667873054,99906521296898,99906374694551,99906228066015,99906081411293,99905934730388,99905788023302,99905641290039,99905494530600,99905347744989,99905200933208,99905054095259,99904907231146,99904760340871,99904613424436,99904466481845,99904319513100,99904172518203,99904025497158,99903878449966,99903731376631,99903584277155,99903437151541,99903289999791,99903142821909,99902995617897]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (672+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(69228753618667103712394/88664120431450879479885:Fraction),(69222717331425790218628/88662370431452629479885:Fraction),(23072227353616996296941/29553540143818126493295:Fraction),(63788615490321588596/81713244637286755281:Fraction),(69204613358396562907922/88657120431457879479885:Fraction),(2562910322779883365874/3283532238202208499255:Fraction),(9884649298364403893924/12664802918780197068555:Fraction),(69186512478932301930536/88651870431463129479885:Fraction),(1537343992770483047488/1970002676254775099553:Fraction),(7686049765264692417278/9849818936829625497765:Fraction),(4611227727033613281844/5909774695431225298659:Fraction),(7684709303227841211382/9849430047941125497765:Fraction),(69156352569677700840022/88643120431471879479885:Fraction),(23050107475813525501312/29547123477157876493295:Fraction),(23048097363574771985471/29546540143825126493295:Fraction),(13827652554245224997380/17727574086295425895977:Fraction),(1868438736683845362829/2395570822472402148105:Fraction),(7680689417853334539826/9848263381275625497765:Fraction),(9874310867097765705793/12661802918783197068555:Fraction),(13822829436865887572996/17726174086296825895977:Fraction),(23036039772128573856844/29543040143828626493295:Fraction),(13820418493181633870720/17725474086297525895977:Fraction),(13819213084233307837012/17725124086297875895977:Fraction),(4606002626264969584210/5908258028766075298659:Fraction),(7676001463618967989222/9846902270165875497765:Fraction),(69077987968799972547328/88620370431494629479885:Fraction),(1096380358267790880112/1406644768753910785395:Fraction),(9866562598665288376771/12659552918785447068555:Fraction),(1973140389038269121344/2531860583757139413711:Fraction),(4603592670654626350960/5907558028766775298659:Fraction),(852442793941345511712/1093970622611152833085:Fraction),(69041842364642278020656/88609870431505129479885:Fraction)]
abbrev p673 := params 0
abbrev ray673 := rays 0
def bank673 : Fin 1 → Cell := oneBank p673 ray673
theorem signs673 : ∀ j, Signs p673 (bank673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p674 := params 1
abbrev ray674 := rays 1
def bank674 : Fin 1 → Cell := oneBank p674 ray674
theorem signs674 : ∀ j, Signs p674 (bank674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p675 := params 2
abbrev ray675 := rays 2
def bank675 : Fin 1 → Cell := oneBank p675 ray675
theorem signs675 : ∀ j, Signs p675 (bank675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p676 := params 3
abbrev ray676 := rays 3
def bank676 : Fin 1 → Cell := oneBank p676 ray676
theorem signs676 : ∀ j, Signs p676 (bank676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p677 := params 4
abbrev ray677 := rays 4
def bank677 : Fin 1 → Cell := oneBank p677 ray677
theorem signs677 : ∀ j, Signs p677 (bank677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p678 := params 5
abbrev ray678 := rays 5
def bank678 : Fin 1 → Cell := oneBank p678 ray678
theorem signs678 : ∀ j, Signs p678 (bank678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p679 := params 6
abbrev ray679 := rays 6
def bank679 : Fin 1 → Cell := oneBank p679 ray679
theorem signs679 : ∀ j, Signs p679 (bank679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p680 := params 7
abbrev ray680 := rays 7
def bank680 : Fin 1 → Cell := oneBank p680 ray680
theorem signs680 : ∀ j, Signs p680 (bank680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p681 := params 8
abbrev ray681 := rays 8
def bank681 : Fin 1 → Cell := oneBank p681 ray681
theorem signs681 : ∀ j, Signs p681 (bank681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p682 := params 9
abbrev ray682 := rays 9
def bank682 : Fin 1 → Cell := oneBank p682 ray682
theorem signs682 : ∀ j, Signs p682 (bank682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p683 := params 10
abbrev ray683 := rays 10
def bank683 : Fin 1 → Cell := oneBank p683 ray683
theorem signs683 : ∀ j, Signs p683 (bank683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p684 := params 11
abbrev ray684 := rays 11
def bank684 : Fin 1 → Cell := oneBank p684 ray684
theorem signs684 : ∀ j, Signs p684 (bank684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p685 := params 12
abbrev ray685 := rays 12
def bank685 : Fin 1 → Cell := oneBank p685 ray685
theorem signs685 : ∀ j, Signs p685 (bank685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p686 := params 13
abbrev ray686 := rays 13
def bank686 : Fin 1 → Cell := oneBank p686 ray686
theorem signs686 : ∀ j, Signs p686 (bank686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p687 := params 14
abbrev ray687 := rays 14
def bank687 : Fin 1 → Cell := oneBank p687 ray687
theorem signs687 : ∀ j, Signs p687 (bank687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p688 := params 15
abbrev ray688 := rays 15
def bank688 : Fin 1 → Cell := oneBank p688 ray688
theorem signs688 : ∀ j, Signs p688 (bank688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p689 := params 16
abbrev ray689 := rays 16
def bank689 : Fin 1 → Cell := oneBank p689 ray689
theorem signs689 : ∀ j, Signs p689 (bank689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p690 := params 17
abbrev ray690 := rays 17
def bank690 : Fin 1 → Cell := oneBank p690 ray690
theorem signs690 : ∀ j, Signs p690 (bank690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p691 := params 18
abbrev ray691 := rays 18
def bank691 : Fin 1 → Cell := oneBank p691 ray691
theorem signs691 : ∀ j, Signs p691 (bank691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p692 := params 19
abbrev ray692 := rays 19
def bank692 : Fin 1 → Cell := oneBank p692 ray692
theorem signs692 : ∀ j, Signs p692 (bank692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p693 := params 20
abbrev ray693 := rays 20
def bank693 : Fin 1 → Cell := oneBank p693 ray693
theorem signs693 : ∀ j, Signs p693 (bank693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p694 := params 21
abbrev ray694 := rays 21
def bank694 : Fin 1 → Cell := oneBank p694 ray694
theorem signs694 : ∀ j, Signs p694 (bank694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p695 := params 22
abbrev ray695 := rays 22
def bank695 : Fin 1 → Cell := oneBank p695 ray695
theorem signs695 : ∀ j, Signs p695 (bank695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p696 := params 23
abbrev ray696 := rays 23
def bank696 : Fin 1 → Cell := oneBank p696 ray696
theorem signs696 : ∀ j, Signs p696 (bank696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p697 := params 24
abbrev ray697 := rays 24
def bank697 : Fin 1 → Cell := oneBank p697 ray697
theorem signs697 : ∀ j, Signs p697 (bank697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p698 := params 25
abbrev ray698 := rays 25
def bank698 : Fin 1 → Cell := oneBank p698 ray698
theorem signs698 : ∀ j, Signs p698 (bank698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p699 := params 26
abbrev ray699 := rays 26
def bank699 : Fin 1 → Cell := oneBank p699 ray699
theorem signs699 : ∀ j, Signs p699 (bank699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p700 := params 27
abbrev ray700 := rays 27
def bank700 : Fin 1 → Cell := oneBank p700 ray700
theorem signs700 : ∀ j, Signs p700 (bank700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p701 := params 28
abbrev ray701 := rays 28
def bank701 : Fin 1 → Cell := oneBank p701 ray701
theorem signs701 : ∀ j, Signs p701 (bank701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p702 := params 29
abbrev ray702 := rays 29
def bank702 : Fin 1 → Cell := oneBank p702 ray702
theorem signs702 : ∀ j, Signs p702 (bank702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p703 := params 30
abbrev ray703 := rays 30
def bank703 : Fin 1 → Cell := oneBank p703 ray703
theorem signs703 : ∀ j, Signs p703 (bank703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p704 := params 31
abbrev ray704 := rays 31
def bank704 : Fin 1 → Cell := oneBank p704 ray704
theorem signs704 : ∀ j, Signs p704 (bank704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00673_00704
