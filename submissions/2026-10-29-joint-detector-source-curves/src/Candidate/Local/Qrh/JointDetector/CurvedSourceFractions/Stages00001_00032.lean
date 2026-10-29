/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00001_00032
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99999999900000,99999871764842,99999743601494,99999615409958,99999487190239,99999358942339,99999230666262,99999102362010,99998974029587,99998845668997,99998717280242,99998588863326,99998460418252,99998331945023,99998203443643,99998074914115,99997946356442,99997817770627,99997689156673,99997560514584,99997431844363,99997303146013,99997174419537,99997045664939,99996916882222,99996788071389,99996659232443,99996530365388,99996401470226,99996272546962,99996143595598,99996014616137,99995885608583]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (0+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(14675430044459158303480/17968024086054975895977:Fraction),(73370843341582647488636/89838370430276629479885:Fraction),(2717205090691346165776/3327282238158458499255:Fraction),(73358231341911315520864/89834870430280129479885:Fraction),(73351925021334618858287/89833120430281879479885:Fraction),(8149513298741367296284/9981263381142625497765:Fraction),(1982143657945529008096/2427827579196902148105:Fraction),(543207487300567453568/665391632816941699851:Fraction),(54926371545666049726/67285483468381183131:Fraction),(1705125633242909476997/2088938847216061150695:Fraction),(8146011048175224094876/9980291158921375497765:Fraction),(3490847448767067527416/4277184306204482356185:Fraction),(24433831467626751666644/29939706810098626493295:Fraction),(73295192168110146899083/89817370430297629479885:Fraction),(2714403322956068510884/3326504460381458499255:Fraction),(14656517651975341047386/17962774086060225895977:Fraction),(73276287788357586141508/89812120430302879479885:Fraction),(8141109678157210264688/9978930047811625497765:Fraction),(10466240886437584205527/12829802918615197068555:Fraction),(1162815655480126775098/1425505879846160785395:Fraction),(1627801941645076453720/1995669342895775099553:Fraction),(24414929413167880045169/29934456810103876493295:Fraction),(2712536625618075611218/3325985941863458499255:Fraction),(659749464257537222812/809007841714550716035:Fraction),(8136210351362027736952/9977568936701875497765:Fraction),(14643919115748576932630/17959274086063725895977:Fraction),(3486347513431189637273/4275934306205732356185:Fraction),(73207000974258698252254/89792870430322129479885:Fraction),(73200705155411575226056/89791120430323879479885:Fraction),(1161816017833285229996/1425228102068660785395:Fraction),(73188114080620848014504/89787620430327379479885:Fraction),(6652892620430401586539/8162351857302648134535:Fraction)]
abbrev p1 := params 0
abbrev ray1 := rays 0
def bank1 : Fin 1 → Cell := oneBank p1 ray1
theorem signs1 : ∀ j, Signs p1 (bank1 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2 := params 1
abbrev ray2 := rays 1
def bank2 : Fin 1 → Cell := oneBank p2 ray2
theorem signs2 : ∀ j, Signs p2 (bank2 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3 := params 2
abbrev ray3 := rays 2
def bank3 : Fin 1 → Cell := oneBank p3 ray3
theorem signs3 : ∀ j, Signs p3 (bank3 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4 := params 3
abbrev ray4 := rays 3
def bank4 : Fin 1 → Cell := oneBank p4 ray4
theorem signs4 : ∀ j, Signs p4 (bank4 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5 := params 4
abbrev ray5 := rays 4
def bank5 : Fin 1 → Cell := oneBank p5 ray5
theorem signs5 : ∀ j, Signs p5 (bank5 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6 := params 5
abbrev ray6 := rays 5
def bank6 : Fin 1 → Cell := oneBank p6 ray6
theorem signs6 : ∀ j, Signs p6 (bank6 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7 := params 6
abbrev ray7 := rays 6
def bank7 : Fin 1 → Cell := oneBank p7 ray7
theorem signs7 : ∀ j, Signs p7 (bank7 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8 := params 7
abbrev ray8 := rays 7
def bank8 : Fin 1 → Cell := oneBank p8 ray8
theorem signs8 : ∀ j, Signs p8 (bank8 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9 := params 8
abbrev ray9 := rays 8
def bank9 : Fin 1 → Cell := oneBank p9 ray9
theorem signs9 : ∀ j, Signs p9 (bank9 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10 := params 9
abbrev ray10 := rays 9
def bank10 : Fin 1 → Cell := oneBank p10 ray10
theorem signs10 : ∀ j, Signs p10 (bank10 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11 := params 10
abbrev ray11 := rays 10
def bank11 : Fin 1 → Cell := oneBank p11 ray11
theorem signs11 : ∀ j, Signs p11 (bank11 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12 := params 11
abbrev ray12 := rays 11
def bank12 : Fin 1 → Cell := oneBank p12 ray12
theorem signs12 : ∀ j, Signs p12 (bank12 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13 := params 12
abbrev ray13 := rays 12
def bank13 : Fin 1 → Cell := oneBank p13 ray13
theorem signs13 : ∀ j, Signs p13 (bank13 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14 := params 13
abbrev ray14 := rays 13
def bank14 : Fin 1 → Cell := oneBank p14 ray14
theorem signs14 : ∀ j, Signs p14 (bank14 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15 := params 14
abbrev ray15 := rays 14
def bank15 : Fin 1 → Cell := oneBank p15 ray15
theorem signs15 : ∀ j, Signs p15 (bank15 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16 := params 15
abbrev ray16 := rays 15
def bank16 : Fin 1 → Cell := oneBank p16 ray16
theorem signs16 : ∀ j, Signs p16 (bank16 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17 := params 16
abbrev ray17 := rays 16
def bank17 : Fin 1 → Cell := oneBank p17 ray17
theorem signs17 : ∀ j, Signs p17 (bank17 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p18 := params 17
abbrev ray18 := rays 17
def bank18 : Fin 1 → Cell := oneBank p18 ray18
theorem signs18 : ∀ j, Signs p18 (bank18 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p19 := params 18
abbrev ray19 := rays 18
def bank19 : Fin 1 → Cell := oneBank p19 ray19
theorem signs19 : ∀ j, Signs p19 (bank19 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p20 := params 19
abbrev ray20 := rays 19
def bank20 : Fin 1 → Cell := oneBank p20 ray20
theorem signs20 : ∀ j, Signs p20 (bank20 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p21 := params 20
abbrev ray21 := rays 20
def bank21 : Fin 1 → Cell := oneBank p21 ray21
theorem signs21 : ∀ j, Signs p21 (bank21 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p22 := params 21
abbrev ray22 := rays 21
def bank22 : Fin 1 → Cell := oneBank p22 ray22
theorem signs22 : ∀ j, Signs p22 (bank22 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p23 := params 22
abbrev ray23 := rays 22
def bank23 : Fin 1 → Cell := oneBank p23 ray23
theorem signs23 : ∀ j, Signs p23 (bank23 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p24 := params 23
abbrev ray24 := rays 23
def bank24 : Fin 1 → Cell := oneBank p24 ray24
theorem signs24 : ∀ j, Signs p24 (bank24 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p25 := params 24
abbrev ray25 := rays 24
def bank25 : Fin 1 → Cell := oneBank p25 ray25
theorem signs25 : ∀ j, Signs p25 (bank25 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p26 := params 25
abbrev ray26 := rays 25
def bank26 : Fin 1 → Cell := oneBank p26 ray26
theorem signs26 : ∀ j, Signs p26 (bank26 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p27 := params 26
abbrev ray27 := rays 26
def bank27 : Fin 1 → Cell := oneBank p27 ray27
theorem signs27 : ∀ j, Signs p27 (bank27 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p28 := params 27
abbrev ray28 := rays 27
def bank28 : Fin 1 → Cell := oneBank p28 ray28
theorem signs28 : ∀ j, Signs p28 (bank28 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p29 := params 28
abbrev ray29 := rays 28
def bank29 : Fin 1 → Cell := oneBank p29 ray29
theorem signs29 : ∀ j, Signs p29 (bank29 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p30 := params 29
abbrev ray30 := rays 29
def bank30 : Fin 1 → Cell := oneBank p30 ray30
theorem signs30 : ∀ j, Signs p30 (bank30 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p31 := params 30
abbrev ray31 := rays 30
def bank31 : Fin 1 → Cell := oneBank p31 ray31
theorem signs31 : ∀ j, Signs p31 (bank31 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p32 := params 31
abbrev ray32 := rays 31
def bank32 : Fin 1 → Cell := oneBank p32 ray32
theorem signs32 : ∀ j, Signs p32 (bank32 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00001_00032
