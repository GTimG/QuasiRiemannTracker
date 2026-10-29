/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00033_00064
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99995885608583,99995756572939,99995627509208,99995498417393,99995369297498,99995240149526,99995110973480,99994981769362,99994852537177,99994723276928,99994593988618,99994464672249,99994335327826,99994205955351,99994076554828,99993947126260,99993817669650,99993688185001,99993558672317,99993429131600,99993299562854,99993169966082,99993040341287,99992910688473,99992781007643,99992651298799,99992521561945,99992391797085,99992262004222,99992132183358,99992002334497,99991872457642,99991742552796]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (32+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(2710204568735310627019/3325337793715958499255:Fraction),(8129914319569929800996/9975818936703625497765:Fraction),(73162935385621157697896/89780620430334379479885:Fraction),(24385547227406928397588/29926290143445376493295:Fraction),(3483349893616378541392/4275100972873232356185:Fraction),(73144054839001407148816/89775370430339629479885:Fraction),(1625283620032265287006/1994969342896475099553:Fraction),(73131470751127126620764/89771870430343129479885:Fraction),(14625035677608787835105/17954024086068975895977:Fraction),(902702308820645286812/1108251486794402833085:Fraction),(6646599693679170559672/8160601857304398134535:Fraction),(73106306033812190428586/89764870430350129479885:Fraction),(8122223913834796223576/9973680047816875497765:Fraction),(4872915026993436345845/5984091362023575298659:Fraction),(73087436575037350240886/89759620430355379479885:Fraction),(4872076502175675802526/5983858028690475298659:Fraction),(4871657218513953108100/5983741362023925298659:Fraction),(73068570012647965211944/89754370430360629479885:Fraction),(24354094245837049196672/29917540143454126493295:Fraction),(394897271621367484240/485139840164130429621:Fraction),(24349902917469073032736/29916373476788626493295:Fraction),(24347807347499900683688/29915790143455876493295:Fraction),(73037135120244809774399/89745620430369379479885:Fraction),(73030849188120611773379/89743870430371129479885:Fraction),(540922698119894897032/664756447632391699851:Fraction),(1973467002486644824939/2425415417037152148105:Fraction),(14602398745119279173866/17947724086075275895977:Fraction),(4867047289966305699698/5982458028691875298659:Fraction),(72999425963759113467112/89735120430379879479885:Fraction),(4866209491059754366496/5982224695358775298659:Fraction),(24328952851973940995261/29910540143461126493295:Fraction),(72980575736430607315148/89729870430385129479885:Fraction)]
abbrev p33 := params 0
abbrev ray33 := rays 0
def bank33 : Fin 1 → Cell := oneBank p33 ray33
theorem signs33 : ∀ j, Signs p33 (bank33 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p34 := params 1
abbrev ray34 := rays 1
def bank34 : Fin 1 → Cell := oneBank p34 ray34
theorem signs34 : ∀ j, Signs p34 (bank34 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p35 := params 2
abbrev ray35 := rays 2
def bank35 : Fin 1 → Cell := oneBank p35 ray35
theorem signs35 : ∀ j, Signs p35 (bank35 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p36 := params 3
abbrev ray36 := rays 3
def bank36 : Fin 1 → Cell := oneBank p36 ray36
theorem signs36 : ∀ j, Signs p36 (bank36 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p37 := params 4
abbrev ray37 := rays 4
def bank37 : Fin 1 → Cell := oneBank p37 ray37
theorem signs37 : ∀ j, Signs p37 (bank37 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p38 := params 5
abbrev ray38 := rays 5
def bank38 : Fin 1 → Cell := oneBank p38 ray38
theorem signs38 : ∀ j, Signs p38 (bank38 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p39 := params 6
abbrev ray39 := rays 6
def bank39 : Fin 1 → Cell := oneBank p39 ray39
theorem signs39 : ∀ j, Signs p39 (bank39 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p40 := params 7
abbrev ray40 := rays 7
def bank40 : Fin 1 → Cell := oneBank p40 ray40
theorem signs40 : ∀ j, Signs p40 (bank40 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p41 := params 8
abbrev ray41 := rays 8
def bank41 : Fin 1 → Cell := oneBank p41 ray41
theorem signs41 : ∀ j, Signs p41 (bank41 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p42 := params 9
abbrev ray42 := rays 9
def bank42 : Fin 1 → Cell := oneBank p42 ray42
theorem signs42 : ∀ j, Signs p42 (bank42 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p43 := params 10
abbrev ray43 := rays 10
def bank43 : Fin 1 → Cell := oneBank p43 ray43
theorem signs43 : ∀ j, Signs p43 (bank43 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p44 := params 11
abbrev ray44 := rays 11
def bank44 : Fin 1 → Cell := oneBank p44 ray44
theorem signs44 : ∀ j, Signs p44 (bank44 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p45 := params 12
abbrev ray45 := rays 12
def bank45 : Fin 1 → Cell := oneBank p45 ray45
theorem signs45 : ∀ j, Signs p45 (bank45 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p46 := params 13
abbrev ray46 := rays 13
def bank46 : Fin 1 → Cell := oneBank p46 ray46
theorem signs46 : ∀ j, Signs p46 (bank46 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p47 := params 14
abbrev ray47 := rays 14
def bank47 : Fin 1 → Cell := oneBank p47 ray47
theorem signs47 : ∀ j, Signs p47 (bank47 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p48 := params 15
abbrev ray48 := rays 15
def bank48 : Fin 1 → Cell := oneBank p48 ray48
theorem signs48 : ∀ j, Signs p48 (bank48 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p49 := params 16
abbrev ray49 := rays 16
def bank49 : Fin 1 → Cell := oneBank p49 ray49
theorem signs49 : ∀ j, Signs p49 (bank49 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p50 := params 17
abbrev ray50 := rays 17
def bank50 : Fin 1 → Cell := oneBank p50 ray50
theorem signs50 : ∀ j, Signs p50 (bank50 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p51 := params 18
abbrev ray51 := rays 18
def bank51 : Fin 1 → Cell := oneBank p51 ray51
theorem signs51 : ∀ j, Signs p51 (bank51 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p52 := params 19
abbrev ray52 := rays 19
def bank52 : Fin 1 → Cell := oneBank p52 ray52
theorem signs52 : ∀ j, Signs p52 (bank52 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p53 := params 20
abbrev ray53 := rays 20
def bank53 : Fin 1 → Cell := oneBank p53 ray53
theorem signs53 : ∀ j, Signs p53 (bank53 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p54 := params 21
abbrev ray54 := rays 21
def bank54 : Fin 1 → Cell := oneBank p54 ray54
theorem signs54 : ∀ j, Signs p54 (bank54 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p55 := params 22
abbrev ray55 := rays 22
def bank55 : Fin 1 → Cell := oneBank p55 ray55
theorem signs55 : ∀ j, Signs p55 (bank55 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p56 := params 23
abbrev ray56 := rays 23
def bank56 : Fin 1 → Cell := oneBank p56 ray56
theorem signs56 : ∀ j, Signs p56 (bank56 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p57 := params 24
abbrev ray57 := rays 24
def bank57 : Fin 1 → Cell := oneBank p57 ray57
theorem signs57 : ∀ j, Signs p57 (bank57 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p58 := params 25
abbrev ray58 := rays 25
def bank58 : Fin 1 → Cell := oneBank p58 ray58
theorem signs58 : ∀ j, Signs p58 (bank58 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p59 := params 26
abbrev ray59 := rays 26
def bank59 : Fin 1 → Cell := oneBank p59 ray59
theorem signs59 : ∀ j, Signs p59 (bank59 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p60 := params 27
abbrev ray60 := rays 27
def bank60 : Fin 1 → Cell := oneBank p60 ray60
theorem signs60 : ∀ j, Signs p60 (bank60 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p61 := params 28
abbrev ray61 := rays 28
def bank61 : Fin 1 → Cell := oneBank p61 ray61
theorem signs61 : ∀ j, Signs p61 (bank61 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p62 := params 29
abbrev ray62 := rays 29
def bank62 : Fin 1 → Cell := oneBank p62 ray62
theorem signs62 : ∀ j, Signs p62 (bank62 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p63 := params 30
abbrev ray63 := rays 30
def bank63 : Fin 1 → Cell := oneBank p63 ray63
theorem signs63 : ∀ j, Signs p63 (bank63 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p64 := params 31
abbrev ray64 := rays 31
def bank64 : Fin 1 → Cell := oneBank p64 ray64
theorem signs64 : ∀ j, Signs p64 (bank64 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00033_00064
