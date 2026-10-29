/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00961_00992
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99864459160007,99864305326124,99864151466769,99863997581943,99863843671650,99863689735893,99863535774673,99863381787994,99863227775857,99863073738265,99862919675220,99862765586725,99862611472783,99862457333395,99862303168564,99862148978294,99861994762586,99861840521442,99861686254865,99861531962858,99861377645423,99861223302563,99861068934279,99860914540574,99860760121451,99860605676913,99860451206961,99860296711598,99860142190827,99859987644649,99859833073068,99859678476086,99859523853705]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (960+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(9643980719598465540503/12594302918850697068555:Fraction),(67501950928625513627104/88158370431956629479885:Fraction),(499970650729948473604/653012003199691699851:Fraction),(22496707788568062044593/29384956810653376493295:Fraction),(13496842225411637339600/17630624086392375895977:Fraction),(3213252319112163797359/4197684306283982356185:Fraction),(7496931787622884238026/9794402270218375497765:Fraction),(22488824834841854294672/29382623477322376493295:Fraction),(7495618216574118011693/9794013381329875497765:Fraction),(1037763895490073035878/1356067237414932761229:Fraction),(121529265365044666130/158815532309860143207:Fraction),(4496188825144926433165/5876058028798275298659:Fraction),(9633846215090313187478/12591302918853697068555:Fraction),(13486202889447913781519/17627474086395525895977:Fraction),(4495007013467223651080/5875708028798625298659:Fraction),(166467153051280160032/217614494893780566617:Fraction),(13482657716548399051936/17626424086396575895977:Fraction),(202424568194549701684/264655767063016905345:Fraction),(4493431657596848949463/5875241362132425298659:Fraction),(4493037888828445241156/5875124695465875298659:Fraction),(7487740179357559546339/9791680047998875497765:Fraction),(13476751185048221058404/17624674086398325895977:Fraction),(21328854468359812534/27895416407721867515:Fraction),(831752424929200589952/1087899634962902833085:Fraction),(67366041386403213591262/88118120431996879479885:Fraction),(2172907657513995682661/2842463562322536434835:Fraction),(22451411469636651004201/29371540144000126493295:Fraction),(22449443749466339482424/29370956810667376493295:Fraction),(13468485580282672546897/17622224086400775895977:Fraction),(7481836175997666039362/9789930048000625497765:Fraction),(121316440173247092320/158752469246860143207:Fraction),(7480524757993570910432/9789541159112125497765:Fraction)]
abbrev p961 := params 0
abbrev ray961 := rays 0
def bank961 : Fin 1 → Cell := oneBank p961 ray961
theorem signs961 : ∀ j, Signs p961 (bank961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p962 := params 1
abbrev ray962 := rays 1
def bank962 : Fin 1 → Cell := oneBank p962 ray962
theorem signs962 : ∀ j, Signs p962 (bank962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p963 := params 2
abbrev ray963 := rays 2
def bank963 : Fin 1 → Cell := oneBank p963 ray963
theorem signs963 : ∀ j, Signs p963 (bank963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p964 := params 3
abbrev ray964 := rays 3
def bank964 : Fin 1 → Cell := oneBank p964 ray964
theorem signs964 : ∀ j, Signs p964 (bank964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p965 := params 4
abbrev ray965 := rays 4
def bank965 : Fin 1 → Cell := oneBank p965 ray965
theorem signs965 : ∀ j, Signs p965 (bank965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p966 := params 5
abbrev ray966 := rays 5
def bank966 : Fin 1 → Cell := oneBank p966 ray966
theorem signs966 : ∀ j, Signs p966 (bank966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p967 := params 6
abbrev ray967 := rays 6
def bank967 : Fin 1 → Cell := oneBank p967 ray967
theorem signs967 : ∀ j, Signs p967 (bank967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p968 := params 7
abbrev ray968 := rays 7
def bank968 : Fin 1 → Cell := oneBank p968 ray968
theorem signs968 : ∀ j, Signs p968 (bank968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p969 := params 8
abbrev ray969 := rays 8
def bank969 : Fin 1 → Cell := oneBank p969 ray969
theorem signs969 : ∀ j, Signs p969 (bank969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p970 := params 9
abbrev ray970 := rays 9
def bank970 : Fin 1 → Cell := oneBank p970 ray970
theorem signs970 : ∀ j, Signs p970 (bank970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p971 := params 10
abbrev ray971 := rays 10
def bank971 : Fin 1 → Cell := oneBank p971 ray971
theorem signs971 : ∀ j, Signs p971 (bank971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p972 := params 11
abbrev ray972 := rays 11
def bank972 : Fin 1 → Cell := oneBank p972 ray972
theorem signs972 : ∀ j, Signs p972 (bank972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p973 := params 12
abbrev ray973 := rays 12
def bank973 : Fin 1 → Cell := oneBank p973 ray973
theorem signs973 : ∀ j, Signs p973 (bank973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p974 := params 13
abbrev ray974 := rays 13
def bank974 : Fin 1 → Cell := oneBank p974 ray974
theorem signs974 : ∀ j, Signs p974 (bank974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p975 := params 14
abbrev ray975 := rays 14
def bank975 : Fin 1 → Cell := oneBank p975 ray975
theorem signs975 : ∀ j, Signs p975 (bank975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p976 := params 15
abbrev ray976 := rays 15
def bank976 : Fin 1 → Cell := oneBank p976 ray976
theorem signs976 : ∀ j, Signs p976 (bank976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p977 := params 16
abbrev ray977 := rays 16
def bank977 : Fin 1 → Cell := oneBank p977 ray977
theorem signs977 : ∀ j, Signs p977 (bank977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p978 := params 17
abbrev ray978 := rays 17
def bank978 : Fin 1 → Cell := oneBank p978 ray978
theorem signs978 : ∀ j, Signs p978 (bank978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p979 := params 18
abbrev ray979 := rays 18
def bank979 : Fin 1 → Cell := oneBank p979 ray979
theorem signs979 : ∀ j, Signs p979 (bank979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p980 := params 19
abbrev ray980 := rays 19
def bank980 : Fin 1 → Cell := oneBank p980 ray980
theorem signs980 : ∀ j, Signs p980 (bank980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p981 := params 20
abbrev ray981 := rays 20
def bank981 : Fin 1 → Cell := oneBank p981 ray981
theorem signs981 : ∀ j, Signs p981 (bank981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p982 := params 21
abbrev ray982 := rays 21
def bank982 : Fin 1 → Cell := oneBank p982 ray982
theorem signs982 : ∀ j, Signs p982 (bank982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p983 := params 22
abbrev ray983 := rays 22
def bank983 : Fin 1 → Cell := oneBank p983 ray983
theorem signs983 : ∀ j, Signs p983 (bank983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p984 := params 23
abbrev ray984 := rays 23
def bank984 : Fin 1 → Cell := oneBank p984 ray984
theorem signs984 : ∀ j, Signs p984 (bank984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p985 := params 24
abbrev ray985 := rays 24
def bank985 : Fin 1 → Cell := oneBank p985 ray985
theorem signs985 : ∀ j, Signs p985 (bank985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p986 := params 25
abbrev ray986 := rays 25
def bank986 : Fin 1 → Cell := oneBank p986 ray986
theorem signs986 : ∀ j, Signs p986 (bank986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p987 := params 26
abbrev ray987 := rays 26
def bank987 : Fin 1 → Cell := oneBank p987 ray987
theorem signs987 : ∀ j, Signs p987 (bank987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p988 := params 27
abbrev ray988 := rays 27
def bank988 : Fin 1 → Cell := oneBank p988 ray988
theorem signs988 : ∀ j, Signs p988 (bank988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p989 := params 28
abbrev ray989 := rays 28
def bank989 : Fin 1 → Cell := oneBank p989 ray989
theorem signs989 : ∀ j, Signs p989 (bank989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p990 := params 29
abbrev ray990 := rays 29
def bank990 : Fin 1 → Cell := oneBank p990 ray990
theorem signs990 : ∀ j, Signs p990 (bank990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p991 := params 30
abbrev ray991 := rays 30
def bank991 : Fin 1 → Cell := oneBank p991 ray991
theorem signs991 : ∀ j, Signs p991 (bank991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p992 := params 31
abbrev ray992 := rays 31
def bank992 : Fin 1 → Cell := oneBank p992 ray992
theorem signs992 : ∀ j, Signs p992 (bank992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00961_00992
