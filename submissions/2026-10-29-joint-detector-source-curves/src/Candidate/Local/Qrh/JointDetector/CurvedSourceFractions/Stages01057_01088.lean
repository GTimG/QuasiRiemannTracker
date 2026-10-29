/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01057_01088
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99849575303033,99849419034933,99849262741594,99849106423018,99848950079207,99848793710164,99848637315891,99848480896391,99848324451666,99848167981718,99848011486550,99847854966164,99847698420563,99847541849749,99847385253725,99847228632492,99847071986054,99846915314412,99846758617569,99846601895527,99846445148289,99846288375857,99846131578233,99845974755420,99845817907420,99845661034236,99845504135870,99845347212325,99845190263602,99845033289704,99844876290633,99844719266392,99844562216984]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1056+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(66942043306584551019907/87992120432122879479885:Fraction),(13387233946512635900848/17598074086424925895977:Fraction),(7436699687874505959632/9776513381347375497765:Fraction),(22308141488182600432544/29328956810709376493295:Fraction),(66918552770632672073569/87985120432129879479885:Fraction),(4460845392809267252276/5865558028808775298659:Fraction),(66906810046132989214984/87981620432133379479885:Fraction),(66900939015600018095558/87979870432135129479885:Fraction),(22298356339211566430756/29326040144045626493295:Fraction),(602605394911647274304/792579913803050716035:Fraction),(13376665937079728947520/17594924086428075895977:Fraction),(4458497356745298145592/5864858028809475298659:Fraction),(66871592049687933577861/87971120432143879479885:Fraction),(66865723563822978440426/87969370432145629479885:Fraction),(4457323740717708670760/5864508028809825298659:Fraction),(4456932564892350343396/5864391362143275298659:Fraction),(66848121868892448038656/87964120432150879479885:Fraction),(22280751693376049466832/29320790144050876493295:Fraction),(66836389324330212517612/87960620432154379479885:Fraction),(66830523384312308463776/87958870432156129479885:Fraction),(22274886159113568556537/29319040144052626493295:Fraction),(4454586225746709945418/5863691362143975298659:Fraction),(66812929328185666837336/87953620432161379479885:Fraction),(1484601473407788895370/1954486009603625099553:Fraction),(13360240375425358508558/17590024086432975895977:Fraction),(66795339701459572065286/87948370432166629479885:Fraction),(1484210580542819748064/1954369342937075099553:Fraction),(13356722959611799841915/17588974086434025895977:Fraction),(66777752070347565414796/87943120432171879479885:Fraction),(85935510416226597878/113180656926864388005:Fraction),(13353206186508856740523/17587924086435075895977:Fraction),(804339398647811098154/1059492414845507584095:Fraction)]
abbrev p1057 := params 0
abbrev ray1057 := rays 0
def bank1057 : Fin 1 → Cell := oneBank p1057 ray1057
theorem signs1057 : ∀ j, Signs p1057 (bank1057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1058 := params 1
abbrev ray1058 := rays 1
def bank1058 : Fin 1 → Cell := oneBank p1058 ray1058
theorem signs1058 : ∀ j, Signs p1058 (bank1058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1059 := params 2
abbrev ray1059 := rays 2
def bank1059 : Fin 1 → Cell := oneBank p1059 ray1059
theorem signs1059 : ∀ j, Signs p1059 (bank1059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1060 := params 3
abbrev ray1060 := rays 3
def bank1060 : Fin 1 → Cell := oneBank p1060 ray1060
theorem signs1060 : ∀ j, Signs p1060 (bank1060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1061 := params 4
abbrev ray1061 := rays 4
def bank1061 : Fin 1 → Cell := oneBank p1061 ray1061
theorem signs1061 : ∀ j, Signs p1061 (bank1061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1062 := params 5
abbrev ray1062 := rays 5
def bank1062 : Fin 1 → Cell := oneBank p1062 ray1062
theorem signs1062 : ∀ j, Signs p1062 (bank1062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1063 := params 6
abbrev ray1063 := rays 6
def bank1063 : Fin 1 → Cell := oneBank p1063 ray1063
theorem signs1063 : ∀ j, Signs p1063 (bank1063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1064 := params 7
abbrev ray1064 := rays 7
def bank1064 : Fin 1 → Cell := oneBank p1064 ray1064
theorem signs1064 : ∀ j, Signs p1064 (bank1064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1065 := params 8
abbrev ray1065 := rays 8
def bank1065 : Fin 1 → Cell := oneBank p1065 ray1065
theorem signs1065 : ∀ j, Signs p1065 (bank1065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1066 := params 9
abbrev ray1066 := rays 9
def bank1066 : Fin 1 → Cell := oneBank p1066 ray1066
theorem signs1066 : ∀ j, Signs p1066 (bank1066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1067 := params 10
abbrev ray1067 := rays 10
def bank1067 : Fin 1 → Cell := oneBank p1067 ray1067
theorem signs1067 : ∀ j, Signs p1067 (bank1067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1068 := params 11
abbrev ray1068 := rays 11
def bank1068 : Fin 1 → Cell := oneBank p1068 ray1068
theorem signs1068 : ∀ j, Signs p1068 (bank1068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1069 := params 12
abbrev ray1069 := rays 12
def bank1069 : Fin 1 → Cell := oneBank p1069 ray1069
theorem signs1069 : ∀ j, Signs p1069 (bank1069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1070 := params 13
abbrev ray1070 := rays 13
def bank1070 : Fin 1 → Cell := oneBank p1070 ray1070
theorem signs1070 : ∀ j, Signs p1070 (bank1070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1071 := params 14
abbrev ray1071 := rays 14
def bank1071 : Fin 1 → Cell := oneBank p1071 ray1071
theorem signs1071 : ∀ j, Signs p1071 (bank1071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1072 := params 15
abbrev ray1072 := rays 15
def bank1072 : Fin 1 → Cell := oneBank p1072 ray1072
theorem signs1072 : ∀ j, Signs p1072 (bank1072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1073 := params 16
abbrev ray1073 := rays 16
def bank1073 : Fin 1 → Cell := oneBank p1073 ray1073
theorem signs1073 : ∀ j, Signs p1073 (bank1073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1074 := params 17
abbrev ray1074 := rays 17
def bank1074 : Fin 1 → Cell := oneBank p1074 ray1074
theorem signs1074 : ∀ j, Signs p1074 (bank1074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1075 := params 18
abbrev ray1075 := rays 18
def bank1075 : Fin 1 → Cell := oneBank p1075 ray1075
theorem signs1075 : ∀ j, Signs p1075 (bank1075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1076 := params 19
abbrev ray1076 := rays 19
def bank1076 : Fin 1 → Cell := oneBank p1076 ray1076
theorem signs1076 : ∀ j, Signs p1076 (bank1076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1077 := params 20
abbrev ray1077 := rays 20
def bank1077 : Fin 1 → Cell := oneBank p1077 ray1077
theorem signs1077 : ∀ j, Signs p1077 (bank1077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1078 := params 21
abbrev ray1078 := rays 21
def bank1078 : Fin 1 → Cell := oneBank p1078 ray1078
theorem signs1078 : ∀ j, Signs p1078 (bank1078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1079 := params 22
abbrev ray1079 := rays 22
def bank1079 : Fin 1 → Cell := oneBank p1079 ray1079
theorem signs1079 : ∀ j, Signs p1079 (bank1079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1080 := params 23
abbrev ray1080 := rays 23
def bank1080 : Fin 1 → Cell := oneBank p1080 ray1080
theorem signs1080 : ∀ j, Signs p1080 (bank1080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1081 := params 24
abbrev ray1081 := rays 24
def bank1081 : Fin 1 → Cell := oneBank p1081 ray1081
theorem signs1081 : ∀ j, Signs p1081 (bank1081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1082 := params 25
abbrev ray1082 := rays 25
def bank1082 : Fin 1 → Cell := oneBank p1082 ray1082
theorem signs1082 : ∀ j, Signs p1082 (bank1082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1083 := params 26
abbrev ray1083 := rays 26
def bank1083 : Fin 1 → Cell := oneBank p1083 ray1083
theorem signs1083 : ∀ j, Signs p1083 (bank1083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1084 := params 27
abbrev ray1084 := rays 27
def bank1084 : Fin 1 → Cell := oneBank p1084 ray1084
theorem signs1084 : ∀ j, Signs p1084 (bank1084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1085 := params 28
abbrev ray1085 := rays 28
def bank1085 : Fin 1 → Cell := oneBank p1085 ray1085
theorem signs1085 : ∀ j, Signs p1085 (bank1085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1086 := params 29
abbrev ray1086 := rays 29
def bank1086 : Fin 1 → Cell := oneBank p1086 ray1086
theorem signs1086 : ∀ j, Signs p1086 (bank1086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1087 := params 30
abbrev ray1087 := rays 30
def bank1087 : Fin 1 → Cell := oneBank p1087 ray1087
theorem signs1087 : ∀ j, Signs p1087 (bank1087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1088 := params 31
abbrev ray1088 := rays 31
def bank1088 : Fin 1 → Cell := oneBank p1088 ray1088
theorem signs1088 : ∀ j, Signs p1088 (bank1088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01057_01088
