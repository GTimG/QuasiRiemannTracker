/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01025_01056
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99854562541542,99854407082367,99854251597875,99854096088070,99853940552953,99853784992527,99853629406795,99853473795758,99853318159420,99853162497782,99853006810847,99852851098618,99852695361096,99852539598285,99852383810187,99852227996804,99852072158139,99851916294193,99851760404970,99851604490471,99851448550700,99851292585658,99851136595348,99850980579772,99850824538933,99850668472833,99850512381475,99850356264861,99850200122993,99850043955874,99849887763506,99849731545892,99849575303033]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1024+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(13426042792333463057056/17609624086413375895977:Fraction),(165739078623101586642/217398445511280566617:Fraction),(4474562716939592897290/5869641362138025298659:Fraction),(4474170298691956032256/5869524695471475298659:Fraction),(22368889745931311294459/29347040144024626493295:Fraction),(67100783809806813567332/88039370432075629479885:Fraction),(1916997126086577393118/2515360583773639413711:Fraction),(7454334981211385656064/9781763381342125497765:Fraction),(4472208752004363151678/5868941362138725298659:Fraction),(4471816502928601322336/5868824695472175298659:Fraction),(7452373735833933087577/9781180048009375497765:Fraction),(13413096389829824939416/17605774086417225895977:Fraction),(1490213308308872822924/1956158231824175099553:Fraction),(4470247788675052031539/5868358028805975298659:Fraction),(563427191746910635159/739694289345305709915:Fraction),(13408390924098935217626/17604374086418625895977:Fraction),(1064064673884400306034/1397144768763410785395:Fraction),(67030194103846020800623/88018370432096629479885:Fraction),(4468287652311012948220/5867774695473225298659:Fraction),(3191354060973443158769/4191184306290482356185:Fraction),(13402511361597983505940/17602624086420375895977:Fraction),(67006678150547137865452/88011370432103629479885:Fraction),(496302226110769008442/651923114311891699851:Fraction),(5153455593417058794634/6769836187085163806145:Fraction),(66989044718963163928231/88006120432108879479885:Fraction),(637934942593616233787/838136861258196471237:Fraction),(13395458364793046664980/17600524086422475895977:Fraction),(1810038295257687391363/2378401903570652148105:Fraction),(22321846874464886152129/29333040144038626493295:Fraction),(22319888451456617793944/29332456810705876493295:Fraction),(66953791117513693825888/87995620432119379479885:Fraction),(826517490073152459996/1086344079408902833085:Fraction)]
abbrev p1025 := params 0
abbrev ray1025 := rays 0
def bank1025 : Fin 1 → Cell := oneBank p1025 ray1025
theorem signs1025 : ∀ j, Signs p1025 (bank1025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1026 := params 1
abbrev ray1026 := rays 1
def bank1026 : Fin 1 → Cell := oneBank p1026 ray1026
theorem signs1026 : ∀ j, Signs p1026 (bank1026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1027 := params 2
abbrev ray1027 := rays 2
def bank1027 : Fin 1 → Cell := oneBank p1027 ray1027
theorem signs1027 : ∀ j, Signs p1027 (bank1027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1028 := params 3
abbrev ray1028 := rays 3
def bank1028 : Fin 1 → Cell := oneBank p1028 ray1028
theorem signs1028 : ∀ j, Signs p1028 (bank1028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1029 := params 4
abbrev ray1029 := rays 4
def bank1029 : Fin 1 → Cell := oneBank p1029 ray1029
theorem signs1029 : ∀ j, Signs p1029 (bank1029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1030 := params 5
abbrev ray1030 := rays 5
def bank1030 : Fin 1 → Cell := oneBank p1030 ray1030
theorem signs1030 : ∀ j, Signs p1030 (bank1030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1031 := params 6
abbrev ray1031 := rays 6
def bank1031 : Fin 1 → Cell := oneBank p1031 ray1031
theorem signs1031 : ∀ j, Signs p1031 (bank1031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1032 := params 7
abbrev ray1032 := rays 7
def bank1032 : Fin 1 → Cell := oneBank p1032 ray1032
theorem signs1032 : ∀ j, Signs p1032 (bank1032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1033 := params 8
abbrev ray1033 := rays 8
def bank1033 : Fin 1 → Cell := oneBank p1033 ray1033
theorem signs1033 : ∀ j, Signs p1033 (bank1033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1034 := params 9
abbrev ray1034 := rays 9
def bank1034 : Fin 1 → Cell := oneBank p1034 ray1034
theorem signs1034 : ∀ j, Signs p1034 (bank1034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1035 := params 10
abbrev ray1035 := rays 10
def bank1035 : Fin 1 → Cell := oneBank p1035 ray1035
theorem signs1035 : ∀ j, Signs p1035 (bank1035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1036 := params 11
abbrev ray1036 := rays 11
def bank1036 : Fin 1 → Cell := oneBank p1036 ray1036
theorem signs1036 : ∀ j, Signs p1036 (bank1036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1037 := params 12
abbrev ray1037 := rays 12
def bank1037 : Fin 1 → Cell := oneBank p1037 ray1037
theorem signs1037 : ∀ j, Signs p1037 (bank1037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1038 := params 13
abbrev ray1038 := rays 13
def bank1038 : Fin 1 → Cell := oneBank p1038 ray1038
theorem signs1038 : ∀ j, Signs p1038 (bank1038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1039 := params 14
abbrev ray1039 := rays 14
def bank1039 : Fin 1 → Cell := oneBank p1039 ray1039
theorem signs1039 : ∀ j, Signs p1039 (bank1039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1040 := params 15
abbrev ray1040 := rays 15
def bank1040 : Fin 1 → Cell := oneBank p1040 ray1040
theorem signs1040 : ∀ j, Signs p1040 (bank1040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1041 := params 16
abbrev ray1041 := rays 16
def bank1041 : Fin 1 → Cell := oneBank p1041 ray1041
theorem signs1041 : ∀ j, Signs p1041 (bank1041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1042 := params 17
abbrev ray1042 := rays 17
def bank1042 : Fin 1 → Cell := oneBank p1042 ray1042
theorem signs1042 : ∀ j, Signs p1042 (bank1042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1043 := params 18
abbrev ray1043 := rays 18
def bank1043 : Fin 1 → Cell := oneBank p1043 ray1043
theorem signs1043 : ∀ j, Signs p1043 (bank1043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1044 := params 19
abbrev ray1044 := rays 19
def bank1044 : Fin 1 → Cell := oneBank p1044 ray1044
theorem signs1044 : ∀ j, Signs p1044 (bank1044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1045 := params 20
abbrev ray1045 := rays 20
def bank1045 : Fin 1 → Cell := oneBank p1045 ray1045
theorem signs1045 : ∀ j, Signs p1045 (bank1045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1046 := params 21
abbrev ray1046 := rays 21
def bank1046 : Fin 1 → Cell := oneBank p1046 ray1046
theorem signs1046 : ∀ j, Signs p1046 (bank1046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1047 := params 22
abbrev ray1047 := rays 22
def bank1047 : Fin 1 → Cell := oneBank p1047 ray1047
theorem signs1047 : ∀ j, Signs p1047 (bank1047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1048 := params 23
abbrev ray1048 := rays 23
def bank1048 : Fin 1 → Cell := oneBank p1048 ray1048
theorem signs1048 : ∀ j, Signs p1048 (bank1048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1049 := params 24
abbrev ray1049 := rays 24
def bank1049 : Fin 1 → Cell := oneBank p1049 ray1049
theorem signs1049 : ∀ j, Signs p1049 (bank1049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1050 := params 25
abbrev ray1050 := rays 25
def bank1050 : Fin 1 → Cell := oneBank p1050 ray1050
theorem signs1050 : ∀ j, Signs p1050 (bank1050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1051 := params 26
abbrev ray1051 := rays 26
def bank1051 : Fin 1 → Cell := oneBank p1051 ray1051
theorem signs1051 : ∀ j, Signs p1051 (bank1051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1052 := params 27
abbrev ray1052 := rays 27
def bank1052 : Fin 1 → Cell := oneBank p1052 ray1052
theorem signs1052 : ∀ j, Signs p1052 (bank1052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1053 := params 28
abbrev ray1053 := rays 28
def bank1053 : Fin 1 → Cell := oneBank p1053 ray1053
theorem signs1053 : ∀ j, Signs p1053 (bank1053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1054 := params 29
abbrev ray1054 := rays 29
def bank1054 : Fin 1 → Cell := oneBank p1054 ray1054
theorem signs1054 : ∀ j, Signs p1054 (bank1054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1055 := params 30
abbrev ray1055 := rays 30
def bank1055 : Fin 1 → Cell := oneBank p1055 ray1055
theorem signs1055 : ∀ j, Signs p1055 (bank1055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1056 := params 31
abbrev ray1056 := rays 31
def bank1056 : Fin 1 → Cell := oneBank p1056 ray1056
theorem signs1056 : ∀ j, Signs p1056 (bank1056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01025_01056
