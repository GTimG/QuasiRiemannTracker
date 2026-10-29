/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00897_00928
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99874251433386,99874099234867,99873947010717,99873794760939,99873642485535,99873490184507,99873337857858,99873185505591,99873033127708,99872880724211,99872728295104,99872575840388,99872423360066,99872270854141,99872118322615,99871965765491,99871813182770,99871660574456,99871507940551,99871355281058,99871202595978,99871049885315,99870897149071,99870744387248,99870591599849,99870438786877,99870285948334,99870133084222,99869980194544,99869827279302,99869674338499,99869521372137,99869368380219]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (896+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(22629085747416075833368/29424040143947626493295:Fraction),(4525421085355323364723/5884691362122975298659:Fraction),(67875375129591416253152/88268620431846379479885:Fraction),(2513682777954681104636/3269143349327708499255:Fraction),(1938956991176962755640/2521860583767139413711:Fraction),(67857554188854639179324/88263370431851629479885:Fraction),(22617205309106490912776/29420540143951126493295:Fraction),(67845676262321903181539/88259870431855129479885:Fraction),(67839738838237798094372/88258120431856879479885:Fraction),(611115315411836771468/795102436323050716035:Fraction),(67827862209383072675542/88254620431860379479885:Fraction),(67821925434298387037762/88252870431862129479885:Fraction),(4521065898043699733980/5883408028790925298659:Fraction),(67810052533340842227452/88249370431865629479885:Fraction),(1506758142389340513413/1961058231819275099553:Fraction),(2511043752152184087221/3268365571550708499255:Fraction),(1936921314864083156660/2521260583767739413711:Fraction),(67786311758866934167064/88242370431872629479885:Fraction),(2510384344781101583129/3268171127106458499255:Fraction),(67774443885883539646244/88238870431876129479885:Fraction),(1075690639275035874068/1400589213204410785395:Fraction),(4517505179294857442324/5882358028791975298659:Fraction),(13551328983244371643553/17646724086376275895977:Fraction),(67750713169752445382366/88231870431883129479885:Fraction),(2509065971668100655553/3267782238217958499255:Fraction),(67738850327138620059884/88228370431886629479885:Fraction),(1505175982912144165688/1960591565153075099553:Fraction),(2508407005994358164824/3267587793773708499255:Fraction),(67721058904509088575382/88223120431891879479885:Fraction),(67715129674144666670336/88221370431893629479885:Fraction),(22569733823603231959682/29406540143965126493295:Fraction),(67703271864295805448953/88217870431897129479885:Fraction)]
abbrev p897 := params 0
abbrev ray897 := rays 0
def bank897 : Fin 1 → Cell := oneBank p897 ray897
theorem signs897 : ∀ j, Signs p897 (bank897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p898 := params 1
abbrev ray898 := rays 1
def bank898 : Fin 1 → Cell := oneBank p898 ray898
theorem signs898 : ∀ j, Signs p898 (bank898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p899 := params 2
abbrev ray899 := rays 2
def bank899 : Fin 1 → Cell := oneBank p899 ray899
theorem signs899 : ∀ j, Signs p899 (bank899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p900 := params 3
abbrev ray900 := rays 3
def bank900 : Fin 1 → Cell := oneBank p900 ray900
theorem signs900 : ∀ j, Signs p900 (bank900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p901 := params 4
abbrev ray901 := rays 4
def bank901 : Fin 1 → Cell := oneBank p901 ray901
theorem signs901 : ∀ j, Signs p901 (bank901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p902 := params 5
abbrev ray902 := rays 5
def bank902 : Fin 1 → Cell := oneBank p902 ray902
theorem signs902 : ∀ j, Signs p902 (bank902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p903 := params 6
abbrev ray903 := rays 6
def bank903 : Fin 1 → Cell := oneBank p903 ray903
theorem signs903 : ∀ j, Signs p903 (bank903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p904 := params 7
abbrev ray904 := rays 7
def bank904 : Fin 1 → Cell := oneBank p904 ray904
theorem signs904 : ∀ j, Signs p904 (bank904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p905 := params 8
abbrev ray905 := rays 8
def bank905 : Fin 1 → Cell := oneBank p905 ray905
theorem signs905 : ∀ j, Signs p905 (bank905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p906 := params 9
abbrev ray906 := rays 9
def bank906 : Fin 1 → Cell := oneBank p906 ray906
theorem signs906 : ∀ j, Signs p906 (bank906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p907 := params 10
abbrev ray907 := rays 10
def bank907 : Fin 1 → Cell := oneBank p907 ray907
theorem signs907 : ∀ j, Signs p907 (bank907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p908 := params 11
abbrev ray908 := rays 11
def bank908 : Fin 1 → Cell := oneBank p908 ray908
theorem signs908 : ∀ j, Signs p908 (bank908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p909 := params 12
abbrev ray909 := rays 12
def bank909 : Fin 1 → Cell := oneBank p909 ray909
theorem signs909 : ∀ j, Signs p909 (bank909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p910 := params 13
abbrev ray910 := rays 13
def bank910 : Fin 1 → Cell := oneBank p910 ray910
theorem signs910 : ∀ j, Signs p910 (bank910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p911 := params 14
abbrev ray911 := rays 14
def bank911 : Fin 1 → Cell := oneBank p911 ray911
theorem signs911 : ∀ j, Signs p911 (bank911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p912 := params 15
abbrev ray912 := rays 15
def bank912 : Fin 1 → Cell := oneBank p912 ray912
theorem signs912 : ∀ j, Signs p912 (bank912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p913 := params 16
abbrev ray913 := rays 16
def bank913 : Fin 1 → Cell := oneBank p913 ray913
theorem signs913 : ∀ j, Signs p913 (bank913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p914 := params 17
abbrev ray914 := rays 17
def bank914 : Fin 1 → Cell := oneBank p914 ray914
theorem signs914 : ∀ j, Signs p914 (bank914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p915 := params 18
abbrev ray915 := rays 18
def bank915 : Fin 1 → Cell := oneBank p915 ray915
theorem signs915 : ∀ j, Signs p915 (bank915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p916 := params 19
abbrev ray916 := rays 19
def bank916 : Fin 1 → Cell := oneBank p916 ray916
theorem signs916 : ∀ j, Signs p916 (bank916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p917 := params 20
abbrev ray917 := rays 20
def bank917 : Fin 1 → Cell := oneBank p917 ray917
theorem signs917 : ∀ j, Signs p917 (bank917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p918 := params 21
abbrev ray918 := rays 21
def bank918 : Fin 1 → Cell := oneBank p918 ray918
theorem signs918 : ∀ j, Signs p918 (bank918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p919 := params 22
abbrev ray919 := rays 22
def bank919 : Fin 1 → Cell := oneBank p919 ray919
theorem signs919 : ∀ j, Signs p919 (bank919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p920 := params 23
abbrev ray920 := rays 23
def bank920 : Fin 1 → Cell := oneBank p920 ray920
theorem signs920 : ∀ j, Signs p920 (bank920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p921 := params 24
abbrev ray921 := rays 24
def bank921 : Fin 1 → Cell := oneBank p921 ray921
theorem signs921 : ∀ j, Signs p921 (bank921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p922 := params 25
abbrev ray922 := rays 25
def bank922 : Fin 1 → Cell := oneBank p922 ray922
theorem signs922 : ∀ j, Signs p922 (bank922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p923 := params 26
abbrev ray923 := rays 26
def bank923 : Fin 1 → Cell := oneBank p923 ray923
theorem signs923 : ∀ j, Signs p923 (bank923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p924 := params 27
abbrev ray924 := rays 27
def bank924 : Fin 1 → Cell := oneBank p924 ray924
theorem signs924 : ∀ j, Signs p924 (bank924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p925 := params 28
abbrev ray925 := rays 28
def bank925 : Fin 1 → Cell := oneBank p925 ray925
theorem signs925 : ∀ j, Signs p925 (bank925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p926 := params 29
abbrev ray926 := rays 29
def bank926 : Fin 1 → Cell := oneBank p926 ray926
theorem signs926 : ∀ j, Signs p926 (bank926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p927 := params 30
abbrev ray927 := rays 30
def bank927 : Fin 1 → Cell := oneBank p927 ray927
theorem signs927 : ∀ j, Signs p927 (bank927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p928 := params 31
abbrev ray928 := rays 31
def bank928 : Fin 1 → Cell := oneBank p928 ray928
theorem signs928 : ∀ j, Signs p928 (bank928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00897_00928
