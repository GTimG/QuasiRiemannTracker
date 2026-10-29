/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00929_00960
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99869368380219,99869215362747,99869062319724,99868909251152,99868756157034,99868603037372,99868449892169,99868296721427,99868143525149,99867990303337,99867837055994,99867683783122,99867530484724,99867377160801,99867223811357,99867070436394,99866917035914,99866763609920,99866610158415,99866456681401,99866303178880,99866149650855,99865996097328,99865842518302,99865688913779,99865535283762,99865381628253,99865227947255,99865074240770,99864920508800,99864766751348,99864612968416,99864459160007]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (928+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(509002590225632684018/663279100991720898345:Fraction),(22563805244189079717188/29404790143966876493295:Fraction),(13537097841492390186592/17642524086380475895977:Fraction),(67679562494413464861736/88210870431904129479885:Fraction),(22557878531144731197088/29403040143968626493295:Fraction),(4511180647983489173866/5880491362127175298659:Fraction),(67661783658191916443486/88205620431909379479885:Fraction),(7517317624889966014792/9800430047990125497765:Fraction),(67649933402001116649866/88202120431912879479885:Fraction),(13528801841490301886735/17640074086382925895977:Fraction),(7515342758347527449456/9799846714657375497765:Fraction),(22544053823447904728272/29398956810639376493295:Fraction),(13525247585567543229352/17639024086383975895977:Fraction),(834818708801864522483/1088807042369402833085:Fraction),(7512710436193338486421/9799068936880375497765:Fraction),(7512052472322118062196/9798874492436125497765:Fraction),(166919877502319247308/217748445510930566617:Fraction),(1931332272964613203220/2519610583769389413711:Fraction),(13518141706303634756705/17636924086386075895977:Fraction),(22528262845712510161577/29394290143977376493295:Fraction),(4505257890349494285214/5878741362128925298659:Fraction),(500540364454004754602/653180521718041699851:Fraction),(22522343691778749952232/29392540143979126493295:Fraction),(13512222552392090054128/17635174086387825895977:Fraction),(22518398087058149387144/29391373477313626493295:Fraction),(2501825066240487053452/3265643349331208499255:Fraction),(67543359128453770671778/88170620431944379479885:Fraction),(5448765025945926394/7113261027184036263:Fraction),(1500700597621891709252/1959269342932175099553:Fraction),(13505121977308927776310/17633074086389925895977:Fraction),(67519695123969530426582/88163620431951379479885:Fraction),(2500510376821492034498/3265254460442708499255:Fraction)]
abbrev p929 := params 0
abbrev ray929 := rays 0
def bank929 : Fin 1 → Cell := oneBank p929 ray929
theorem signs929 : ∀ j, Signs p929 (bank929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p930 := params 1
abbrev ray930 := rays 1
def bank930 : Fin 1 → Cell := oneBank p930 ray930
theorem signs930 : ∀ j, Signs p930 (bank930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p931 := params 2
abbrev ray931 := rays 2
def bank931 : Fin 1 → Cell := oneBank p931 ray931
theorem signs931 : ∀ j, Signs p931 (bank931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p932 := params 3
abbrev ray932 := rays 3
def bank932 : Fin 1 → Cell := oneBank p932 ray932
theorem signs932 : ∀ j, Signs p932 (bank932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p933 := params 4
abbrev ray933 := rays 4
def bank933 : Fin 1 → Cell := oneBank p933 ray933
theorem signs933 : ∀ j, Signs p933 (bank933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p934 := params 5
abbrev ray934 := rays 5
def bank934 : Fin 1 → Cell := oneBank p934 ray934
theorem signs934 : ∀ j, Signs p934 (bank934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p935 := params 6
abbrev ray935 := rays 6
def bank935 : Fin 1 → Cell := oneBank p935 ray935
theorem signs935 : ∀ j, Signs p935 (bank935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p936 := params 7
abbrev ray936 := rays 7
def bank936 : Fin 1 → Cell := oneBank p936 ray936
theorem signs936 : ∀ j, Signs p936 (bank936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p937 := params 8
abbrev ray937 := rays 8
def bank937 : Fin 1 → Cell := oneBank p937 ray937
theorem signs937 : ∀ j, Signs p937 (bank937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p938 := params 9
abbrev ray938 := rays 9
def bank938 : Fin 1 → Cell := oneBank p938 ray938
theorem signs938 : ∀ j, Signs p938 (bank938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p939 := params 10
abbrev ray939 := rays 10
def bank939 : Fin 1 → Cell := oneBank p939 ray939
theorem signs939 : ∀ j, Signs p939 (bank939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p940 := params 11
abbrev ray940 := rays 11
def bank940 : Fin 1 → Cell := oneBank p940 ray940
theorem signs940 : ∀ j, Signs p940 (bank940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p941 := params 12
abbrev ray941 := rays 12
def bank941 : Fin 1 → Cell := oneBank p941 ray941
theorem signs941 : ∀ j, Signs p941 (bank941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p942 := params 13
abbrev ray942 := rays 13
def bank942 : Fin 1 → Cell := oneBank p942 ray942
theorem signs942 : ∀ j, Signs p942 (bank942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p943 := params 14
abbrev ray943 := rays 14
def bank943 : Fin 1 → Cell := oneBank p943 ray943
theorem signs943 : ∀ j, Signs p943 (bank943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p944 := params 15
abbrev ray944 := rays 15
def bank944 : Fin 1 → Cell := oneBank p944 ray944
theorem signs944 : ∀ j, Signs p944 (bank944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p945 := params 16
abbrev ray945 := rays 16
def bank945 : Fin 1 → Cell := oneBank p945 ray945
theorem signs945 : ∀ j, Signs p945 (bank945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p946 := params 17
abbrev ray946 := rays 17
def bank946 : Fin 1 → Cell := oneBank p946 ray946
theorem signs946 : ∀ j, Signs p946 (bank946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p947 := params 18
abbrev ray947 := rays 18
def bank947 : Fin 1 → Cell := oneBank p947 ray947
theorem signs947 : ∀ j, Signs p947 (bank947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p948 := params 19
abbrev ray948 := rays 19
def bank948 : Fin 1 → Cell := oneBank p948 ray948
theorem signs948 : ∀ j, Signs p948 (bank948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p949 := params 20
abbrev ray949 := rays 20
def bank949 : Fin 1 → Cell := oneBank p949 ray949
theorem signs949 : ∀ j, Signs p949 (bank949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p950 := params 21
abbrev ray950 := rays 21
def bank950 : Fin 1 → Cell := oneBank p950 ray950
theorem signs950 : ∀ j, Signs p950 (bank950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p951 := params 22
abbrev ray951 := rays 22
def bank951 : Fin 1 → Cell := oneBank p951 ray951
theorem signs951 : ∀ j, Signs p951 (bank951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p952 := params 23
abbrev ray952 := rays 23
def bank952 : Fin 1 → Cell := oneBank p952 ray952
theorem signs952 : ∀ j, Signs p952 (bank952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p953 := params 24
abbrev ray953 := rays 24
def bank953 : Fin 1 → Cell := oneBank p953 ray953
theorem signs953 : ∀ j, Signs p953 (bank953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p954 := params 25
abbrev ray954 := rays 25
def bank954 : Fin 1 → Cell := oneBank p954 ray954
theorem signs954 : ∀ j, Signs p954 (bank954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p955 := params 26
abbrev ray955 := rays 26
def bank955 : Fin 1 → Cell := oneBank p955 ray955
theorem signs955 : ∀ j, Signs p955 (bank955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p956 := params 27
abbrev ray956 := rays 27
def bank956 : Fin 1 → Cell := oneBank p956 ray956
theorem signs956 : ∀ j, Signs p956 (bank956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p957 := params 28
abbrev ray957 := rays 28
def bank957 : Fin 1 → Cell := oneBank p957 ray957
theorem signs957 : ∀ j, Signs p957 (bank957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p958 := params 29
abbrev ray958 := rays 29
def bank958 : Fin 1 → Cell := oneBank p958 ray958
theorem signs958 : ∀ j, Signs p958 (bank958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p959 := params 30
abbrev ray959 := rays 30
def bank959 : Fin 1 → Cell := oneBank p959 ray959
theorem signs959 : ∀ j, Signs p959 (bank959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p960 := params 31
abbrev ray960 := rays 31
def bank960 : Fin 1 → Cell := oneBank p960 ray960
theorem signs960 : ∀ j, Signs p960 (bank960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00929_00960
