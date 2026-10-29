/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11937_11968
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96722480449769,96722075401617,96721670334082,96721265247165,96720860140866,96720455015186,96720049870125,96719644705683,96719239521861,96718834318659,96718429096078,96718023854118,96717618592780,96717213312064,96716808011970,96716402692499,96715997353651,96715591995427,96715186617827,96714781220852,96714375804502,96713970368777,96713564913678,96713159439206,96712753945360,96712348432142,96711942899551,96711537347588,96711131776254,96710726185549,96710320575473,96709914946027,96709509297211]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11936+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11937 := params 0
abbrev ray11937 := rays 0
def bank11937 : Fin 2 → Cell := twoBank p11937 ray11937
theorem signs11937 : ∀ j, Signs p11937 (bank11937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11938 := params 1
abbrev ray11938 := rays 1
def bank11938 : Fin 2 → Cell := twoBank p11938 ray11938
theorem signs11938 : ∀ j, Signs p11938 (bank11938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11939 := params 2
abbrev ray11939 := rays 2
def bank11939 : Fin 2 → Cell := twoBank p11939 ray11939
theorem signs11939 : ∀ j, Signs p11939 (bank11939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11940 := params 3
abbrev ray11940 := rays 3
def bank11940 : Fin 2 → Cell := twoBank p11940 ray11940
theorem signs11940 : ∀ j, Signs p11940 (bank11940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11941 := params 4
abbrev ray11941 := rays 4
def bank11941 : Fin 2 → Cell := twoBank p11941 ray11941
theorem signs11941 : ∀ j, Signs p11941 (bank11941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11942 := params 5
abbrev ray11942 := rays 5
def bank11942 : Fin 2 → Cell := twoBank p11942 ray11942
theorem signs11942 : ∀ j, Signs p11942 (bank11942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11943 := params 6
abbrev ray11943 := rays 6
def bank11943 : Fin 2 → Cell := twoBank p11943 ray11943
theorem signs11943 : ∀ j, Signs p11943 (bank11943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11944 := params 7
abbrev ray11944 := rays 7
def bank11944 : Fin 2 → Cell := twoBank p11944 ray11944
theorem signs11944 : ∀ j, Signs p11944 (bank11944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11945 := params 8
abbrev ray11945 := rays 8
def bank11945 : Fin 2 → Cell := twoBank p11945 ray11945
theorem signs11945 : ∀ j, Signs p11945 (bank11945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11946 := params 9
abbrev ray11946 := rays 9
def bank11946 : Fin 2 → Cell := twoBank p11946 ray11946
theorem signs11946 : ∀ j, Signs p11946 (bank11946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11947 := params 10
abbrev ray11947 := rays 10
def bank11947 : Fin 2 → Cell := twoBank p11947 ray11947
theorem signs11947 : ∀ j, Signs p11947 (bank11947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11948 := params 11
abbrev ray11948 := rays 11
def bank11948 : Fin 2 → Cell := twoBank p11948 ray11948
theorem signs11948 : ∀ j, Signs p11948 (bank11948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11949 := params 12
abbrev ray11949 := rays 12
def bank11949 : Fin 2 → Cell := twoBank p11949 ray11949
theorem signs11949 : ∀ j, Signs p11949 (bank11949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11950 := params 13
abbrev ray11950 := rays 13
def bank11950 : Fin 2 → Cell := twoBank p11950 ray11950
theorem signs11950 : ∀ j, Signs p11950 (bank11950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11951 := params 14
abbrev ray11951 := rays 14
def bank11951 : Fin 2 → Cell := twoBank p11951 ray11951
theorem signs11951 : ∀ j, Signs p11951 (bank11951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11952 := params 15
abbrev ray11952 := rays 15
def bank11952 : Fin 2 → Cell := twoBank p11952 ray11952
theorem signs11952 : ∀ j, Signs p11952 (bank11952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11953 := params 16
abbrev ray11953 := rays 16
def bank11953 : Fin 2 → Cell := twoBank p11953 ray11953
theorem signs11953 : ∀ j, Signs p11953 (bank11953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11954 := params 17
abbrev ray11954 := rays 17
def bank11954 : Fin 2 → Cell := twoBank p11954 ray11954
theorem signs11954 : ∀ j, Signs p11954 (bank11954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11955 := params 18
abbrev ray11955 := rays 18
def bank11955 : Fin 2 → Cell := twoBank p11955 ray11955
theorem signs11955 : ∀ j, Signs p11955 (bank11955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11956 := params 19
abbrev ray11956 := rays 19
def bank11956 : Fin 2 → Cell := twoBank p11956 ray11956
theorem signs11956 : ∀ j, Signs p11956 (bank11956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11957 := params 20
abbrev ray11957 := rays 20
def bank11957 : Fin 2 → Cell := twoBank p11957 ray11957
theorem signs11957 : ∀ j, Signs p11957 (bank11957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11958 := params 21
abbrev ray11958 := rays 21
def bank11958 : Fin 2 → Cell := twoBank p11958 ray11958
theorem signs11958 : ∀ j, Signs p11958 (bank11958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11959 := params 22
abbrev ray11959 := rays 22
def bank11959 : Fin 2 → Cell := twoBank p11959 ray11959
theorem signs11959 : ∀ j, Signs p11959 (bank11959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11960 := params 23
abbrev ray11960 := rays 23
def bank11960 : Fin 2 → Cell := twoBank p11960 ray11960
theorem signs11960 : ∀ j, Signs p11960 (bank11960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11961 := params 24
abbrev ray11961 := rays 24
def bank11961 : Fin 2 → Cell := twoBank p11961 ray11961
theorem signs11961 : ∀ j, Signs p11961 (bank11961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11962 := params 25
abbrev ray11962 := rays 25
def bank11962 : Fin 2 → Cell := twoBank p11962 ray11962
theorem signs11962 : ∀ j, Signs p11962 (bank11962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11963 := params 26
abbrev ray11963 := rays 26
def bank11963 : Fin 2 → Cell := twoBank p11963 ray11963
theorem signs11963 : ∀ j, Signs p11963 (bank11963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11964 := params 27
abbrev ray11964 := rays 27
def bank11964 : Fin 2 → Cell := twoBank p11964 ray11964
theorem signs11964 : ∀ j, Signs p11964 (bank11964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11965 := params 28
abbrev ray11965 := rays 28
def bank11965 : Fin 2 → Cell := twoBank p11965 ray11965
theorem signs11965 : ∀ j, Signs p11965 (bank11965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11966 := params 29
abbrev ray11966 := rays 29
def bank11966 : Fin 2 → Cell := twoBank p11966 ray11966
theorem signs11966 : ∀ j, Signs p11966 (bank11966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11967 := params 30
abbrev ray11967 := rays 30
def bank11967 : Fin 2 → Cell := twoBank p11967 ray11967
theorem signs11967 : ∀ j, Signs p11967 (bank11967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11968 := params 31
abbrev ray11968 := rays 31
def bank11968 : Fin 2 → Cell := twoBank p11968 ray11968
theorem signs11968 : ∀ j, Signs p11968 (bank11968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11937_11968
