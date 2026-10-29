/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15937_15968
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94963226640891,94962754288149,94962281919412,94961809534681,94961337133955,94960864717235,94960392284520,94959919835811,94959447371107,94958974890409,94958502393717,94958029881031,94957557352350,94957084807675,94956612247006,94956139670343,94955667077686,94955194469035,94954721844390,94954249203751,94953776547118,94953303874491,94952831185871,94952358481257,94951885760649,94951413024047,94950940271452,94950467502863,94949994718281,94949521917705,94949049101136,94948576268573,94948103420017]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15936+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15937 := params 0
abbrev ray15937 := rays 0
def bank15937 : Fin 1 → Cell := oneBank p15937 ray15937
theorem signs15937 : ∀ j, Signs p15937 (bank15937 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15938 := params 1
abbrev ray15938 := rays 1
def bank15938 : Fin 1 → Cell := oneBank p15938 ray15938
theorem signs15938 : ∀ j, Signs p15938 (bank15938 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15939 := params 2
abbrev ray15939 := rays 2
def bank15939 : Fin 1 → Cell := oneBank p15939 ray15939
theorem signs15939 : ∀ j, Signs p15939 (bank15939 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15940 := params 3
abbrev ray15940 := rays 3
def bank15940 : Fin 1 → Cell := oneBank p15940 ray15940
theorem signs15940 : ∀ j, Signs p15940 (bank15940 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15941 := params 4
abbrev ray15941 := rays 4
def bank15941 : Fin 1 → Cell := oneBank p15941 ray15941
theorem signs15941 : ∀ j, Signs p15941 (bank15941 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15942 := params 5
abbrev ray15942 := rays 5
def bank15942 : Fin 1 → Cell := oneBank p15942 ray15942
theorem signs15942 : ∀ j, Signs p15942 (bank15942 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15943 := params 6
abbrev ray15943 := rays 6
def bank15943 : Fin 1 → Cell := oneBank p15943 ray15943
theorem signs15943 : ∀ j, Signs p15943 (bank15943 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15944 := params 7
abbrev ray15944 := rays 7
def bank15944 : Fin 1 → Cell := oneBank p15944 ray15944
theorem signs15944 : ∀ j, Signs p15944 (bank15944 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15945 := params 8
abbrev ray15945 := rays 8
def bank15945 : Fin 1 → Cell := oneBank p15945 ray15945
theorem signs15945 : ∀ j, Signs p15945 (bank15945 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15946 := params 9
abbrev ray15946 := rays 9
def bank15946 : Fin 1 → Cell := oneBank p15946 ray15946
theorem signs15946 : ∀ j, Signs p15946 (bank15946 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15947 := params 10
abbrev ray15947 := rays 10
def bank15947 : Fin 1 → Cell := oneBank p15947 ray15947
theorem signs15947 : ∀ j, Signs p15947 (bank15947 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15948 := params 11
abbrev ray15948 := rays 11
def bank15948 : Fin 1 → Cell := oneBank p15948 ray15948
theorem signs15948 : ∀ j, Signs p15948 (bank15948 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15949 := params 12
abbrev ray15949 := rays 12
def bank15949 : Fin 1 → Cell := oneBank p15949 ray15949
theorem signs15949 : ∀ j, Signs p15949 (bank15949 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15950 := params 13
abbrev ray15950 := rays 13
def bank15950 : Fin 1 → Cell := oneBank p15950 ray15950
theorem signs15950 : ∀ j, Signs p15950 (bank15950 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15951 := params 14
abbrev ray15951 := rays 14
def bank15951 : Fin 1 → Cell := oneBank p15951 ray15951
theorem signs15951 : ∀ j, Signs p15951 (bank15951 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15952 := params 15
abbrev ray15952 := rays 15
def bank15952 : Fin 1 → Cell := oneBank p15952 ray15952
theorem signs15952 : ∀ j, Signs p15952 (bank15952 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15953 := params 16
abbrev ray15953 := rays 16
def bank15953 : Fin 1 → Cell := oneBank p15953 ray15953
theorem signs15953 : ∀ j, Signs p15953 (bank15953 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15954 := params 17
abbrev ray15954 := rays 17
def bank15954 : Fin 1 → Cell := oneBank p15954 ray15954
theorem signs15954 : ∀ j, Signs p15954 (bank15954 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15955 := params 18
abbrev ray15955 := rays 18
def bank15955 : Fin 1 → Cell := oneBank p15955 ray15955
theorem signs15955 : ∀ j, Signs p15955 (bank15955 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15956 := params 19
abbrev ray15956 := rays 19
def bank15956 : Fin 1 → Cell := oneBank p15956 ray15956
theorem signs15956 : ∀ j, Signs p15956 (bank15956 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15957 := params 20
abbrev ray15957 := rays 20
def bank15957 : Fin 1 → Cell := oneBank p15957 ray15957
theorem signs15957 : ∀ j, Signs p15957 (bank15957 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15958 := params 21
abbrev ray15958 := rays 21
def bank15958 : Fin 1 → Cell := oneBank p15958 ray15958
theorem signs15958 : ∀ j, Signs p15958 (bank15958 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15959 := params 22
abbrev ray15959 := rays 22
def bank15959 : Fin 1 → Cell := oneBank p15959 ray15959
theorem signs15959 : ∀ j, Signs p15959 (bank15959 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15960 := params 23
abbrev ray15960 := rays 23
def bank15960 : Fin 1 → Cell := oneBank p15960 ray15960
theorem signs15960 : ∀ j, Signs p15960 (bank15960 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15961 := params 24
abbrev ray15961 := rays 24
def bank15961 : Fin 1 → Cell := oneBank p15961 ray15961
theorem signs15961 : ∀ j, Signs p15961 (bank15961 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15962 := params 25
abbrev ray15962 := rays 25
def bank15962 : Fin 1 → Cell := oneBank p15962 ray15962
theorem signs15962 : ∀ j, Signs p15962 (bank15962 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15963 := params 26
abbrev ray15963 := rays 26
def bank15963 : Fin 1 → Cell := oneBank p15963 ray15963
theorem signs15963 : ∀ j, Signs p15963 (bank15963 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15964 := params 27
abbrev ray15964 := rays 27
def bank15964 : Fin 1 → Cell := oneBank p15964 ray15964
theorem signs15964 : ∀ j, Signs p15964 (bank15964 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15965 := params 28
abbrev ray15965 := rays 28
def bank15965 : Fin 1 → Cell := oneBank p15965 ray15965
theorem signs15965 : ∀ j, Signs p15965 (bank15965 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15966 := params 29
abbrev ray15966 := rays 29
def bank15966 : Fin 1 → Cell := oneBank p15966 ray15966
theorem signs15966 : ∀ j, Signs p15966 (bank15966 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15967 := params 30
abbrev ray15967 := rays 30
def bank15967 : Fin 1 → Cell := oneBank p15967 ray15967
theorem signs15967 : ∀ j, Signs p15967 (bank15967 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15968 := params 31
abbrev ray15968 := rays 31
def bank15968 : Fin 1 → Cell := oneBank p15968 ray15968
theorem signs15968 : ∀ j, Signs p15968 (bank15968 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15937_15968
