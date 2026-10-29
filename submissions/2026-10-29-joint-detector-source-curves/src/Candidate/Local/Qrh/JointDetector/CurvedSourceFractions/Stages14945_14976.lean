/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14945_14976
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95423913028342,95423456574677,95423000104940,95422543619131,95422087117250,95421630599297,95421174065272,95420717515176,95420260949008,95419804366769,95419347768459,95418891154078,95418434523626,95417977877103,95417521214509,95417064535845,95416607841110,95416151130305,95415694403430,95415237660484,95414780901468,95414324126382,95413867335227,95413410528002,95412953704707,95412496865343,95412040009909,95411583138406,95411126250834,95410669347193,95410212427483,95409755491704,95409298539857]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14944+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14945 := params 0
abbrev ray14945 := rays 0
def bank14945 : Fin 1 → Cell := oneBank p14945 ray14945
theorem signs14945 : ∀ j, Signs p14945 (bank14945 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14946 := params 1
abbrev ray14946 := rays 1
def bank14946 : Fin 1 → Cell := oneBank p14946 ray14946
theorem signs14946 : ∀ j, Signs p14946 (bank14946 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14947 := params 2
abbrev ray14947 := rays 2
def bank14947 : Fin 1 → Cell := oneBank p14947 ray14947
theorem signs14947 : ∀ j, Signs p14947 (bank14947 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14948 := params 3
abbrev ray14948 := rays 3
def bank14948 : Fin 1 → Cell := oneBank p14948 ray14948
theorem signs14948 : ∀ j, Signs p14948 (bank14948 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14949 := params 4
abbrev ray14949 := rays 4
def bank14949 : Fin 1 → Cell := oneBank p14949 ray14949
theorem signs14949 : ∀ j, Signs p14949 (bank14949 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14950 := params 5
abbrev ray14950 := rays 5
def bank14950 : Fin 1 → Cell := oneBank p14950 ray14950
theorem signs14950 : ∀ j, Signs p14950 (bank14950 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14951 := params 6
abbrev ray14951 := rays 6
def bank14951 : Fin 1 → Cell := oneBank p14951 ray14951
theorem signs14951 : ∀ j, Signs p14951 (bank14951 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14952 := params 7
abbrev ray14952 := rays 7
def bank14952 : Fin 1 → Cell := oneBank p14952 ray14952
theorem signs14952 : ∀ j, Signs p14952 (bank14952 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14953 := params 8
abbrev ray14953 := rays 8
def bank14953 : Fin 1 → Cell := oneBank p14953 ray14953
theorem signs14953 : ∀ j, Signs p14953 (bank14953 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14954 := params 9
abbrev ray14954 := rays 9
def bank14954 : Fin 1 → Cell := oneBank p14954 ray14954
theorem signs14954 : ∀ j, Signs p14954 (bank14954 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14955 := params 10
abbrev ray14955 := rays 10
def bank14955 : Fin 1 → Cell := oneBank p14955 ray14955
theorem signs14955 : ∀ j, Signs p14955 (bank14955 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14956 := params 11
abbrev ray14956 := rays 11
def bank14956 : Fin 1 → Cell := oneBank p14956 ray14956
theorem signs14956 : ∀ j, Signs p14956 (bank14956 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14957 := params 12
abbrev ray14957 := rays 12
def bank14957 : Fin 1 → Cell := oneBank p14957 ray14957
theorem signs14957 : ∀ j, Signs p14957 (bank14957 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14958 := params 13
abbrev ray14958 := rays 13
def bank14958 : Fin 1 → Cell := oneBank p14958 ray14958
theorem signs14958 : ∀ j, Signs p14958 (bank14958 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14959 := params 14
abbrev ray14959 := rays 14
def bank14959 : Fin 1 → Cell := oneBank p14959 ray14959
theorem signs14959 : ∀ j, Signs p14959 (bank14959 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14960 := params 15
abbrev ray14960 := rays 15
def bank14960 : Fin 1 → Cell := oneBank p14960 ray14960
theorem signs14960 : ∀ j, Signs p14960 (bank14960 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14961 := params 16
abbrev ray14961 := rays 16
def bank14961 : Fin 1 → Cell := oneBank p14961 ray14961
theorem signs14961 : ∀ j, Signs p14961 (bank14961 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14962 := params 17
abbrev ray14962 := rays 17
def bank14962 : Fin 1 → Cell := oneBank p14962 ray14962
theorem signs14962 : ∀ j, Signs p14962 (bank14962 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14963 := params 18
abbrev ray14963 := rays 18
def bank14963 : Fin 1 → Cell := oneBank p14963 ray14963
theorem signs14963 : ∀ j, Signs p14963 (bank14963 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14964 := params 19
abbrev ray14964 := rays 19
def bank14964 : Fin 1 → Cell := oneBank p14964 ray14964
theorem signs14964 : ∀ j, Signs p14964 (bank14964 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14965 := params 20
abbrev ray14965 := rays 20
def bank14965 : Fin 1 → Cell := oneBank p14965 ray14965
theorem signs14965 : ∀ j, Signs p14965 (bank14965 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14966 := params 21
abbrev ray14966 := rays 21
def bank14966 : Fin 1 → Cell := oneBank p14966 ray14966
theorem signs14966 : ∀ j, Signs p14966 (bank14966 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14967 := params 22
abbrev ray14967 := rays 22
def bank14967 : Fin 1 → Cell := oneBank p14967 ray14967
theorem signs14967 : ∀ j, Signs p14967 (bank14967 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14968 := params 23
abbrev ray14968 := rays 23
def bank14968 : Fin 1 → Cell := oneBank p14968 ray14968
theorem signs14968 : ∀ j, Signs p14968 (bank14968 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14969 := params 24
abbrev ray14969 := rays 24
def bank14969 : Fin 1 → Cell := oneBank p14969 ray14969
theorem signs14969 : ∀ j, Signs p14969 (bank14969 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14970 := params 25
abbrev ray14970 := rays 25
def bank14970 : Fin 1 → Cell := oneBank p14970 ray14970
theorem signs14970 : ∀ j, Signs p14970 (bank14970 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14971 := params 26
abbrev ray14971 := rays 26
def bank14971 : Fin 1 → Cell := oneBank p14971 ray14971
theorem signs14971 : ∀ j, Signs p14971 (bank14971 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14972 := params 27
abbrev ray14972 := rays 27
def bank14972 : Fin 1 → Cell := oneBank p14972 ray14972
theorem signs14972 : ∀ j, Signs p14972 (bank14972 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14973 := params 28
abbrev ray14973 := rays 28
def bank14973 : Fin 1 → Cell := oneBank p14973 ray14973
theorem signs14973 : ∀ j, Signs p14973 (bank14973 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14974 := params 29
abbrev ray14974 := rays 29
def bank14974 : Fin 1 → Cell := oneBank p14974 ray14974
theorem signs14974 : ∀ j, Signs p14974 (bank14974 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14975 := params 30
abbrev ray14975 := rays 30
def bank14975 : Fin 1 → Cell := oneBank p14975 ray14975
theorem signs14975 : ∀ j, Signs p14975 (bank14975 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14976 := params 31
abbrev ray14976 := rays 31
def bank14976 : Fin 1 → Cell := oneBank p14976 ray14976
theorem signs14976 : ∀ j, Signs p14976 (bank14976 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14945_14976
