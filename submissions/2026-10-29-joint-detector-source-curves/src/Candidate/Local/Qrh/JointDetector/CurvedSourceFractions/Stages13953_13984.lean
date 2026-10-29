/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13953_13984
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95868777339214,95868336897786,95867896440135,95867455966262,95867015476167,95866574969849,95866134447309,95865693908548,95865253353565,95864812782361,95864372194936,95863931591290,95863490971423,95863050335335,95862609683027,95862169014499,95861728329750,95861287628782,95860846911594,95860406178186,95859965428559,95859524662713,95859083880648,95858643082364,95858202267862,95857761437141,95857320590202,95856879727045,95856438847670,95855997952078,95855557040268,95855116112241,95854675167997]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13952+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13953 := params 0
abbrev ray13953 := rays 0
def bank13953 : Fin 1 → Cell := oneBank p13953 ray13953
theorem signs13953 : ∀ j, Signs p13953 (bank13953 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13954 := params 1
abbrev ray13954 := rays 1
def bank13954 : Fin 1 → Cell := oneBank p13954 ray13954
theorem signs13954 : ∀ j, Signs p13954 (bank13954 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13955 := params 2
abbrev ray13955 := rays 2
def bank13955 : Fin 1 → Cell := oneBank p13955 ray13955
theorem signs13955 : ∀ j, Signs p13955 (bank13955 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13956 := params 3
abbrev ray13956 := rays 3
def bank13956 : Fin 1 → Cell := oneBank p13956 ray13956
theorem signs13956 : ∀ j, Signs p13956 (bank13956 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13957 := params 4
abbrev ray13957 := rays 4
def bank13957 : Fin 1 → Cell := oneBank p13957 ray13957
theorem signs13957 : ∀ j, Signs p13957 (bank13957 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13958 := params 5
abbrev ray13958 := rays 5
def bank13958 : Fin 1 → Cell := oneBank p13958 ray13958
theorem signs13958 : ∀ j, Signs p13958 (bank13958 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13959 := params 6
abbrev ray13959 := rays 6
def bank13959 : Fin 1 → Cell := oneBank p13959 ray13959
theorem signs13959 : ∀ j, Signs p13959 (bank13959 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13960 := params 7
abbrev ray13960 := rays 7
def bank13960 : Fin 1 → Cell := oneBank p13960 ray13960
theorem signs13960 : ∀ j, Signs p13960 (bank13960 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13961 := params 8
abbrev ray13961 := rays 8
def bank13961 : Fin 1 → Cell := oneBank p13961 ray13961
theorem signs13961 : ∀ j, Signs p13961 (bank13961 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13962 := params 9
abbrev ray13962 := rays 9
def bank13962 : Fin 1 → Cell := oneBank p13962 ray13962
theorem signs13962 : ∀ j, Signs p13962 (bank13962 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13963 := params 10
abbrev ray13963 := rays 10
def bank13963 : Fin 1 → Cell := oneBank p13963 ray13963
theorem signs13963 : ∀ j, Signs p13963 (bank13963 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13964 := params 11
abbrev ray13964 := rays 11
def bank13964 : Fin 1 → Cell := oneBank p13964 ray13964
theorem signs13964 : ∀ j, Signs p13964 (bank13964 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13965 := params 12
abbrev ray13965 := rays 12
def bank13965 : Fin 1 → Cell := oneBank p13965 ray13965
theorem signs13965 : ∀ j, Signs p13965 (bank13965 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13966 := params 13
abbrev ray13966 := rays 13
def bank13966 : Fin 1 → Cell := oneBank p13966 ray13966
theorem signs13966 : ∀ j, Signs p13966 (bank13966 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13967 := params 14
abbrev ray13967 := rays 14
def bank13967 : Fin 1 → Cell := oneBank p13967 ray13967
theorem signs13967 : ∀ j, Signs p13967 (bank13967 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13968 := params 15
abbrev ray13968 := rays 15
def bank13968 : Fin 1 → Cell := oneBank p13968 ray13968
theorem signs13968 : ∀ j, Signs p13968 (bank13968 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13969 := params 16
abbrev ray13969 := rays 16
def bank13969 : Fin 1 → Cell := oneBank p13969 ray13969
theorem signs13969 : ∀ j, Signs p13969 (bank13969 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13970 := params 17
abbrev ray13970 := rays 17
def bank13970 : Fin 1 → Cell := oneBank p13970 ray13970
theorem signs13970 : ∀ j, Signs p13970 (bank13970 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13971 := params 18
abbrev ray13971 := rays 18
def bank13971 : Fin 1 → Cell := oneBank p13971 ray13971
theorem signs13971 : ∀ j, Signs p13971 (bank13971 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13972 := params 19
abbrev ray13972 := rays 19
def bank13972 : Fin 1 → Cell := oneBank p13972 ray13972
theorem signs13972 : ∀ j, Signs p13972 (bank13972 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13973 := params 20
abbrev ray13973 := rays 20
def bank13973 : Fin 1 → Cell := oneBank p13973 ray13973
theorem signs13973 : ∀ j, Signs p13973 (bank13973 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13974 := params 21
abbrev ray13974 := rays 21
def bank13974 : Fin 1 → Cell := oneBank p13974 ray13974
theorem signs13974 : ∀ j, Signs p13974 (bank13974 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13975 := params 22
abbrev ray13975 := rays 22
def bank13975 : Fin 1 → Cell := oneBank p13975 ray13975
theorem signs13975 : ∀ j, Signs p13975 (bank13975 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13976 := params 23
abbrev ray13976 := rays 23
def bank13976 : Fin 1 → Cell := oneBank p13976 ray13976
theorem signs13976 : ∀ j, Signs p13976 (bank13976 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13977 := params 24
abbrev ray13977 := rays 24
def bank13977 : Fin 1 → Cell := oneBank p13977 ray13977
theorem signs13977 : ∀ j, Signs p13977 (bank13977 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13978 := params 25
abbrev ray13978 := rays 25
def bank13978 : Fin 1 → Cell := oneBank p13978 ray13978
theorem signs13978 : ∀ j, Signs p13978 (bank13978 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13979 := params 26
abbrev ray13979 := rays 26
def bank13979 : Fin 1 → Cell := oneBank p13979 ray13979
theorem signs13979 : ∀ j, Signs p13979 (bank13979 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13980 := params 27
abbrev ray13980 := rays 27
def bank13980 : Fin 1 → Cell := oneBank p13980 ray13980
theorem signs13980 : ∀ j, Signs p13980 (bank13980 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13981 := params 28
abbrev ray13981 := rays 28
def bank13981 : Fin 1 → Cell := oneBank p13981 ray13981
theorem signs13981 : ∀ j, Signs p13981 (bank13981 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13982 := params 29
abbrev ray13982 := rays 29
def bank13982 : Fin 1 → Cell := oneBank p13982 ray13982
theorem signs13982 : ∀ j, Signs p13982 (bank13982 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13983 := params 30
abbrev ray13983 := rays 30
def bank13983 : Fin 1 → Cell := oneBank p13983 ray13983
theorem signs13983 : ∀ j, Signs p13983 (bank13983 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13984 := params 31
abbrev ray13984 := rays 31
def bank13984 : Fin 1 → Cell := oneBank p13984 ray13984
theorem signs13984 : ∀ j, Signs p13984 (bank13984 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13953_13984
