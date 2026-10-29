/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13313_13344
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96147323437564,96146893420687,96146463387451,96146033337856,96145603271902,96145173189590,96144743090920,96144312975892,96143882844507,96143452696764,96143022532664,96142592352207,96142162155394,96141731942224,96141301712698,96140871466816,96140441204579,96140010925986,96139580631038,96139150319735,96138719992077,96138289648065,96137859287699,96137428910979,96136998517905,96136568108477,96136137682696,96135707240562,96135276782075,96134846307235,96134415816043,96133985308499,96133554784603]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13312+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13313 := params 0
abbrev ray13313 := rays 0
def bank13313 : Fin 1 → Cell := oneBank p13313 ray13313
theorem signs13313 : ∀ j, Signs p13313 (bank13313 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13314 := params 1
abbrev ray13314 := rays 1
def bank13314 : Fin 1 → Cell := oneBank p13314 ray13314
theorem signs13314 : ∀ j, Signs p13314 (bank13314 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13315 := params 2
abbrev ray13315 := rays 2
def bank13315 : Fin 1 → Cell := oneBank p13315 ray13315
theorem signs13315 : ∀ j, Signs p13315 (bank13315 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13316 := params 3
abbrev ray13316 := rays 3
def bank13316 : Fin 1 → Cell := oneBank p13316 ray13316
theorem signs13316 : ∀ j, Signs p13316 (bank13316 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13317 := params 4
abbrev ray13317 := rays 4
def bank13317 : Fin 1 → Cell := oneBank p13317 ray13317
theorem signs13317 : ∀ j, Signs p13317 (bank13317 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13318 := params 5
abbrev ray13318 := rays 5
def bank13318 : Fin 1 → Cell := oneBank p13318 ray13318
theorem signs13318 : ∀ j, Signs p13318 (bank13318 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13319 := params 6
abbrev ray13319 := rays 6
def bank13319 : Fin 1 → Cell := oneBank p13319 ray13319
theorem signs13319 : ∀ j, Signs p13319 (bank13319 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13320 := params 7
abbrev ray13320 := rays 7
def bank13320 : Fin 1 → Cell := oneBank p13320 ray13320
theorem signs13320 : ∀ j, Signs p13320 (bank13320 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13321 := params 8
abbrev ray13321 := rays 8
def bank13321 : Fin 1 → Cell := oneBank p13321 ray13321
theorem signs13321 : ∀ j, Signs p13321 (bank13321 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13322 := params 9
abbrev ray13322 := rays 9
def bank13322 : Fin 1 → Cell := oneBank p13322 ray13322
theorem signs13322 : ∀ j, Signs p13322 (bank13322 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13323 := params 10
abbrev ray13323 := rays 10
def bank13323 : Fin 1 → Cell := oneBank p13323 ray13323
theorem signs13323 : ∀ j, Signs p13323 (bank13323 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13324 := params 11
abbrev ray13324 := rays 11
def bank13324 : Fin 1 → Cell := oneBank p13324 ray13324
theorem signs13324 : ∀ j, Signs p13324 (bank13324 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13325 := params 12
abbrev ray13325 := rays 12
def bank13325 : Fin 1 → Cell := oneBank p13325 ray13325
theorem signs13325 : ∀ j, Signs p13325 (bank13325 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13326 := params 13
abbrev ray13326 := rays 13
def bank13326 : Fin 1 → Cell := oneBank p13326 ray13326
theorem signs13326 : ∀ j, Signs p13326 (bank13326 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13327 := params 14
abbrev ray13327 := rays 14
def bank13327 : Fin 1 → Cell := oneBank p13327 ray13327
theorem signs13327 : ∀ j, Signs p13327 (bank13327 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13328 := params 15
abbrev ray13328 := rays 15
def bank13328 : Fin 1 → Cell := oneBank p13328 ray13328
theorem signs13328 : ∀ j, Signs p13328 (bank13328 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13329 := params 16
abbrev ray13329 := rays 16
def bank13329 : Fin 1 → Cell := oneBank p13329 ray13329
theorem signs13329 : ∀ j, Signs p13329 (bank13329 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13330 := params 17
abbrev ray13330 := rays 17
def bank13330 : Fin 1 → Cell := oneBank p13330 ray13330
theorem signs13330 : ∀ j, Signs p13330 (bank13330 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13331 := params 18
abbrev ray13331 := rays 18
def bank13331 : Fin 1 → Cell := oneBank p13331 ray13331
theorem signs13331 : ∀ j, Signs p13331 (bank13331 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13332 := params 19
abbrev ray13332 := rays 19
def bank13332 : Fin 1 → Cell := oneBank p13332 ray13332
theorem signs13332 : ∀ j, Signs p13332 (bank13332 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13333 := params 20
abbrev ray13333 := rays 20
def bank13333 : Fin 1 → Cell := oneBank p13333 ray13333
theorem signs13333 : ∀ j, Signs p13333 (bank13333 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13334 := params 21
abbrev ray13334 := rays 21
def bank13334 : Fin 1 → Cell := oneBank p13334 ray13334
theorem signs13334 : ∀ j, Signs p13334 (bank13334 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13335 := params 22
abbrev ray13335 := rays 22
def bank13335 : Fin 1 → Cell := oneBank p13335 ray13335
theorem signs13335 : ∀ j, Signs p13335 (bank13335 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13336 := params 23
abbrev ray13336 := rays 23
def bank13336 : Fin 1 → Cell := oneBank p13336 ray13336
theorem signs13336 : ∀ j, Signs p13336 (bank13336 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13337 := params 24
abbrev ray13337 := rays 24
def bank13337 : Fin 1 → Cell := oneBank p13337 ray13337
theorem signs13337 : ∀ j, Signs p13337 (bank13337 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13338 := params 25
abbrev ray13338 := rays 25
def bank13338 : Fin 1 → Cell := oneBank p13338 ray13338
theorem signs13338 : ∀ j, Signs p13338 (bank13338 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13339 := params 26
abbrev ray13339 := rays 26
def bank13339 : Fin 1 → Cell := oneBank p13339 ray13339
theorem signs13339 : ∀ j, Signs p13339 (bank13339 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13340 := params 27
abbrev ray13340 := rays 27
def bank13340 : Fin 1 → Cell := oneBank p13340 ray13340
theorem signs13340 : ∀ j, Signs p13340 (bank13340 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13341 := params 28
abbrev ray13341 := rays 28
def bank13341 : Fin 1 → Cell := oneBank p13341 ray13341
theorem signs13341 : ∀ j, Signs p13341 (bank13341 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13342 := params 29
abbrev ray13342 := rays 29
def bank13342 : Fin 1 → Cell := oneBank p13342 ray13342
theorem signs13342 : ∀ j, Signs p13342 (bank13342 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13343 := params 30
abbrev ray13343 := rays 30
def bank13343 : Fin 1 → Cell := oneBank p13343 ray13343
theorem signs13343 : ∀ j, Signs p13343 (bank13343 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13344 := params 31
abbrev ray13344 := rays 31
def bank13344 : Fin 1 → Cell := oneBank p13344 ray13344
theorem signs13344 : ∀ j, Signs p13344 (bank13344 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13313_13344
