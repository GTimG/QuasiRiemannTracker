/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12417_12448
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96525836941300,96525422638412,96525008316343,96524593975094,96524179614666,96523765235059,96523350836273,96522936418308,96522521981166,96522107524846,96521693049349,96521278554675,96520864040825,96520449507799,96520034955598,96519620384222,96519205793671,96518791183946,96518376555047,96517961906974,96517547239728,96517132553310,96516717847719,96516303122957,96515888379023,96515473615918,96515058833643,96514644032198,96514229211583,96513814371798,96513399512844,96512984634722,96512569737432]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12416+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12417 := params 0
abbrev ray12417 := rays 0
def bank12417 : Fin 2 → Cell := twoBank p12417 ray12417
theorem signs12417 : ∀ j, Signs p12417 (bank12417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12418 := params 1
abbrev ray12418 := rays 1
def bank12418 : Fin 2 → Cell := twoBank p12418 ray12418
theorem signs12418 : ∀ j, Signs p12418 (bank12418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12419 := params 2
abbrev ray12419 := rays 2
def bank12419 : Fin 2 → Cell := twoBank p12419 ray12419
theorem signs12419 : ∀ j, Signs p12419 (bank12419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12420 := params 3
abbrev ray12420 := rays 3
def bank12420 : Fin 2 → Cell := twoBank p12420 ray12420
theorem signs12420 : ∀ j, Signs p12420 (bank12420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12421 := params 4
abbrev ray12421 := rays 4
def bank12421 : Fin 2 → Cell := twoBank p12421 ray12421
theorem signs12421 : ∀ j, Signs p12421 (bank12421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12422 := params 5
abbrev ray12422 := rays 5
def bank12422 : Fin 2 → Cell := twoBank p12422 ray12422
theorem signs12422 : ∀ j, Signs p12422 (bank12422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12423 := params 6
abbrev ray12423 := rays 6
def bank12423 : Fin 2 → Cell := twoBank p12423 ray12423
theorem signs12423 : ∀ j, Signs p12423 (bank12423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12424 := params 7
abbrev ray12424 := rays 7
def bank12424 : Fin 2 → Cell := twoBank p12424 ray12424
theorem signs12424 : ∀ j, Signs p12424 (bank12424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12425 := params 8
abbrev ray12425 := rays 8
def bank12425 : Fin 2 → Cell := twoBank p12425 ray12425
theorem signs12425 : ∀ j, Signs p12425 (bank12425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12426 := params 9
abbrev ray12426 := rays 9
def bank12426 : Fin 2 → Cell := twoBank p12426 ray12426
theorem signs12426 : ∀ j, Signs p12426 (bank12426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12427 := params 10
abbrev ray12427 := rays 10
def bank12427 : Fin 2 → Cell := twoBank p12427 ray12427
theorem signs12427 : ∀ j, Signs p12427 (bank12427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12428 := params 11
abbrev ray12428 := rays 11
def bank12428 : Fin 2 → Cell := twoBank p12428 ray12428
theorem signs12428 : ∀ j, Signs p12428 (bank12428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12429 := params 12
abbrev ray12429 := rays 12
def bank12429 : Fin 2 → Cell := twoBank p12429 ray12429
theorem signs12429 : ∀ j, Signs p12429 (bank12429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12430 := params 13
abbrev ray12430 := rays 13
def bank12430 : Fin 2 → Cell := twoBank p12430 ray12430
theorem signs12430 : ∀ j, Signs p12430 (bank12430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12431 := params 14
abbrev ray12431 := rays 14
def bank12431 : Fin 2 → Cell := twoBank p12431 ray12431
theorem signs12431 : ∀ j, Signs p12431 (bank12431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12432 := params 15
abbrev ray12432 := rays 15
def bank12432 : Fin 2 → Cell := twoBank p12432 ray12432
theorem signs12432 : ∀ j, Signs p12432 (bank12432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12433 := params 16
abbrev ray12433 := rays 16
def bank12433 : Fin 2 → Cell := twoBank p12433 ray12433
theorem signs12433 : ∀ j, Signs p12433 (bank12433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12434 := params 17
abbrev ray12434 := rays 17
def bank12434 : Fin 2 → Cell := twoBank p12434 ray12434
theorem signs12434 : ∀ j, Signs p12434 (bank12434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12435 := params 18
abbrev ray12435 := rays 18
def bank12435 : Fin 2 → Cell := twoBank p12435 ray12435
theorem signs12435 : ∀ j, Signs p12435 (bank12435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12436 := params 19
abbrev ray12436 := rays 19
def bank12436 : Fin 2 → Cell := twoBank p12436 ray12436
theorem signs12436 : ∀ j, Signs p12436 (bank12436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12437 := params 20
abbrev ray12437 := rays 20
def bank12437 : Fin 2 → Cell := twoBank p12437 ray12437
theorem signs12437 : ∀ j, Signs p12437 (bank12437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12438 := params 21
abbrev ray12438 := rays 21
def bank12438 : Fin 2 → Cell := twoBank p12438 ray12438
theorem signs12438 : ∀ j, Signs p12438 (bank12438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12439 := params 22
abbrev ray12439 := rays 22
def bank12439 : Fin 2 → Cell := twoBank p12439 ray12439
theorem signs12439 : ∀ j, Signs p12439 (bank12439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12440 := params 23
abbrev ray12440 := rays 23
def bank12440 : Fin 2 → Cell := twoBank p12440 ray12440
theorem signs12440 : ∀ j, Signs p12440 (bank12440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12441 := params 24
abbrev ray12441 := rays 24
def bank12441 : Fin 2 → Cell := twoBank p12441 ray12441
theorem signs12441 : ∀ j, Signs p12441 (bank12441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12442 := params 25
abbrev ray12442 := rays 25
def bank12442 : Fin 2 → Cell := twoBank p12442 ray12442
theorem signs12442 : ∀ j, Signs p12442 (bank12442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12443 := params 26
abbrev ray12443 := rays 26
def bank12443 : Fin 2 → Cell := twoBank p12443 ray12443
theorem signs12443 : ∀ j, Signs p12443 (bank12443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12444 := params 27
abbrev ray12444 := rays 27
def bank12444 : Fin 2 → Cell := twoBank p12444 ray12444
theorem signs12444 : ∀ j, Signs p12444 (bank12444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12445 := params 28
abbrev ray12445 := rays 28
def bank12445 : Fin 2 → Cell := twoBank p12445 ray12445
theorem signs12445 : ∀ j, Signs p12445 (bank12445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12446 := params 29
abbrev ray12446 := rays 29
def bank12446 : Fin 2 → Cell := twoBank p12446 ray12446
theorem signs12446 : ∀ j, Signs p12446 (bank12446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12447 := params 30
abbrev ray12447 := rays 30
def bank12447 : Fin 2 → Cell := twoBank p12447 ray12447
theorem signs12447 : ∀ j, Signs p12447 (bank12447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12448 := params 31
abbrev ray12448 := rays 31
def bank12448 : Fin 2 → Cell := twoBank p12448 ray12448
theorem signs12448 : ∀ j, Signs p12448 (bank12448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12417_12448
