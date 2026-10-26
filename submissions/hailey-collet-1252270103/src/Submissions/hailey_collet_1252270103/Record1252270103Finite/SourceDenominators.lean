/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceContinuous
set_option autoImplicit false
namespace Record1252270103Finite

theorem density_denominators_positive {ν L:ℝ} (hν:ν∈Set.Icc (1/2) (3/4)) (hL:1<L) :
 0<15-6*ν ∧ 0<115-54*ν ∧ 0<185-138*ν ∧
 0<L*(15-6*ν)-10 ∧ 0<10+3*(5-6*ν) ∧
 0<L*(10+3*(5-6*ν))-(10+2*(5-6*ν)) := by
 have ht : 0<15-6*ν := by linarith [hν.2]
 have hw : 0<5-6*ν := by linarith [hν.2]
 have hL1 : 0<(L-1)*(15-6*ν) := mul_pos (sub_pos.mpr hL) ht
 have hL2 : 0<(L-1)*(10+3*(5-6*ν)) := mul_pos (sub_pos.mpr hL) (by linarith)
 constructor
 · exact ht
 constructor
 · linarith [hν.2]
 constructor
 · linarith [hν.2]
 constructor
 · nlinarith [hν.2]
 constructor
 · linarith
 · nlinarith
#print axioms density_denominators_positive
end Record1252270103Finite
