/- Repeated marks: fork of Collet's final-stage module CountMonotonicity (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
import Submissions.arvi_repeated_marks_20261024.FinalReturn.CountAdmission
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.RepeatedMarks.Return
open QRH.Record1252270103Return
noncomputable section


theorem C0_hasDerivAt (b : CountBranch) (p : ℝ) :
 HasDerivAt (C0 b) (derivativeC b) p := by
 have hp := hasDerivAt_id p
 by_cases hc : isCap b = true
 · convert (hasDerivAt_const p (1:ℝ)).sub ((hp.const_mul 2).mul_const (branchZ b)) using 1
   · funext z; simp [C0,hc]
   · simp [derivativeC,hc] <;> ring
 · convert (hasDerivAt_const p (1:ℝ)).sub (((hp.const_mul 2).mul_const (branchB b)).div_const (branchL b)) using 1
   · funext z; simp [C0,hc]
   · simp [derivativeC,hc] <;> ring

theorem A_hasDerivAt (b : CountBranch) (p : ℝ) :
 HasDerivAt (A b) (derivativeA b) p := by
 have hp := hasDerivAt_id p
 by_cases hc : isCap b = true
 · convert hasDerivAt_const p (2:ℝ) using 1
   · funext z;simp [A,hc]
   · simp [derivativeA,hc]
 · convert (hasDerivAt_const p (2:ℝ)).sub ((hp.const_mul 4).div_const (branchL b)) using 1
   · funext z; simp [A,hc]
   · simp [derivativeA,hc] <;> ring

theorem D_hasDerivAt (b : CountBranch) (p : ℝ) :
 HasDerivAt (D b) (derivativeD b) p := by
 have hp := hasDerivAt_id p
 by_cases hc : isCap b = true
 · convert (hasDerivAt_const p (3:ℝ)).sub hp using 1 <;> (try funext z) <;> (try simp [D,derivativeD,hc]) <;> ring
 · convert ((hasDerivAt_const p (3:ℝ)).sub hp).sub ((hp.const_mul 4).div_const (branchL b)) using 1
   · funext z; simp [D,hc]
   · simp [derivativeD,hc] <;> ring

theorem U_hasDerivAt (b : CountBranch) (p : ℝ) :
 HasDerivAt (U b) (derivativeU b p) p := by
 convert ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)).mul (C0_hasDerivAt b p) using 1
 · funext z;rfl
 · dsimp [derivativeU] <;> ring

theorem J_hasDerivAt (b : CountBranch) (hb : b≠.old) (δ p : ℝ) :
 HasDerivAt (countJ b δ) (derivativeJ b δ p) p := by
 have h1 := (hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)
 convert ((D_hasDerivAt b p).const_mul (V δ)).add ((h1.mul (A_hasDerivAt b p)).const_mul δ) using 1
 · funext z;rw [branch_J b hb];dsimp [V];ring
 · dsimp [derivativeJ] <;> ring

theorem branchCount_ratio (b : CountBranch) (hb : b≠.old) {δ p : ℝ}
 (hj : countJ b δ p≠0) :
 branchCount b δ p=1-δ+V δ*δ*(U b p/countJ b δ p) := by
 unfold branchCount
 rw [branch_N b hb]
 dsimp [V]
 field_simp
 <;> ring

theorem branchCount_hasDerivAt (b : CountBranch) (hb : b≠.old) {δ p : ℝ}
 (hj : countJ b δ p≠0) :
 HasDerivAt (branchCount b δ)
 (V δ*δ*(-(U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p))/(countJ b δ p)^2) p := by
 have hq := (U_hasDerivAt b p).div (J_hasDerivAt b hb δ p) hj
 have hn := (J_hasDerivAt b hb δ p).continuousAt.eventually_ne hj
 have he : branchCount b δ =ᶠ[nhds p] (fun z=>1-δ+V δ*δ*(U b z/countJ b δ z)) :=
   hn.mono (fun z hz=>branchCount_ratio b hb hz)
 apply HasDerivAt.congr_of_eventuallyEq _ he
 convert (hasDerivAt_const p (1-δ)).add (hq.const_mul (V δ*δ)) using 1 <;> (try funext z) <;> ring

theorem branchCount_antitoneOn (b : CountBranch) (hb : b≠.old) {δ lo : ℝ}
 (hδ : 0≤δ) (hδhi : δ≤5/6)
 (hg : ∀p∈Set.Icc lo (1/2),∀j:Fin 15,0<admissionGuard b δ p j) :
 AntitoneOn (branchCount b δ) (Set.Icc lo (1/2)) := by
 have hj (p : ℝ) (hp : p∈Set.Icc lo (1/2)) : 0<countJ b δ p :=
  (admitted_witness_ranges b hb (hg p hp)).2.1
 have hm (p : ℝ) (hp : p∈Set.Icc lo (1/2)) :
  0≤U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p := by
  have hh := hg p hp 11
  have hpos : 0<U b p*derivativeJ b δ p-derivativeU b p*countJ b δ p := by
   cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hh
  exact hpos.le
 have hh (p : ℝ) (hp : p∈Set.Icc lo (1/2)) := branchCount_hasDerivAt b hb (hj p hp).ne'
 apply antitoneOn_of_deriv_nonpos (convex_Icc lo (1/2))
 · intro p hp;exact (hh p hp).continuousAt.continuousWithinAt
 · intro p hp;exact (hh p (interior_subset hp)).differentiableAt.differentiableWithinAt
 · intro p hp
   rw [(hh p (interior_subset hp)).deriv]
   apply div_nonpos_of_nonpos_of_nonneg
   · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by dsimp [V];linarith) hδ) (neg_nonpos.mpr (hm p (interior_subset hp)))
   · exact sq_nonneg _
end
end QRH.RepeatedMarks.Return
#print axioms QRH.RepeatedMarks.Return.branchCount_antitoneOn
