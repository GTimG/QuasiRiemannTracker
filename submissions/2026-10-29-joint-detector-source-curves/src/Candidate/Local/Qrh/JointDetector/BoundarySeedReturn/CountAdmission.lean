/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
/- Repeated marks: fork of Collet's final-stage module CountAdmission (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): namespace Qrh.JointDetector.BoundarySeedReturn; three count branches -/
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.Facts
import Submissions.hailey_collet_1252270103.Record1252270103Return.CountCurve
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace Qrh.JointDetector.BoundarySeedReturn
open QRH.Record1252270103Return
noncomputable section


def branchCutoff (b : CountBranch) (δ p : ℝ) : ℝ := countT b δ p/countJ b δ p
def branchInverse (b : CountBranch) (δ p : ℝ) : ℝ := RN b δ p/DJ b δ p
def branchPlain (b : CountBranch) (δ p : ℝ) : ℝ := MN b δ p/DJ b δ p
def branchCount (b : CountBranch) (δ p : ℝ) : ℝ := countN b δ p/countJ b δ p

theorem count_crossing_algebra {δ p D A Z U J : ℝ}
 (hD : D=1-p+A) (hU : U=(1-p)*(1-Z))
 (hJ : J=(5/6-δ)*D+δ*(1-p)*A) (hD0 : D≠0) (hJ0 : J≠0) :
 1-δ*(p+(1-p)*((A*(J+δ*U)+(Z-p)*J)/(D*J)))=
 ((1-δ)*J+(5/6-δ)*δ*U)/J := by
 field_simp [hD0,hJ0]
 rw [hJ,hD,hU]
 ring

theorem branch_D (b : CountBranch) (p : ℝ) : D b p=1-p+A b p := by
 cases b <;> simp [D,A,isCap] <;> ring

theorem branch_U (b : CountBranch) (p : ℝ) : U b p=(1-p)*(1-Z b p) := by
 cases b <;> simp [U,C0,Z,isCap]

theorem branch_J (b : CountBranch) (hb : b≠.old) (δ p : ℝ) :
 countJ b δ p=(5/6-δ)*D b p+δ*(1-p)*A b p := by
 cases b <;> simp_all [countJ,V]

theorem branch_N (b : CountBranch) (hb : b≠.old) (δ p : ℝ) :
 countN b δ p=(1-δ)*countJ b δ p+(5/6-δ)*δ*U b p := by
 cases b <;> simp_all [countN,V]

theorem inverse_at_branch_crossing (b : CountBranch) (hb : b≠.old) {δ p : ℝ}
 (hD : 0<D b p) (hJ : 0<countJ b δ p) :
 1-δ*(p+(1-p)*branchInverse b δ p)=branchCount b δ p := by
 unfold branchInverse branchCount RN DJ countT
 rw [branch_N b hb]
 exact count_crossing_algebra (branch_D b p) (branch_U b p) (branch_J b hb δ p) hD.ne' hJ.ne'

theorem long_at_branch_crossing (b : CountBranch) (hb : b≠.old) {δ p : ℝ}
 (hJ : 0<countJ b δ p) :
 1-δ+(5/6-δ)*(branchCutoff b δ p-1)=branchCount b δ p := by
 unfold branchCutoff branchCount countT
 rw [branch_N b hb]
 field_simp [hJ.ne']
 ring

theorem branch_lengths (b : CountBranch) {δ p : ℝ}
 (hD : 0<D b p) (hJ : 0<countJ b δ p) :
 branchInverse b δ p+branchPlain b δ p=branchCutoff b δ p := by
 unfold branchInverse branchPlain branchCutoff MN DJ
 field_simp [hD.ne',hJ.ne']
 ring

/-- The admission guards retain the original cutoff and witness ranges. -/
theorem admitted_witness_ranges (b : CountBranch) (hb : b≠.old) {δ p : ℝ}
 (hg : ∀j:Fin 15,0<admissionGuard b δ p j) :
 0<D b p ∧ 0<countJ b δ p ∧
 1<branchCutoff b δ p ∧ branchCutoff b δ p<12499/10000 ∧
 23/37<branchInverse b δ p ∧ branchInverse b δ p<1 ∧
 lowerM b<branchPlain b δ p ∧ branchPlain b δ p<upperM b := by
 have hD : 0<D b p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 0
 have hJ : 0<countJ b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 3
 have ht0 : 0<countT b δ p-countJ b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 4
 have ht1 : 0<(12499/10000)*countJ b δ p-countT b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 5
 have hr0 : 0<RN b δ p-(23/37)*DJ b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 6
 have hr1 : 0<DJ b δ p-RN b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 7
 have hm0 : 0<MN b δ p-lowerM b*DJ b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 8
 have hm1 : 0<upperM b*DJ b δ p-MN b δ p := by
  cases b <;> first | exact (hb rfl).elim | simpa [admissionGuard] using hg 9
 have hDJ : 0<DJ b δ p := mul_pos hD hJ
 dsimp only [branchCutoff,branchInverse,branchPlain]
 refine ⟨hD,hJ,?_,?_,?_,?_,?_,?_⟩
 · exact (lt_div_iff₀ hJ).mpr (by linarith)
 · exact (div_lt_iff₀ hJ).mpr (by linarith)
 · exact (lt_div_iff₀ hDJ).mpr (by linarith)
 · exact (div_lt_iff₀ hDJ).mpr (by linarith)
 · exact (lt_div_iff₀ hDJ).mpr (by linarith)
 · exact (div_lt_iff₀ hDJ).mpr (by linarith)
end
end Qrh.JointDetector.BoundarySeedReturn
