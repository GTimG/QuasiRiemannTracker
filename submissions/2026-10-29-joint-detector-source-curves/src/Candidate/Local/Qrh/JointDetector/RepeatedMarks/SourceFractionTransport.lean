/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceFractionSigns
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionHighTemplates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceHighSigns
namespace Qrh.JointDetector.RepeatedMarks.SourceFractionSigns
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open FractionArithmetic

noncomputable def Params.real (p : Params) : SourceStep.Params :=
 ⟨p.B0.evalR,p.L0.evalR,p.c0.evalR,p.B.evalR,p.L.evalR,p.c.evalR,p.A.evalR,p.q.evalR⟩

@[simp] theorem eval_crossing (p : Params) :
 (crossing p).eval=SourceStep.crossing p.real := by
 simp [crossing,Params.real,SourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,Fraction.evalR]
@[simp] theorem eval_width (p : Params) (k : Fin 2) :
 (width p k).eval=SourceStep.endpointWidth p.real k := by
 fin_cases k <;> simp [width,SourceStep.endpointWidth,Params.real,Fraction.evalR]
@[simp] theorem eval_U (p : Params) (k : Fin 2) :
 (U p k).eval=SourceStep.endpointU p.real k := by
 simp [U,SourceStep.endpointU,Fraction.evalR,Params.real,eval_width,eval_crossing]
@[simp] theorem eval_H (p : Params) (k : Fin 2) :
 (H p k).eval=SourceStep.endpointH p.real k := by
 simp [H,SourceStep.endpointH,Fraction.evalR,Params.real,eval_U]
@[simp] theorem eval_P (p : Params) (k : Fin 2) :
 (P p k).eval=SourceStep.endpointP p.real k := by
 simp [P,SourceStep.endpointP,Fraction.evalR,Params.real,eval_width]
@[simp] theorem eval_S (p : Params) (k : Fin 2) :
 (S p k).eval=SourceStep.endpointS p.real k := by
 simp [S,SourceStep.endpointS,Fraction.evalR,Params.real,eval_width,eval_U]
@[simp] theorem eval_rho : rho.eval=SourceStep.highRho := by
 norm_num [rho,SourceStep.highRho,Fraction.evalR]

/-- A kernel-checked integer certificate is transported to exactly the
existing real coefficient predicate. No analytic estimate is introduced. -/
theorem Signs.sourceHighSigns {p : Params} {r : Fraction} {combined : Bool}
 (hc : Signs p r combined)
 (hr : 0 < r.evalR) (hrhi : r.evalR ≤ 1)
 (hq : 0 < p.q.evalR) (hqhi : p.q.evalR < 3/4) (hL : 3/2 ≤ p.L0.evalR)
 (hcut : combined=true → (500001/1000000:ℝ) ≤ r.evalR*p.q.evalR) :
 SourceStep.SourceHighSigns p.real r.evalR combined := by
 rcases hc with ⟨hca,hba,hch,hbh,hth,hsh⟩
 refine ⟨hr,hrhi,hq,hqhi,hL,hcut,?_,?_,?_,?_,?_,?_⟩
 · intro i j
   rw [FastBernsteinBox.coefficients24_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hca i j)
   rw [FractionHighTemplates.eval_fast24] at ht
   simp only [FractionHighTemplates.eval_rayCapPower] at ht
   simpa [Fraction.evalR,Params.real] using ht
 · intro i j
   rw [FastBernsteinBox.coefficients24_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hba i j)
   rw [FractionHighTemplates.eval_fast24] at ht
   simp only [FractionHighTemplates.eval_rayBudgetPower] at ht
   simpa [Fraction.evalR,Params.real] using ht
 · intro k i j
   rw [FastBernsteinBox.coefficients20_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hch k i j)
   rw [FractionHighTemplates.eval_fast20] at ht
   simp only [FractionHighTemplates.eval_rayCapHighPower] at ht
   simpa [Fraction.evalR,Params.real] using ht
 · intro k i j
   rw [FastBernsteinBox.coefficients20_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hbh k i j)
   rw [FractionHighTemplates.eval_fast20] at ht
   simp only [FractionHighTemplates.eval_rayBudgetHighPower] at ht
   simpa [Fraction.evalR,Params.real] using ht
 · intro k i j
   rw [FastBernsteinBox.coefficients20_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hth k i j)
   rw [FractionHighTemplates.eval_fast20] at ht
   simp only [FractionHighTemplates.eval_tailPower] at ht
   simpa [Fraction.evalR,Params.real] using ht
 · intro he k i j
   rw [FastBernsteinBox.coefficients20_eq]
   have ht := Fraction.evalR_nonneg_of_num _ (hsh he k i j)
   rw [FractionHighTemplates.eval_fast20] at ht
   simp only [FractionHighTemplates.eval_selectedPower] at ht
   simpa [Fraction.evalR,Params.real] using ht


/-- Full integer-only certificate, including the scalar density/ray ranges. -/
theorem Certificate.sourceHighSigns {p : Params} {r : Fraction} {combined : Bool}
 (hc : Certificate p r combined) :
 SourceStep.SourceHighSigns p.real r.evalR combined := by
 rcases hc with ⟨⟨hr,hrhi,hq,hqhi,hL,hcut⟩,hs⟩
 apply hs.sourceHighSigns
 · exact Fraction.evalR_pos_of_num _ hr
 · have hh : 0 ≤ 1-r.evalR := by
     simpa [Fraction.evalR] using Fraction.evalR_nonneg_of_num _ hrhi
   linarith
 · exact Fraction.evalR_pos_of_num _ hq
 · have hh : 0 < (3/4:ℝ)-p.q.evalR := by
     simpa [Fraction.evalR] using Fraction.evalR_pos_of_num _ hqhi
   linarith
 · have hh : 0 ≤ p.L0.evalR-(3/2:ℝ) := by
     simpa [Fraction.evalR] using Fraction.evalR_nonneg_of_num _ hL
   linarith
 · intro he
   have hh : 0 ≤ r.evalR*p.q.evalR-(500001/1000000:ℝ) := by
     simpa [Fraction.evalR] using Fraction.evalR_nonneg_of_num _ (hcut he)
   linarith

#print axioms Certificate.sourceHighSigns

#print axioms Signs.sourceHighSigns
end
end Qrh.JointDetector.RepeatedMarks.SourceFractionSigns
