/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionHighData
namespace Qrh.JointDetector.RepeatedMarks.SourceFractionSigns
set_option autoImplicit false
open FractionArithmetic FractionHighTemplates

structure Params where
 B0 : Fraction
 L0 : Fraction
 c0 : Fraction
 B : Fraction
 L : Fraction
 c : Fraction
 A : Fraction
 q : Fraction

def crossing (p : Params) : Fraction := (p.B0-p.B)/(p.L0-p.L)
def width (p : Params) (k : Fin 2) : Fraction := if k=0 then crossing p else p.c
def U (p : Params) (k : Fin 2) : Fraction := p.A*(width p k-crossing p)
def H (p : Params) (k : Fin 2) : Fraction := 1-6*U p k
def P (p : Params) (k : Fin 2) : Fraction := p.B-p.L*width p k
def S (p : Params) (k : Fin 2) : Fraction := width p k-U p k
def rho : Fraction := 1/10000000000000

/-- Pure integer sign checks of computable unreduced coefficient fractions.
The real source interpretation and its scalar hypotheses are separate. -/
def Signs (p : Params) (r : Fraction) (combined : Bool) : Prop :=
 (∀ i j, 0 ≤ (fast24 (rayCapPower p.B0 p.L0 (1/10) 0 r (crossing p)) p.q (3/4) i j).num) ∧
 (∀ i j, 0 ≤ (fast24 (rayBudgetPower p.B0 p.L0 (1/10) 0 r (crossing p)) p.q (3/4) i j).num) ∧
 (∀ k i j, 0 ≤ (fast20 (rayCapHighPower p.B0 p.L0 (1/10) 0 r
   (H p k) (P p k) (S p k) (U p k) rho) p.q (3/4) i j).num) ∧
 (∀ k i j, 0 ≤ (fast20 (rayBudgetHighPower p.B0 p.L0 (1/10) 0 r
   (H p k) (P p k) (S p k) (U p k) rho) p.q (3/4) i j).num) ∧
 (∀ k i j, 0 ≤ (fast20 (tailPower p.B0 0 r
   (H p k) (P p k) (S p k) (U p k) rho) p.q (3/4) i j).num) ∧
 (combined=true → ∀ k i j, 0 ≤ (fast20 (selectedPower 0 r
   (H p k) (P p k) (S p k) (U p k) rho) p.q (3/4) i j).num)


/-- All scalar range hypotheses are also executable integer sign checks. -/
def Basic (p : Params) (r : Fraction) (combined : Bool) : Prop :=
 0 < r.num ∧ 0 ≤ ((1:Fraction)-r).num ∧ 0 < p.q.num ∧
 0 < ((3/4:Fraction)-p.q).num ∧ 0 ≤ (p.L0-(3/2:Fraction)).num ∧
 (combined=true → 0 ≤ (r*p.q-(500001/1000000:Fraction)).num)

def Certificate (p : Params) (r : Fraction) (combined : Bool) : Prop :=
 Basic p r combined ∧ Signs p r combined

end Qrh.JointDetector.RepeatedMarks.SourceFractionSigns

elab "source_fraction_certificate" : tactic => do
 Lean.Elab.Tactic.evalTactic (← `(tactic| unfold
   Qrh.JointDetector.RepeatedMarks.SourceFractionSigns.Certificate
   Qrh.JointDetector.RepeatedMarks.SourceFractionSigns.Basic
   Qrh.JointDetector.RepeatedMarks.SourceFractionSigns.Signs))
 Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel))
