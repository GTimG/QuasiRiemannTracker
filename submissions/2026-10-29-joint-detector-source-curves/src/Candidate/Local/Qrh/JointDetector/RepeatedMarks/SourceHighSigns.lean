/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RayHighCertificate
namespace Qrh.JointDetector.RepeatedMarks.SourceStep
noncomputable section
set_option autoImplicit false
open BernsteinBox HighTemplates AuxHighTemplates

def highRho : ℝ := 1/10000000000000

def endpointWidth (p : Params) (i : Fin 2) : ℝ := if i=0 then crossing p else p.c
def endpointU (p : Params) (i : Fin 2) : ℝ := p.A*(endpointWidth p i-crossing p)
def endpointH (p : Params) (i : Fin 2) : ℝ := 1-6*endpointU p i
def endpointP (p : Params) (i : Fin 2) : ℝ := p.B-p.L*endpointWidth p i
def endpointS (p : Params) (i : Fin 2) : ℝ := endpointWidth p i-endpointU p i

/-- Finite coefficient signs for the ACTUAL two plain branches, full amplitude
range, and both physical width endpoints. The semantic transport to HIGH is
proved separately; this predicate contains no assumed analytic estimate. -/
def SourceHighSigns (p : Params) (r : ℝ) (combined : Bool) : Prop :=
 0 < r ∧ r ≤ 1 ∧ 0 < p.q ∧ p.q < 3/4 ∧ 3/2 ≤ p.L0 ∧
 (combined = true → (500001/1000000:ℝ) ≤ r*p.q) ∧
 (∀ i j, 0 ≤ coefficients (rayCapPower p.B0 p.L0 (1/10) 0 r (crossing p)) p.q (3/4) i j) ∧
 (∀ i j, 0 ≤ coefficients (rayBudgetPower p.B0 p.L0 (1/10) 0 r (crossing p)) p.q (3/4) i j) ∧
 (∀ k i j, 0 ≤ coefficients (rayCapHighPower p.B0 p.L0 (1/10) 0 r
   (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho) p.q (3/4) i j) ∧
 (∀ k i j, 0 ≤ coefficients (rayBudgetHighPower p.B0 p.L0 (1/10) 0 r
   (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho) p.q (3/4) i j) ∧
 (∀ k i j, 0 ≤ coefficients (tailPower p.B0 0 r
   (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho) p.q (3/4) i j) ∧
 (combined = true → ∀ k i j, 0 ≤ coefficients (selectedPower 0 r
   (endpointH p k) (endpointP p k) (endpointS p k) (endpointU p k) highRho) p.q (3/4) i j)

end
end Qrh.JointDetector.RepeatedMarks.SourceStep

/-- Expand only the finite rational scalar certificate. No native evaluator
or external checker is part of the produced Lean proof. -/
macro "source_high_signs" : tactic => `(tactic|
 norm_num [Qrh.JointDetector.RepeatedMarks.SourceStep.SourceHighSigns,
   Qrh.JointDetector.RepeatedMarks.SourceStep.highRho,
   Qrh.JointDetector.RepeatedMarks.SourceStep.endpointWidth,
   Qrh.JointDetector.RepeatedMarks.SourceStep.endpointU,
   Qrh.JointDetector.RepeatedMarks.SourceStep.endpointH,
   Qrh.JointDetector.RepeatedMarks.SourceStep.endpointP,
   Qrh.JointDetector.RepeatedMarks.SourceStep.endpointS,
   Qrh.JointDetector.RepeatedMarks.SourceStep.crossing,
   QRH.SilDensitySplit.Hybrid.cross,
   Qrh.JointDetector.RepeatedMarks.BernsteinBox.coefficients,
   Qrh.JointDetector.RepeatedMarks.BernsteinBox.intervalPower,
   Qrh.JointDetector.RepeatedMarks.HighTemplates.rayCapPower,
   Qrh.JointDetector.RepeatedMarks.HighTemplates.rayBudgetPower,
   Qrh.JointDetector.RepeatedMarks.HighTemplates.rayCapHighPower,
   Qrh.JointDetector.RepeatedMarks.HighTemplates.rayBudgetHighPower,
   Qrh.JointDetector.RepeatedMarks.AuxHighTemplates.tailPower,
   Qrh.JointDetector.RepeatedMarks.AuxHighTemplates.selectedPower,
   Fin.forall_fin_succ,Fin.sum_univ_succ,Nat.choose])
