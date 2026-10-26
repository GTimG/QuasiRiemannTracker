/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual normalized corrected source is paid by its divided centered
cofactors through the finite Newton mass, preserving all row zeros. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalCollisionEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.WeightedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSecondHeightFamily CenteredMomentAbsoluteEnergy
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => ActualEisensteinCubic.O
variable {ι Row : Type*} [Fintype ι]

def newtonCofactorPlain (s : Input ι) (A₁ A₂ R : Ideal O) (b : ℝ)
    (S A : Finset (Ideal O)) (τ : Character) (t : ℝ) (z : O) : ℂ :=
  let d:=newtonDivisorPair S A
  frozenCenteredRow (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂
    (A₁*d.1) (A₂*d.2) b (s.X₁/d.1.absNorm) (s.X₂/d.2.absNorm)
      (s.Y₁/d.1.absNorm) (s.Y₂/d.2.absNorm) ((s.X₁*s.X₂)/pairNorm d)

/-- The only analytic inlet is an actual positive energy for each divided
cofactor; the original corrected source bound is derived by exact expansion. -/
theorem actual_corrected_newton_completed_energy
    (s : Input ι) (P : Finset (Ideal O)) (A₁ A₂ D K R : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (depth : ℕ)
    (τ : Row→Character) (t : Row→ℝ) (z : Row→O) (weight : Row→ℝ)
    (hw : ∀u,0≤weight u) (b : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm)
    (havoid : ∀v : (∀i,s.slots i),∀p∈P,¬p∣∏i,(v i:Ideal O))
    (hsupport : ∀u,∀v : (∀i,s.slots i),markedNewtonCoefficient s K R (τ u) (t u) (z u) v≠0→
      ∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile s.W₁ s.W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
      rowWeight (τ u) (fixedBadMask*idealGenerator R) 1 (z u) (t u) (n.1*n.2)≠0→
      IsCoprime D ((∏i,(v i:Ideal O))*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card)
    (hP : 0<P.card) (hbudget : 2*((idealDividingPool P D).card+(depth:ℝ)+1)≤P.card)
    (E : ℝ) (hE : 0≤E)
    (hchild : ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀rows : Finset Row,
      (∑u∈rows,‖newtonCofactorPlain s A₁ A₂ R b S A (τ u) (t u) (z u)*
        markedNewtonSlots s K R (τ u) (t u) (z u)‖^2*weight u)≤E) :
    (∑'u,‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P))
        R 1 (τ u) (t u) (z u)‖^2*weight u)≤newtonMassBound depth^2*E := by
  let assignments : Finset (Σ _ : Finset (Ideal O),Finset (Ideal O)) :=
    (P.powerset.filter (fun S=>S.card≤depth)).sigma (fun S=>S.powerset)
  let w := fun q : (Σ _ : Finset (Ideal O),Finset (Ideal O))=>positiveNewtonWeight P D q.1 q.2
  let c := fun (q : (Σ _ : Finset (Ideal O),Finset (Ideal O))) (u : Row)=>
    (newtonCoefficient P.card (idealDividingPool P D).card q.1.card:ℂ)*
      rowWeight (τ u) (fixedBadMask*idealGenerator R) 1 (z u) (t u)
        ((newtonDivisorPair q.1 q.2).1*(newtonDivisorPair q.1 q.2).2)/
          (Real.sqrt (pairNorm (newtonDivisorPair q.1 q.2)):ℂ)
  let f := fun (q : (Σ _ : Finset (Ideal O),Finset (Ideal O))) (u : Row)=>
    newtonCofactorPlain s A₁ A₂ R b q.1 q.2 (τ u) (t u) (z u)*
      markedNewtonSlots s K R (τ u) (t u) (z u)
  have hweight (q) (_hq : q∈assignments) : 0≤w q := by
    dsimp only [w,positiveNewtonWeight]
    exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hc (q) (_hq : q∈assignments) (u : Row) : ‖c q u‖≤w q := by
    dsimp only [c,w,positiveNewtonWeight]
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all _ _ _ _ _ _))
      (Real.sqrt_nonneg _)
  have hh := weighted_sum_energy_le_uniform assignments w E c f weight hweight hw hc
    (by
      intro q hq rows
      obtain ⟨hS,hA⟩:=Finset.mem_sigma.mp hq
      exact hchild q.1 hS q.2 hA rows)
  have hr (u : Row) :
      (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
        modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P))
          R 1 (τ u) (t u) (z u)=∑q∈assignments,c q u*f q u := by
    rw [actual_corrected_newton_row s P A₁ A₂ D K R hA₁ hA₂ depth (τ u) (t u) (z u)
      b hb₁ hb₂ hp hN havoid (hsupport u)]
    simp only [assignments,Finset.sum_sigma,c,f,newtonCofactorPlain]
  simp_rw [←hr] at hh
  have hm : (∑q∈assignments,w q)≤newtonMassBound depth := by
    simpa only [assignments,Finset.sum_sigma,w] using
      positive_newton_mass P D depth hP (fun p hpin=>(hp p hpin).ne_zero) hbudget
  have hm0 : 0≤∑q∈assignments,w q := Finset.sum_nonneg hweight
  exact hh.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hm 2) hE)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_corrected_newton_completed_energy
