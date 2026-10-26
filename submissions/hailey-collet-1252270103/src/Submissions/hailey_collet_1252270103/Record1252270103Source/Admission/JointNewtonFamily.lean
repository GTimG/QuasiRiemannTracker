/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The full heterogeneous corrected family is estimated simultaneously, using
one Newton majorant independent of every row and accumulated divisor. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointNewtonMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.WeightedEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNewtonEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.JointNewton
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentSecondHeightFamily
open CenteredMomentAbsoluteEnergy Record1252270103Source Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered High.GlobalPhysical
local notation "O"=>ActualEisensteinCubic.O

/-- Finite weighted Cauchy, preserving the same simultaneous row family in
all cofactor estimates. Only coefficients may vary freely with the row. -/
theorem weighted_finite_uniform {α ρ : Type*} (assignments : Finset α) (rows : Finset ρ)
    (w : α→ℝ) (E : ℝ) (c f : α→ρ→ℂ) (weight : ρ→ℝ)
    (hw : ∀i∈assignments,0≤w i) (hu : ∀r∈rows,0≤weight r)
    (hc : ∀i∈assignments,∀r∈rows,‖c i r‖≤w i)
    (hE : ∀i∈assignments,∑r∈rows,‖f i r‖^2*weight r≤E) :
    (∑r∈rows,‖∑i∈assignments,c i r*f i r‖^2*weight r)≤(∑i∈assignments,w i)^2*E := by
  calc
    _≤∑r∈rows,(∑i∈assignments,w i)*(∑i∈assignments,w i*(‖f i r‖^2*weight r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have h:=mul_le_mul_of_nonneg_right
        (norm_weighted_sum_sq assignments w (fun i=>c i r) (fun i=>f i r) hw
          (fun i hi=>hc i hi r hr)) (hu r hr)
      simpa only [Finset.sum_mul,mul_assoc] using h
    _=(∑i∈assignments,w i)*(∑i∈assignments,w i*(∑r∈rows,‖f i r‖^2*weight r)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _≤(∑i∈assignments,w i)*(∑i∈assignments,w i*E) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg hw)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hE i hi) (hw i hi)
    _=_ := by rw [←Finset.sum_mul];ring

/-- Actual normalized corrected rows with heterogeneous slot types/Inputs
and moving D, all summed before any family count or analytic admission.
The inlet is the exact simultaneous divided-cofactor family, not a norm
assumption about the corrected source being proved. -/
theorem actual_joint_corrected_newton_finite {Row : Type*}
    (rows : Finset Row) (ι : Row→Type*) [∀u,Fintype (ι u)]
    (s : ∀u,Input (ι u)) (P : Finset (Ideal O)) (A₁ A₂ D K R : Row→Ideal O)
    (hA₁ : ∀u∈rows,A₁ u≠0) (hA₂ : ∀u∈rows,A₂ u≠0) (depth : ℕ)
    (τ : Row→Character) (t : Row→ℝ) (z : Row→O) (weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (b : Row→ℝ)
    (hb₁ : ∀u∈rows,(s u).b₁≤b u) (hb₂ : ∀u∈rows,(s u).b₂≤b u)
    (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm)
    (havoid : ∀u∈rows,∀v : (∀i,(s u).slots i),∀p∈P,¬p∣∏i,(v i:Ideal O))
    (hsupport : ∀u∈rows,∀v : (∀i,(s u).slots i),
      markedNewtonCoefficient (s u) (K u) (R u) (τ u) (t u) (z u) v≠0→
      ∀n∈commonPool (b u) (s u).X₁ (s u).X₂ (s u).Y₁ (s u).Y₂,
      Squarefree (((A₁ u)*n.1)*((A₂ u)*n.2))→
      frozenProfile (s u).W₁ (s u).W₂ (A₁ u) (A₂ u) (s u).X₁ (s u).X₂ (s u).Y₁ (s u).Y₂ n≠0→
      rowWeight (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u) (t u) (n.1*n.2)≠0→
      IsCoprime (D u) ((∏i,(v i:Ideal O))*n.1*n.2) ∧
        (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P ((D u)*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card)
    (hP : 0<P.card)
    (hbudget : ∀u∈rows,2*((idealDividingPool P (D u)).card+(depth:ℝ)+1)≤P.card)
    (E : ℝ) (hE : 0≤E)
    (hchild : ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,
      (∑u∈rows,‖newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) (b u) S A (τ u) (t u) (z u)*
        markedNewtonSlots (s u) (K u) (R u) (τ u) (t u) (z u)‖^2*weight u)≤E) :
    (∑u∈rows,‖(Real.sqrt ((s u).X₁*(s u).X₂*∏i,(s u).P i):ℂ)⁻¹*
      modifiedSourceRow (s u)
        (Collision.markedSourceModifier (A₁ u) (A₂ u) (D u) (K u) (poolCorrection P))
        (R u) 1 (τ u) (t u) (z u)‖^2*weight u)≤newtonMassBound depth^2*E := by
  let assignments : Finset (Σ _ : Finset (Ideal O),Finset (Ideal O)) :=
    (P.powerset.filter (fun S=>S.card≤depth)).sigma (fun S=>S.powerset)
  let w := fun q : (Σ _ : Finset (Ideal O),Finset (Ideal O))=>assignmentWeight P q.1 q.2
  let c := fun (q : (Σ _ : Finset (Ideal O),Finset (Ideal O))) (u : Row)=>
    (newtonCoefficient P.card (idealDividingPool P (D u)).card q.1.card:ℂ)*
      rowWeight (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u) (t u)
        ((newtonDivisorPair q.1 q.2).1*(newtonDivisorPair q.1 q.2).2)/
          (Real.sqrt (pairNorm (newtonDivisorPair q.1 q.2)):ℂ)
  let f := fun (q : (Σ _ : Finset (Ideal O),Finset (Ideal O))) (u : Row)=>
    newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) (b u) q.1 q.2 (τ u) (t u) (z u)*
      markedNewtonSlots (s u) (K u) (R u) (τ u) (t u) (z u)
  have hw' (q) (_hq : q∈assignments) : 0≤w q := assignmentWeight_nonneg P q.1 q.2
  have hc (q) (hq : q∈assignments) (u : Row) (hu : u∈rows) : ‖c q u‖≤w q := by
    obtain ⟨hS,_hA⟩:=Finset.mem_sigma.mp hq
    exact coefficient_majorant P (D u) depth hP (hbudget u hu) q.1 q.2
      (Finset.mem_filter.mp hS).2 _ (fun I=>rowWeight_norm_le_one_all _ _ _ _ _ I)
  have hh:=weighted_finite_uniform assignments rows w E c f weight hw' hw hc (by
    intro q hq
    obtain ⟨hS,hA⟩:=Finset.mem_sigma.mp hq
    exact hchild q.1 hS q.2 hA)
  have hr (u : Row) (hu : u∈rows) :
      (Real.sqrt ((s u).X₁*(s u).X₂*∏i,(s u).P i):ℂ)⁻¹*
        modifiedSourceRow (s u)
          (Collision.markedSourceModifier (A₁ u) (A₂ u) (D u) (K u) (poolCorrection P))
          (R u) 1 (τ u) (t u) (z u)=∑q∈assignments,c q u*f q u := by
    rw [actual_corrected_newton_row (s u) P (A₁ u) (A₂ u) (D u) (K u) (R u)
      (hA₁ u hu) (hA₂ u hu) depth (τ u) (t u) (z u) (b u)
      (hb₁ u hu) (hb₂ u hu) hp hN (havoid u hu) (hsupport u hu)]
    simp only [assignments,Finset.sum_sigma,c,f,newtonCofactorPlain]
  have he : (∑u∈rows,‖(Real.sqrt ((s u).X₁*(s u).X₂*∏i,(s u).P i):ℂ)⁻¹*
      modifiedSourceRow (s u)
        (Collision.markedSourceModifier (A₁ u) (A₂ u) (D u) (K u) (poolCorrection P))
        (R u) 1 (τ u) (t u) (z u)‖^2*weight u)=
      ∑u∈rows,‖∑q∈assignments,c q u*f q u‖^2*weight u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hr u hu]
  rw [he]
  apply hh.trans
  have hm : (∑q∈assignments,w q)≤newtonMassBound depth := by
    simpa only [assignments,Finset.sum_sigma,w] using assignment_mass P depth hP
      (fun p hpin=>(hp p hpin).ne_zero)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg hw') hm 2) hE

end
end QRH.Record1252270103Source.Admission.JointNewton
#print axioms QRH.Record1252270103Source.Admission.JointNewton.weighted_finite_uniform
#print axioms QRH.Record1252270103Source.Admission.JointNewton.actual_joint_corrected_newton_finite
