/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialProjectedRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.SlotDictionary
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.ActualEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentHeckeExpansion ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103Restoration
open QRH.Record1252270103Source.Collision
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem sum_pool_functions (S : ι→Finset (Ideal O)) (f : (ι→Ideal O)→ℂ) :
    (∑v : (∀i,S i),f (fun i=>v i))=∑v∈Fintype.piFinset S,f v := by
  apply Finset.sum_bij (fun v _=>fun i=>(v i:Ideal O))
  · intro v hv
    exact Fintype.mem_piFinset.mpr (fun i=>(v i).property)
  · intro v hv w hw he
    funext i
    exact Subtype.ext (congrFun he i)
  · intro v hv
    exact ⟨fun i=>⟨v i,Fintype.mem_piFinset.mp hv i⟩,Finset.mem_univ _,rfl⟩
  · intro v hv
    rfl

theorem markedSlotSum_eq_pool (η : Character) (m A z : O) (t : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) :
    markedSlotSum η m A z t S β=
      ∑v∈Fintype.piFinset S,squarefreeIndicator (∏i,v i)*
        ∏i,(β i (v i)*rowWeight η m A z t (v i)) := by
  unfold markedSlotSum
  simpa only [map_prod,Finset.prod_mul_distrib,mul_assoc] using
    sum_pool_functions S (fun v=>squarefreeIndicator (∏i,v i)*
      ∏i,(β i (v i)*rowWeight η m A z t (v i)))

/-- Exact row dictionary for the injective marked polynomial, including zeros. -/
theorem markedPositiveRow_factor (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O))
    (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms) (hp : ∀p∈atoms,Prime p)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0≤P i) :
    markedPositiveRow η m A z W₁ W₂ b S β P t X₁ X₂=
      ((Real.sqrt (X₁*X₂):ℂ)⁻¹*squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂)*
        injectiveTuplePolynomial
          (fun i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p) := by
  rw [normalized_injective_slot_dictionary η m A z t S β P atoms hS hp]
  unfold markedPositiveRow
  rw [markedSlotSum_eq_pool,Real.sqrt_mul (mul_pos hX₁ hX₂).le,
    Real.sqrt_prod Finset.univ (fun i _=>hP i)]
  simp only [Complex.ofReal_mul,Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem weightedPlain_marked_row_norm (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms) (hp : ∀p∈atoms,Prime p)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0≤P i) (hΦ : ∀x,0≤(Φ x).re) :
    ‖weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ K z*
      injectiveTuplePolynomial
        (fun i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p)‖^2=
      if keep z then ‖markedPositiveRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  rw [markedPositiveRow_factor η m A z t W₁ W₂ b S β P X₁ X₂ atoms hS hp hX₁ hX₂ hP]
  unfold weightedPlain
  by_cases hz : keep z
  · simp only [hz,ite_true,mul_assoc,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
    ring
  · simp [hz]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.markedPositiveRow_factor
#print axioms QRH.Record1252270103Low.weightedPlain_marked_row_norm
