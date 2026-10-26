/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Joint finite-family squarefree restoration with row-dependent positive raw scales.
The divisor union is priced once, without a row-cardinality payment. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.FamilyRestoration
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentAbsoluteEnergy
open Record1252270103Source QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O

variable {ι Row : Type*} [Fintype ι]

lemma hole_finite_family_variable
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : Row→ℝ) (hX : ∀u∈rows,0<X₁ u ∧ 0<X₂ u) (E : ℝ)
    (hE : ∀D∈mobiusPool,(∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ S β P (t u) (X₁ u/Ideal.absNorm (mobiusPair D).1)
        (X₂ u/Ideal.absNorm (mobiusPair D).2)‖^2*weight u)≤E) :
    (∑u∈rows,‖ordinaryHolePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)‖^2*weight u)≤holeDeletionMass^2*E := by
  have he : (∑u∈rows,‖ordinaryHolePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)‖^2*weight u)=
      ∑u∈rows,‖∑D∈mobiusPool,
        (mobiusSign D*rowWeight (η u) (m u) (A u) (z u) (t u)
          ((mobiusPair D).1*(mobiusPair D).2)/(Real.sqrt (pairNorm (mobiusPair D)):ℂ))*
        positiveSlotRow (η u) (m u) (A u) (z u) W₁ W₂ S β P (t u)
          (X₁ u/Ideal.absNorm (mobiusPair D).1) (X₂ u/Ideal.absNorm (mobiusPair D).2)‖^2*weight u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hole_positive_row _ _ _ _ W₁ W₂ b hs₁ hs₂ S β P hP _ _ _ (hX u hu).1 (hX u hu).2]
  rw [he]
  apply finite_weighted_energy mobiusPool rows
    (fun D=>(Real.sqrt (pairNorm (mobiusPair D)))⁻¹) _ _ weight E
    (fun D _=>inv_nonneg.mpr (Real.sqrt_nonneg _)) hw ?_ hE
  intro D hD u hu
  rw [norm_div,norm_mul]
  simp only [mobiusSign,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (rowWeight_norm_le_one_all _ _ _ _ _ _)
    (Real.sqrt_nonneg _)).trans_eq (one_div _)

def familyDivisorPool (rows : Finset Row) (b : ℝ) (X₁ X₂ : Row→ℝ) : Finset IdealPair :=
  rows.biUnion (fun u=>divisorPool (holePairPool b (X₁ u) (X₂ u)))

lemma familyDivisorPool_good {rows : Finset Row} {b : ℝ} {X₁ X₂ : Row→ℝ}
    {d : IdealPair} (hd : d∈familyDivisorPool rows b X₁ X₂) : GoodPair d := by
  classical
  obtain ⟨u,hu,hd⟩:=Finset.mem_biUnion.mp hd
  exact divisorPool_hole_good hd

lemma familyDivisorPool_norm {rows : Finset Row} {b C : ℝ} {X₁ X₂ : Row→ℝ}
    (hcap : ∀u∈rows,b^2*X₁ u*X₂ u≤C) {d : IdealPair}
    (hd : d∈familyDivisorPool rows b X₁ X₂) : pairNorm d≤C := by
  classical
  obtain ⟨u,hu,hd⟩:=Finset.mem_biUnion.mp hd
  exact (divisorPool_norm_bound hd).trans (hcap u hu)

/-- A single raw family estimate covers every pair of divisor shortenings.
Inactive rows of each padded divisor summand stay in that same family. -/
theorem forward_finite_family_variable
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : Row→ℝ) (hX : ∀u∈rows,0<X₁ u ∧ 0<X₂ u) (E : ℝ)
    (hraw : ∀Y₁ Y₂ : Row→ℝ,
      (∀u∈rows,0<Y₁ u ∧ 0<Y₂ u ∧ Y₁ u≤X₁ u ∧ Y₂ u≤X₂ u)→
      (∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
        W₁ W₂ S β P (t u) (Y₁ u) (Y₂ u)‖^2*weight u)≤E) :
    (∑u∈rows,‖squarefreePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)‖^2*weight u)≤
      (∑d∈familyDivisorPool rows b X₁ X₂,
        |(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d))^2*(holeDeletionMass^2*E) := by
  classical
  let D:=familyDivisorPool rows b X₁ X₂
  let w:=fun d : IdealPair=>|(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d)
  let c:=fun (d : IdealPair) (u : Row)=>
    if d∈divisorPool (holePairPool b (X₁ u) (X₂ u)) then
      (forwardKernel d.1 d.2:ℂ)*rowWeight (η u) (m u) (A u) (z u) (t u) (d.1*d.2)/
        (Real.sqrt (pairNorm d):ℂ) else 0
  let f:=fun (d : IdealPair) (u : Row)=>ordinaryHolePositiveSlotRow (η u) (m u) (A u) (z u)
    W₁ W₂ b S β P (t u) (X₁ u/Ideal.absNorm d.1) (X₂ u/Ideal.absNorm d.2)
  have he : (∑u∈rows,‖squarefreePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)‖^2*weight u)=
      ∑u∈rows,‖∑d∈D,c d u*f d u‖^2*weight u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [forward_hole_positive_row _ _ _ _ W₁ W₂ b S β P hP _ _ _ (hX u hu).1 (hX u hu).2]
    have hsub : divisorPool (holePairPool b (X₁ u) (X₂ u))⊆D := by
      intro d hd
      exact Finset.mem_biUnion.mpr ⟨u,hu,hd⟩
    have hh := Finset.sum_subset hsub (f:=fun d=>c d u*f d u)
      (by intro d hd hn;simp [c,hn])
    have hh' : (∑d∈divisorPool (holePairPool b (X₁ u) (X₂ u)),
        (forwardKernel d.1 d.2:ℂ)*rowWeight (η u) (m u) (A u) (z u) (t u) (d.1*d.2)/
          (Real.sqrt (pairNorm d):ℂ)*f d u)=∑d∈D,c d u*f d u := by
      rw [←hh]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [c,if_pos hd]
    change ‖_‖^2*weight u=‖_‖^2*weight u
    rw [hh']
  rw [he]
  apply finite_weighted_energy D rows w c f weight (holeDeletionMass^2*E)
    (fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw
  · intro d hd u hu
    dsimp [c]
    split_ifs
    · rw [norm_div,norm_mul,Complex.norm_intCast,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right (abs_nonneg _) (rowWeight_norm_le_one_all _ _ _ _ _ _))
        (Real.sqrt_nonneg _)
    · simp only [norm_zero];exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · intro d hd
    have hg:=familyDivisorPool_good hd
    have hY : ∀u∈rows,0<X₁ u/Ideal.absNorm d.1 ∧ 0<X₂ u/Ideal.absNorm d.2 := by
      intro u hu
      exact ⟨(shorten_positive (hX u hu).1 hg.1).1,(shorten_positive (hX u hu).2 hg.2.1).1⟩
    apply hole_finite_family_variable rows η m A z t weight hw W₁ W₂ b hs₁ hs₂ S β P hP
      (fun u=>X₁ u/Ideal.absNorm d.1) (fun u=>X₂ u/Ideal.absNorm d.2) hY E
    intro Q hQ
    apply hraw
    intro u hu
    have h₁:=shorten_positive (hX u hu).1 hg.1
    have h₂:=shorten_positive (hX u hu).2 hg.2.1
    have h₃:=shorten_positive h₁.1 (subsetProduct_nonzero Q.1)
    have h₄:=shorten_positive h₂.1 (subsetProduct_nonzero Q.2)
    exact ⟨h₃.1,h₄.1,h₃.2.trans h₁.2,h₄.2.trans h₂.2⟩

theorem forward_finite_family_variable_rankin
    (rows : Finset Row) (η : Row→Character) (m A z : Row→O) (t weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (hP : ∀i,0<P i)
    (X₁ X₂ : Row→ℝ) (hX : ∀u∈rows,0<X₁ u ∧ 0<X₂ u) (E : ℝ) (hE : 0≤E)
    (δ B U : ℝ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : ∀u∈rows,b^2*X₁ u*X₂ u≤U^B)
    (hraw : ∀Y₁ Y₂ : Row→ℝ,
      (∀u∈rows,0<Y₁ u ∧ 0<Y₂ u ∧ Y₁ u≤X₁ u ∧ Y₂ u≤X₂ u)→
      (∑u∈rows,‖positiveSlotRow (η u) (m u) (A u) (z u)
        W₁ W₂ S β P (t u) (Y₁ u) (Y₂ u)‖^2*weight u)≤E) :
    (∑u∈rows,‖squarefreePositiveSlotRow (η u) (m u) (A u) (z u)
      W₁ W₂ b S β P (t u) (X₁ u) (X₂ u)‖^2*weight u)≤
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
        eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  apply (forward_finite_family_variable rows η m A z t weight hw W₁ W₂ b hs₁ hs₂ S β P hP
    X₁ X₂ hX E hraw).trans
  have hm : (∑d∈familyDivisorPool rows b X₁ X₂,
      |(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d))≤
      (eulerBound 5 (1/2+δ/(B+1))+eulerBound 432 (1/2+δ/(B+1)))*U^δ := by
    apply le_trans _ (good_absolute_rankin_nonnegative δ B U hδ hB hU
      (familyDivisorPool rows b X₁ X₂) (fun d hd=>familyDivisorPool_good hd)
        (fun d hd=>familyDivisorPool_norm hcut hd))
    exact Finset.sum_le_sum (fun d hd=>div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (abs_nonneg _)) (Real.sqrt_nonneg _))
  have hn : 0≤∑d∈familyDivisorPool rows b X₁ X₂,
      |(forwardKernel d.1 d.2:ℝ)|/Real.sqrt (pairNorm d) :=
    Finset.sum_nonneg (fun d _=>div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn hm 2)
    (mul_nonneg (sq_nonneg holeDeletionMass) hE)).trans_eq (by ring)

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.hole_finite_family_variable
#print axioms QRH.Record1252270103Source.Admission.familyDivisorPool_good
#print axioms QRH.Record1252270103Source.Admission.familyDivisorPool_norm
#print axioms QRH.Record1252270103Source.Admission.forward_finite_family_variable
#print axioms QRH.Record1252270103Source.Admission.forward_finite_family_variable_rankin
