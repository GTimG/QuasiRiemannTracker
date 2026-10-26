/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The cardinality induction applied to the literal squarefree ordinary energy.
Natural row zeros, the keep predicate and the radial weight remain unchanged. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ActualCoefficients
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Cardinality
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.MarkedSquarefree

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion ConcreteTraceCRT
open Record1252270103Restoration
open Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem whole_normalizer_factor (plain : ℂ) (slot : ι→ℂ) (P : ι→ℝ)
    (X : ℝ) (hX : 0≤X) (hP : ∀i,0≤P i) :
    (Real.sqrt (X*∏i,P i):ℂ)⁻¹*(plain*∏i,slot i)=
      ((Real.sqrt X:ℂ)⁻¹*plain)*(∏i,(Real.sqrt (P i):ℂ)⁻¹*slot i) := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod Finset.univ (fun i _=>hP i)]
  simp only [Complex.ofReal_mul,Complex.ofReal_prod,mul_inv_rev,
    Finset.prod_inv_distrib,Finset.prod_mul_distrib]
  ring

theorem squarefree_row_factor (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b : ℝ) (S : ι→Finset (Ideal O))
    (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0≤P i) :
    squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂=
      ((Real.sqrt (X₁*X₂):ℂ)⁻¹*squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂)*
        ∏i,normalizedSlot η m A z (S i) (β i) t (P i) :=
  whole_normalizer_factor _ _ P _ (mul_pos hX₁ hX₂).le hP

def weightedPlain (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (height : ℝ) (z : O) : ℂ :=
  if keep z then (Real.sqrt ((Φ (‖eisEmbedding z‖^2/height)).re):ℂ)*
    ((Real.sqrt (X₁*X₂):ℂ)⁻¹*squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂)
  else 0

theorem weightedPlain_row_norm (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (height : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0≤P i) (hΦ : ∀x,0≤(Φ x).re) :
    ‖weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ height z*
      (∏i,normalizedSlot η m A z (S i) (β i) t (P i))‖^2=
      if keep z then ‖squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
        (Φ (‖eisEmbedding z‖^2/height)).re else 0 := by
  rw [squarefree_row_factor η m A z t W₁ W₂ b S β P X₁ X₂ hX₁ hX₂ hP]
  unfold weightedPlain
  by_cases hz : keep z
  · simp only [hz,ite_true,mul_assoc,norm_mul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
    ring
  · simp [hz]

/-- A completed positive bound for every projected subset suffices for the
original source. Summability is obtained from finite positive sums; no source
mask or coefficient restriction is treated as an L2 contraction. -/
theorem squarefreeEnergy_of_projected (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (height : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,1≤P i) (hΦ : ∀x,0≤(Φ x).re)
    (B bound : ℝ) (hB : 1≤B) (hbound : 0≤bound)
    (hβ : ∀i,∀I∈S i,‖β i I‖≤B)
    (hp : ∀i,∀I∈S i,I≠0) (hN : ∀i,∀I∈S i,(I.absNorm:ℝ)≤2*P i)
    (K : ℕ) (hK : Fintype.card ι≤K)
    (hproj : ∀rows : Finset O,projectedSubsetBound rows
      (fun z i (I : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) I)
      (weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ height) bound) :
    squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ height≤
      (collisionGrowth B 256 K)^K*bound := by
  let a := fun z i (I : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) I
  let v := fun i (I : atoms)=>‖normalizedPrimeCoeff (S i) (β i) (P i) I‖
  let D := weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ height
  have he (i : ι) : (∑I : atoms,(v i I)^2)≤256*B^2 := by
    dsimp only [v]
    rw [Finset.sum_coe_sort atoms (fun I=>‖normalizedPrimeCoeff (S i) (β i) (P i) I‖^2)]
    exact normalizedPrimeCoeff_energy atoms (S i) (β i) (P i) B (hP i)
      (zero_le_one.trans hB) (hβ i) (hp i) (hN i)
  have hfinite (rows : Finset O) :
      (∑z∈rows,‖D z*(∏i,∑I : atoms,a z i I)‖^2)≤(collisionGrowth B 256 K)^K*bound := by
    exact full_energy_cardinality rows a v D B 256 bound hB (by norm_num) hbound
      (fun i I=>norm_nonneg _) (fun i I=>normalizedPrimeCoeff_bound (S i) (β i) (P i) B
        (hP i) (zero_le_one.trans hB) (hβ i) I) he
      (fun z _ i I=>normalizedRowCoeff_norm η m A z t (S i) (β i) (P i) I) K hK (hproj rows)
  have hsum (z : O) : (∏i,∑I : atoms,a z i I)=
      ∏i,normalizedSlot η m A z (S i) (β i) t (P i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (normalizedSlot_sum_atoms η m A z t (S i) atoms (β i) (P i) (hS i)).symm
  unfold squarefreeEnergy
  apply Real.tsum_le_of_sum_le
  · intro z
    change 0≤(if keep z then _ else 0)
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ _)
    · exact le_rfl
  · intro rows
    have hh := hfinite rows
    simp_rw [hsum] at hh
    simp_rw [D,weightedPlain_row_norm η m A _ t W₁ W₂ b X₁ X₂ keep Φ height S β P
      hX₁ hX₂ (fun i=>zero_le_one.trans (hP i)) hΦ] at hh
    exact hh

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.whole_normalizer_factor
#print axioms QRH.Record1252270103Source.Collision.weightedPlain_row_norm
#print axioms QRH.Record1252270103Source.Collision.squarefreeEnergy_of_projected
