/- Copyright (c) 2026 Sil. Apache-2.0.
Keep the whole centered difference as one common coefficient vector.
The zero-frequency estimate is then applied to that vector, not separately
to signed summands of a physical norm. Both rectangles retain all slots.
-/
import Candidate.SilPrior.FourthPower.MixedActualColumns

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedCenteredZero
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelRowProfiles KernelAssignmentReindex KernelMarkedRows KernelRowExpansion
open KernelLabelledSlots KernelPunctureRows
open ReferenceConvolution SexticSieve
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def difference (S T : Finset (ι → Id)) (β γ : (ι → Id) → ℂ) (v : ι → Id) : ℂ :=
  (if v ∈ S then β v else 0)-(if v ∈ T then γ v else 0)

theorem padded_sum (S U : Finset (ι → Id)) (hSU : S ⊆ U)
    (β : (ι → Id) → ℂ) (χ : Id → ℂ) :
    (∑ v ∈ U, (if v ∈ S then β v else 0)*χ (product v)) =
      ∑ v ∈ S, β v*χ (product v) := by
  calc
    _ = ∑ v ∈ S, (if v ∈ S then β v else 0)*χ (product v) :=
      (Finset.sum_subset hSU (fun v _ hn => by rw [ite_eq_right hn,zero_mul])).symm
    _ = _ := Finset.sum_congr rfl (fun v hv => by rw [ite_eq_left hv])

theorem difference_row (S T : Finset (ι → Id)) (β γ : (ι → Id) → ℂ) (χ : Id → ℂ) :
    (∑ v ∈ S ∪ T, difference S T β γ v*χ (product v)) =
      (∑ v ∈ S, β v*χ (product v))-(∑ v ∈ T, γ v*χ (product v)) := by
  simp only [difference,sub_mul,Finset.sum_sub_distrib]
  rw [padded_sum S (S∪T) Finset.subset_union_left,
    padded_sum T (S∪T) Finset.subset_union_right]

theorem difference_bound (S T : Finset (ι → Id)) (β γ : (ι → Id) → ℂ)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hβ : ∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ))
    (hγ : ∀ v ∈ T, ‖γ v‖ ≤ C/Real.sqrt (Ideal.absNorm (product v) : ℝ)) (v : ι → Id) :
    ‖difference S T β γ v‖ ≤ (B+C)/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
  have hb : ‖(if v ∈ S then β v else 0)‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
    by_cases hv : v ∈ S
    · simpa only [hv,ite_true] using hβ v hv
    · simp only [hv,ite_false,norm_zero]
      exact div_nonneg hB (Real.sqrt_nonneg _)
  have hc : ‖(if v ∈ T then γ v else 0)‖ ≤ C/Real.sqrt (Ideal.absNorm (product v) : ℝ) := by
    by_cases hv : v ∈ T
    · simpa only [hv,ite_true] using hγ v hv
    · simp only [hv,ite_false,norm_zero]
      exact div_nonneg hC (Real.sqrt_nonneg _)
  exact (norm_sub_le _ _).trans ((add_le_add hb hc).trans_eq (add_div _ _ _).symm)

theorem difference_divisor (S T : Finset (ι → Id)) (β γ : (ι → Id) → ℂ) (seed : Id)
    (hβ : ∀ v ∈ S, β v ≠ 0 → seed ∣ product v)
    (hγ : ∀ v ∈ T, γ v ≠ 0 → seed ∣ product v)
    (v : ι → Id) (hv : difference S T β γ v ≠ 0) : seed ∣ product v := by
  by_contra hn
  have hb : (if v ∈ S then β v else 0)=0 := by
    split_ifs with hs
    · by_contra hb
      exact hn (hβ v hs hb)
    · rfl
  have hc : (if v ∈ T then γ v else 0)=0 := by
    split_ifs with ht
    · by_contra hc
      exact hn (hγ v ht hc)
    · rfl
  exact hv (by rw [difference,hb,hc,sub_self])

theorem centered_first_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (ι → Id)) (β γ : (ι → Id) → ℂ) (N B K : ℝ),
      1 ≤ N → 0 ≤ B → 0 ≤ K →
      (∀ v ∈ S∪T, Supported (product v) ∧ (Ideal.absNorm (product v) : ℝ) ≤ N) →
      (∀ v ∈ S∪T, PowerFree 5 (product v)) →
      (∀ v ∈ S, ‖β v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      (∀ v ∈ T, ‖γ v‖ ≤ B/Real.sqrt (Ideal.absNorm (product v) : ℝ)) →
      ∀ (μ : Id → ℂ), (∀ I ∈ columns (S∪T), ‖μ I‖ ≤ 1) →
      ∀ hs : ∀ I ∈ columns (S∪T), Supported I,
      ‖CenteredMomentZeroMode.idealZeroEnergy (columns (S∪T)) hs
        (fun I => coefficient (S∪T) (difference S T β γ) I*μ I) K‖ ≤ C*K*N^ε*B^2 := by
  obtain ⟨C,hC,hb⟩ := MixedDiagonal.grouped_mass (ι := ι) ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro S T β γ N B K hN hB hK hgeom hf hβ hγ μ hμ hs
  have hfree (I : Id) (hI : I ∈ columns (S∪T)) : PowerFree 5 I := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
    exact hf v hv
  have hmass := hb (S∪T) (difference S T β γ) N (B+B) hN (add_nonneg hB hB) hgeom
    (fun v _ => difference_bound S T β γ B B hB hB hβ hγ v)
  have hmask : coefficientMass (columns (S∪T))
      (fun I => coefficient (S∪T) (difference S T β γ) I*μ I) ≤
      coefficientMass (columns (S∪T)) (coefficient (S∪T) (difference S T β γ)) := by
    apply Finset.sum_le_sum
    intro I hI
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hμ I hI)
  calc
    _ ≤ K*coefficientMass (columns (S∪T))
        (fun I => coefficient (S∪T) (difference S T β γ) I*μ I) :=
      MixedFirstZero.zero_energy_mass _ hs hfree _ K hK
    _ ≤ K*(C*N^ε*(B+B)^2) := mul_le_mul_of_nonneg_left (hmask.trans hmass) hK
    _ = _ := by ring

theorem actual_centered_identity (χ : Character) (S H : Finset PrimeIdeal)
    (pool : ι → Finset Id) (D E : Finset IdealPair) (β : ι → Id → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0 ≤ X₁) (hY₁ : 0 ≤ Y₁) :
    let A := MixedActualColumns.tuples S H pool D
    let B := MixedActualColumns.tuples S H pool E
    let a := MixedActualColumns.vector β P W₁ W₂ X₁ X₂
    let b := MixedActualColumns.vector β P W₁ W₂ Y₁ Y₂
    (∑ I ∈ columns (A∪B), coefficient (A∪B) (difference A B a b) I*idealCoeff χ I) =
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => normalizedRow χ D (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂) -
      weightedSum (naturalCoefficients χ S pool β P)
        (fun slot => normalizedRow χ E (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ Y₁ Y₂) := by
  dsimp only
  rw [← row_identity,difference_row,
    MixedActualColumns.actual_row_identity χ S H pool D β P W₁ W₂ X₁ X₂ hX₁,
    MixedActualColumns.actual_row_identity χ S H pool E β P W₁ W₂ Y₁ Y₂ hY₁]

/-- The first diagonal of the literal centered marked row. All coefficient
envelopes are proved from the original profile and annular slot bounds. -/
theorem actual_centered_first_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset PrimeIdeal) (pool : ι → Finset Id)
      (D E : Finset IdealPair) (β : ι → Id → ℂ) (P M : ι → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ b B₁ B₂ : ℝ),
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=Y₁*Y₂ →
      0 ≤ b → 0 ≤ B₁ → 0 ≤ B₂ → (∀ i, 0 < P i) → (∀ i, 0 ≤ M i) →
      (∀ n ∈ D, Supported n.1 ∧ Supported n.2 ∧
        (Ideal.absNorm n.1 : ℝ) ≤ b*X₁ ∧ (Ideal.absNorm n.2 : ℝ) ≤ b*X₂) →
      (∀ n ∈ E, Supported n.1 ∧ Supported n.2 ∧
        (Ideal.absNorm n.1 : ℝ) ≤ b*Y₁ ∧ (Ideal.absNorm n.2 : ℝ) ≤ b*Y₂) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ M i) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      let A := MixedActualColumns.tuples S H pool D
      let B := MixedActualColumns.tuples S H pool E
      let a := MixedActualColumns.vector β P W₁ W₂ X₁ X₂
      let b' := MixedActualColumns.vector β P W₁ W₂ Y₁ Y₂
      ∀ (K : ℝ), 0 ≤ K → ∀ (μ : Id → ℂ), (∀ I ∈ columns (A∪B), ‖μ I‖ ≤ 1) →
      ∀ hs : ∀ I ∈ columns (A∪B), Supported I,
      ‖CenteredMomentZeroMode.idealZeroEnergy (columns (A∪B)) hs
        (fun I => coefficient (A∪B) (difference A B a b') I*μ I) K‖ ≤
        C*K*(max 1 (MixedActualColumns.lengthCap b X₁ X₂ P))^ε*
          (MixedActualColumns.amplitude b B₁ B₂ M)^2 := by
  obtain ⟨C,hC,hbnd⟩ := centered_first_zero (ι := Option (Option ι)) ε hε
  refine ⟨C,hC,?_⟩
  intro S H pool D E β P M W₁ W₂ X₁ X₂ Y₁ Y₂ b B₁ B₂
    hX₁ hX₂ hY₁ hY₂ hprod hb hB₁ hB₂ hP hM hD hE hp hβ hW₁ hW₂
  dsimp only
  intro K hK μ hμ hs
  have hd := MixedActualColumns.actual_bounds S H pool D β P M W₁ W₂ X₁ X₂ b B₁ B₂
    hX₁ hX₂ hb hB₁ hB₂ hD hP hM hp hβ hW₁ hW₂
  have he := MixedActualColumns.actual_bounds S H pool E β P M W₁ W₂ Y₁ Y₂ b B₁ B₂
    hY₁ hY₂ hb hB₁ hB₂ hE hP hM hp hβ hW₁ hW₂
  have hlen : MixedActualColumns.lengthCap b Y₁ Y₂ P=MixedActualColumns.lengthCap b X₁ X₂ P := by
    unfold MixedActualColumns.lengthCap
    calc
      _ = b^2*(Y₁*Y₂)*(∏ i, 2*P i) := by ring
      _ = b^2*(X₁*X₂)*(∏ i, 2*P i) := by rw [hprod]
      _ = _ := by ring
  have hamp : 0 ≤ MixedActualColumns.amplitude b B₁ B₂ M := by
    unfold MixedActualColumns.amplitude
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB₁) (mul_nonneg (Real.sqrt_nonneg _) hB₂))
      (Finset.prod_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (hM i)))
  apply hbnd _ _ _ _ _ _ K (le_max_left _ _) hamp hK
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ⟨(hd v hv).1, (hd v hv).2.1.trans (le_max_right _ _)⟩
    · exact ⟨(he v hv).1, (hlen ▸ (he v hv).2.1).trans (le_max_right _ _)⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact MixedActualColumns.tuples_fifth_free S H pool D
        (fun n hn => ⟨(hD n hn).1.1,(hD n hn).2.1.1⟩) v hv
    · exact MixedActualColumns.tuples_fifth_free S H pool E
        (fun n hn => ⟨(hE n hn).1.1,(hE n hn).2.1.1⟩) v hv
  · exact fun v hv => (hd v hv).2.2
  · exact fun v hv => (he v hv).2.2
  · exact hμ

end
end Candidate.SilPrior.FourthPower.MixedCenteredZero
