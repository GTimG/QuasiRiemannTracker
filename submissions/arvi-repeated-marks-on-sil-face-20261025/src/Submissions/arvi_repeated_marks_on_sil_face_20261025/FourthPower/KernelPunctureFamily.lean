/- Copyright (c) 2026 Sil. Apache-2.0.
The whole marked family is reindexed before taking the physical norm.
The explicit residual-energy input retains the reflected divisor ratio.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelPunctureRows
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelMarkedRows
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelReflectedEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.KernelPunctureFamily
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAllocationIdentity KernelAssignmentReindex KernelLabelledSlots KernelRowExpansion
open KernelRowProfiles KernelRowPools KernelSelectedMass KernelPunctureMass KernelPunctureRows
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def frozenPrimes (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) : Finset PrimeIdeal :=
  T.image (fun i => (slot i).val)

/-- Freezing an actual marked occurrence creates a common ordinary puncture.
This differs from extracting a marked kernel, whose ordinary residual is T. -/
theorem actual_frozen_restriction (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) :
    augmented S (frozenPrimes S slot T) (marked S (fun i : {i // i ∉ T} => slot i.val)) =
      marked S slot := by
  funext Q
  apply Bool.eq_iff_iff.mpr
  simp only [augmented,Bool.or_eq_true,decide_eq_true_eq,marked_true,frozenPrimes,
    Finset.mem_image,Subtype.exists,exists_prop]
  constructor
  · rintro (⟨i,hi,he⟩ | ⟨i,hi,he⟩)
    · exact ⟨i,he⟩
    · exact ⟨i,Subtype.val_injective he⟩
  · rintro ⟨i,he⟩
    by_cases hi : i ∈ T
    · exact Or.inr ⟨i,hi,congrArg Subtype.val he⟩
    · exact Or.inl ⟨i,hi,he⟩

theorem actual_frozen_disjoint (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (T : Finset α) (Q : S)
    (hQ : Q.val ∈ frozenPrimes S slot T) :
    marked S (fun i : {i // i ∉ T} => slot i.val) Q=false := by
  apply Bool.eq_false_iff.mpr
  intro hm
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hQ
  obtain ⟨j,hj⟩ := (marked_true S (fun i : {i // i ∉ T} => slot i.val) Q).mp hm
  have hij : i=j.val := hinj ((Subtype.val_injective he).trans hj.symm)
  exact j.property (hij ▸ hi)

theorem family_expansion (S H : Finset PrimeIdeal) (a : α → S → ℂ)
    (ha : ∀ i Q, Q.val ∈ H → a i Q=0)
    (χ : Character) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    weightedSum a (fun slot => normalizedRow χ (supportedRectangle S b X₁ X₂)
      (restrictedValue S (augmented S H (marked S slot))) W₁ W₂ X₁ X₂) =
      ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
        extractedScalar χ (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*
          weightedSum a (fun slot => normalizedRow χ
            (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
            (restrictedValue S (marked S slot)) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) := by
  calc
    _ = weightedSum a (fun slot => ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
        extractedScalar χ (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*
          normalizedRow χ (supportedRectangle S b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2))
            (restrictedValue S (marked S slot)) W₁ W₂ (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)) := by
      unfold weightedSum
      apply Finset.sum_congr rfl
      intro slot _
      by_cases hi : Function.Injective slot
      · rw [ite_eq_left hi,ite_eq_left hi]
        dsimp only
        by_cases hh : ∀ i, (slot i).val ∉ H
        · have hdisjoint (Q : S) (hQ : Q.val ∈ H) : marked S slot Q=false := by
            apply Bool.eq_false_iff.mpr
            intro hm
            obtain ⟨i,he⟩ := (marked_true S slot Q).mp hm
            exact hh i (he.symm ▸ hQ)
          rw [full_rectangle S H (marked S slot) hdisjoint χ W₁ W₂ b X₁ X₂ hX₁ hX₂]
        · obtain ⟨i,hiH⟩ := not_forall.mp hh
          have hz : (∏ j, a j (slot j))=0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (ha i (slot i) (not_not.mp hiH))
          rw [hz,mul_zero,mul_zero]
      · rw [ite_eq_right hi,ite_eq_right hi]
    _ = _ := by
      rw [weightedSum_sum]
      apply Finset.sum_congr rfl
      intro d hd
      unfold weightedSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro slot _
      by_cases hi : Function.Injective slot <;> simp only [hi,ite_true,ite_false,mul_zero,mul_assoc]

omit [Fintype α] in
theorem energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ F : Id,
      F ≠ 0 → (Ideal.absNorm F : ℝ) ≤ Z^B →
      ∀ (S H : Finset PrimeIdeal), (∀ P ∈ S, Supported P.val) →
      (∀ P ∈ H, P.val ∣ F) → ∀ D : Finset IdealPair,
      (∀ d ∈ D, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ d ∈ D, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (G : IdealPair → Row → ℂ) (E : ℝ), 0 ≤ E → (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ d ∈ D, (∑ u ∈ rows, ρ u*‖G d u‖^2) ≤
        E*(3+((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/3 : ℝ))) →
      (∑ u ∈ rows, ρ u*‖∑ d ∈ D,
        extractedScalar (χ u) (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*
          G d u‖^2) ≤ C*Z^ε*E := by
  obtain ⟨M,hM,hm⟩ := fixed_support_reflected_mass B (ε/2) hB (half_pos hε)
  refine ⟨(2*M)^2,by positivity,?_⟩
  intro Z hZ F hF hcut S H hS hH D hd hs Row rows ρ χ G E hE hρ hG
  let q (d : IdealPair) := ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/6 : ℝ)
  let w (d : IdealPair) := idealWeight S (fun P => atPrime H P.val) (1/2) (1/2) d
  have hq (d : IdealPair) : 0 ≤ q d := by dsimp [q]; positivity
  have hw (d : IdealPair) : 0 ≤ w d := idealWeight_nonneg _ _ _ _ _
  have hq2 (d : IdealPair) : (q d)^2 =
      ((Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))^(1/3 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity :
      0 ≤ (Ideal.absNorm d.2 : ℝ)/(Ideal.absNorm d.1 : ℝ))]
    congr 1
    norm_num
  have he := KernelReflectedEnergy.variable_physical_energy (T:=D) rows ρ
    (fun d u => extractedScalar (χ u)
      (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d.val*G d.val u)
    (fun d u => G d.val u) (fun d => w d.val) (fun d => 2*(1+q d.val)) E hρ
    (fun d => hw d.val) (fun d => by have := hq d.val; positivity) (by
      intro d u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (actual_scalar_bound S H (χ u) d.val (hd d.val d.property)) (norm_nonneg _)) (by
      intro d
      apply (hG d.val d.property).trans
      rw [← hq2]
      simpa only [mul_comm E] using mul_le_mul_of_nonneg_left
        (KernelReflectedEnergy.reflected_cost (q d.val) (hq d.val)) hE)
  have hj (u : Row) : (∑ d : D, extractedScalar (χ u)
      (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d.val*G d.val u) =
      ∑ d ∈ D, extractedScalar (χ u)
        (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*G d u :=
    Finset.sum_coe_sort D (fun d => extractedScalar (χ u)
      (fun e => (kernelOn S (fun P => atPrime H P.val) e.1 e.2 : ℂ)) d*G d u)
  have hsum : (∑ d : D, w d.val*(2*(1+q d.val))) = 2*∑ d ∈ D, w d*(1+q d) := by
    rw [Finset.sum_coe_sort D (fun d => w d*(2*(1+q d))),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp_rw [hj,hsum] at he
  have hmass := hm Z hZ F hF hcut S H hS hH D hd hs
  have hsq : (2*∑ d ∈ D, w d*(1+q d))^2 ≤ (2*M)^2*Z^ε := by
    calc
      _ ≤ (2*(M*Z^(ε/2)))^2 := pow_le_pow_left₀
        (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun d _ =>
          mul_nonneg (hw d) (by have := hq d; positivity))))
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) 2
      _ = _ := by
        rw [← mul_assoc,mul_pow]
        congr 1
        rw [← Real.rpow_natCast (Z^(ε/2)) 2,← Real.rpow_mul (zero_le_one.trans hZ)]
        congr 1
        norm_num
  exact he.trans (mul_le_mul_of_nonneg_right hsq hE)

end
end Candidate.FourthPower.KernelPunctureFamily
