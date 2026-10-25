/- Copyright (c) 2026 Sil. Apache-2.0.
Physical aggregation with the actual extraction ratio. The remaining child
energy is an explicit input; this module does not assert the source theorem.
-/
import Candidate.Feedback.FourthPower.KernelFamilyEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.KernelReflectedEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAllocationIdentity KernelPhysicalScalars KernelCommonScalarMass KernelFamilyEnergy
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

/-- Child norms may have different costs. Only their mass-weighted square
roots are summed, never the number of assignments. -/
theorem variable_physical_energy {Row T : Type*} [Fintype T]
    (rows : Finset Row) (ρ : Row → ℝ) (F G : T → Row → ℂ)
    (w γ : T → ℝ) (E : ℝ)
    (hρ : ∀ u ∈ rows, 0 ≤ ρ u) (hw : ∀ j, 0 ≤ w j) (hγ : ∀ j, 0 < γ j)
    (hFG : ∀ j, ∀ u ∈ rows, ‖F j u‖ ≤ w j*‖G j u‖)
    (hG : ∀ j, (∑ u ∈ rows, ρ u*‖G j u‖^2) ≤ (γ j)^2*E) :
    (∑ u ∈ rows, ρ u*‖∑ j, F j u‖^2) ≤ (∑ j, w j*γ j)^2*E := by
  apply KernelCollisionEnergy.weighted_physical_energy rows ρ F
    (fun j u => G j u/(γ j : ℂ)) (fun j => w j*γ j) E hρ
    (fun j => mul_nonneg (hw j) (hγ j).le)
  · intro j u hu
    apply (hFG j u hu).trans_eq
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hγ j)]
    field_simp [(hγ j).ne']
  · intro j
    have he : (∑ u ∈ rows, ρ u*‖G j u/(γ j : ℂ)‖^2) =
        (∑ u ∈ rows, ρ u*‖G j u‖^2)/(γ j)^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hγ j),div_pow]
      ring
    rw [he]
    exact (div_le_iff₀ (sq_pos_of_pos (hγ j))).mpr (by simpa [mul_comm] using hG j)

theorem criticalRatio_sq (S : Finset PrimeIdeal) (slot : α → S) (d : Id × Id) :
    (criticalRatio S slot d)^2 =
      ((Ideal.absNorm d.2 : ℝ)/((Ideal.absNorm d.1 : ℝ)*frozenNorm S slot))^(1/3 : ℝ) := by
  unfold criticalRatio
  have hf := frozenNorm_pos S slot
  rw [← Real.rpow_natCast _ 2,← Real.rpow_mul (by positivity :
    0 ≤ (Ideal.absNorm d.2 : ℝ)/((Ideal.absNorm d.1 : ℝ)*frozenNorm S slot))]
  congr 1
  norm_num

theorem reflected_cost (q : ℝ) (hq : 0 ≤ q) : 3+q^2 ≤ (2*(1+q))^2 := by
  nlinarith [sq_nonneg q]

theorem actual_reflected_envelope {Row : Type*} (B : ℝ) (hB : 0 ≤ B)
    (S : Finset PrimeIdeal) (F : Finset (α → S)) (D : (α → S) → Finset (Id × Id))
    (hd : ∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (hP : ∀ i, 0 < P i)
    (hp : ∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ B)
    (G : (α → S) → (Id × Id) → Row → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hρ : ∀ u ∈ rows, 0 ≤ ρ u)
    (hG : ∀ t ∈ F, ∀ d ∈ D t,
      (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤ E*(3+(criticalRatio S t d)^2)) :
    (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
      scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false) pool β P t d * G t d u‖^2) ≤
      (2*(∑ t ∈ F, ∑ d ∈ D t, weight false B S t d*(1+criticalRatio S t d)))^2*E := by
  have he := variable_physical_energy (T:=Index F D) rows ρ
    (fun j u => scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false)
      pool β P j.1.val j.2.val * G j.1.val j.2.val u)
    (fun j u => G j.1.val j.2.val u)
    (fun j => weight false B S j.1.val j.2.val)
    (fun j => 2*(1+criticalRatio S j.1.val j.2.val)) E hρ
    (fun j => weight_nonneg false B hB S j.1.val j.2.val)
    (fun j => by have := criticalRatio_nonneg S j.1.val j.2.val; positivity) (by
      intro j u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (scalar_le_weight false B hB S (χ u) pool β P hP hp hβ j.1.val j.2.val
          (hd j.1.val j.1.property j.2.val j.2.property)) (norm_nonneg _)) (by
      intro j
      apply (hG j.1.val j.1.property j.2.val j.2.property).trans
      rw [mul_comm _ E]
      exact mul_le_mul_of_nonneg_left
        (reflected_cost _ (criticalRatio_nonneg S j.1.val j.2.val)) hE)
  have hj (u : Row) : (∑ j : Index F D,
      scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false)
        pool β P j.1.val j.2.val * G j.1.val j.2.val u) =
      ∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false) pool β P t d * G t d u :=
    sum_index F D (fun t d =>
      scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false) pool β P t d * G t d u)
  have hw : (∑ j : Index F D, weight false B S j.1.val j.2.val*
      (2*(1+criticalRatio S j.1.val j.2.val))) =
      2*(∑ t ∈ F, ∑ d ∈ D t, weight false B S t d*(1+criticalRatio S t d)) := by
    calc
      _ = ∑ t ∈ F, ∑ d ∈ D t, weight false B S t d*(2*(1+criticalRatio S t d)) :=
        sum_index F D (fun t d => weight false B S t d*(2*(1+criticalRatio S t d)))
      _ = _ := ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdd
    ring
  simpa only [hj,hw] using he

/-- The actual forward family, with the exact frozen-product ratio from the
reference bound, costs only an arbitrarily small power. Child-energy bounds
remain explicit and must be supplied by the analytic reference. -/
theorem actual_reflected_subpower (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) →
      ∀ F : Finset (α → S), (∀ t ∈ F, Function.Injective t) →
      ∀ D : (α → S) → Finset (Id × Id),
      (∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0) →
      (∀ t ∈ F, ∀ d ∈ D t, pairSupport d.1 d.2 ⊆ primeValues S) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ G : (α → S) → (Id × Id) → Row → ℂ, ∀ E : ℝ, 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ t ∈ F, ∀ d ∈ D t, (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤
        E*(3+((Ideal.absNorm d.2 : ℝ)/
          ((Ideal.absNorm d.1 : ℝ)*frozenNorm S t))^(1/3 : ℝ))) →
      (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor false) (markedSeriesFor false) pool β P t d * G t d u‖^2) ≤
        C*X^ε*E := by
  obtain ⟨M,hM,hm⟩ := reflected_weight_subpower (α:=α) B (ε/2) hB (half_pos hε)
  refine ⟨(2*M)^2,sq_pos_of_pos (by positivity),?_⟩
  intro X hX S hS F hinj D hd hs Row rows ρ χ pool β P hP hp hβ G E hE hρ hG
  have hm0 : 0 ≤ ∑ t ∈ F, ∑ d ∈ D t, weight false B S t d*(1+criticalRatio S t d) :=
    Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun d _ =>
      mul_nonneg (weight_nonneg false B hB S t d) (by have := criticalRatio_nonneg S t d; positivity)))
  have hmass : (2*(∑ t ∈ F, ∑ d ∈ D t, weight false B S t d*(1+criticalRatio S t d)))^2 ≤
      (2*M)^2*X^ε := by
    calc
      _ ≤ (2*(M*X^(ε/2)))^2 := pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hm X hX S hS F hinj D hd hs) (by norm_num)) 2
      _ = _ := by
        rw [← mul_assoc,mul_pow]
        congr 1
        rw [← Real.rpow_natCast (X^(ε/2)) 2,← Real.rpow_mul (zero_le_one.trans hX)]
        congr 1
        norm_num
  exact (actual_reflected_envelope B hB S F D hd rows ρ χ pool β P hP hp hβ G E hE hρ
    (fun t ht d hdd => by simpa only [criticalRatio_sq] using hG t ht d hdd)).trans
      (mul_le_mul_of_nonneg_right hmass hE)

end
end Candidate.Feedback.FourthPower.KernelReflectedEnergy
