/- Copyright (c) 2026 Sil. Apache-2.0.
The actual restoration scalars in one positive physical norm. Residual row
energy is an explicit hypothesis: this adapter is not the final source theorem.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelCommonScalarMass
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.KernelCollisionEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelFamilyEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAllocationIdentity KernelPhysicalScalars KernelCommonScalarMass
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def Index {A : Type*} (F : Finset A) (D : A → Finset (Id × Id)) :=
  (t : F) × D t.val

instance {A : Type*} (F : Finset A) (D : A → Finset (Id × Id)) : Fintype (Index F D) :=
  inferInstanceAs (Fintype ((t : F) × D t.val))

theorem sum_index {A V : Type*} [AddCommMonoid V]
    (F : Finset A) (D : A → Finset (Id × Id)) (f : A → (Id × Id) → V) :
    (∑ j : Index F D, f j.1.val j.2.val) = ∑ t ∈ F, ∑ d ∈ D t, f t d := by
  change (∑ j : (t : F) × D t.val, f j.1.val j.2.val) = _
  rw [Fintype.sum_sigma]
  simp_rw [Finset.sum_coe_sort]
  exact Finset.sum_coe_sort F (fun t => ∑ d ∈ D t, f t d)

/-- Frozen coefficients are controlled by a row-independent envelope, so no
number of assignments is paid by the physical Cauchy-Schwarz step. -/
theorem actual_envelope_energy {Row : Type*} (inv : Bool) (B : ℝ) (hB : 0 ≤ B)
    (S : Finset PrimeIdeal) (F : Finset (α → S)) (D : (α → S) → Finset (Id × Id))
    (hd : ∀ t ∈ F, ∀ d ∈ D t, d.1 ≠ 0 ∧ d.2 ≠ 0)
    (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (hP : ∀ i, 0 < P i)
    (hp : ∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i)
    (hβ : ∀ i I, I ∈ pool i → ‖β i I‖ ≤ B)
    (G : (α → S) → (Id × Id) → Row → ℂ) (E : ℝ)
    (hρ : ∀ u ∈ rows, 0 ≤ ρ u)
    (hG : ∀ t ∈ F, ∀ d ∈ D t, (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤ E) :
    (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
      scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P t d * G t d u‖^2) ≤
      (∑ t ∈ F, ∑ d ∈ D t, weight inv B S t d)^2*E := by
  have he := KernelCollisionEnergy.weighted_physical_energy (T := Index F D) rows ρ
    (fun j u => scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv)
      pool β P j.1.val j.2.val * G j.1.val j.2.val u)
    (fun j u => G j.1.val j.2.val u)
    (fun j => weight inv B S j.1.val j.2.val) E hρ
    (fun j => weight_nonneg inv B hB S j.1.val j.2.val) (by
      intro j u _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (scalar_le_weight inv B hB S (χ u) pool β P hP hp hβ j.1.val j.2.val
          (hd j.1.val j.1.property j.2.val j.2.property)) (norm_nonneg _))
    (fun j => hG j.1.val j.1.property j.2.val j.2.property)
  have hj (u : Row) : (∑ j : Index F D,
      scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv)
        pool β P j.1.val j.2.val * G j.1.val j.2.val u) =
      ∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P t d * G t d u :=
    sum_index F D (fun t d =>
      scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P t d * G t d u)
  simp_rw [hj] at he
  simpa only [sum_index] using he

/-- Both forward and inverse extraction cost an arbitrarily small power in
the positive norm. This does not assert the remaining child-energy input. -/
theorem actual_subpower_energy (inv : Bool) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
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
      (∀ t ∈ F, ∀ d ∈ D t, (∑ u ∈ rows, ρ u*‖G t d u‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖∑ t ∈ F, ∑ d ∈ D t,
        scalar (χ u) S (ordinarySeriesFor inv) (markedSeriesFor inv) pool β P t d * G t d u‖^2) ≤
        C*X^ε*E := by
  obtain ⟨M,hM,hm⟩ := weight_subpower (α := α) inv B (ε/2) hB (half_pos hε)
  refine ⟨M^2,sq_pos_of_pos hM,?_⟩
  intro X hX S hS F hinj D hd hs Row rows ρ χ pool β P hP hp hβ G E hE hρ hG
  have hw := hm X hX S hS F hinj D hd hs
  have hmass : (∑ t ∈ F, ∑ d ∈ D t, weight inv B S t d)^2 ≤ M^2*X^ε := by
    calc
      _ ≤ (M*X^(ε/2))^2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun d _ => weight_nonneg inv B hB S t d))) hw 2
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast (X^(ε/2)) 2,← Real.rpow_mul (zero_le_one.trans hX)]
        congr 1
        norm_num
  exact (actual_envelope_energy inv B hB S F D hd rows ρ χ pool β P hP hp hβ G E hρ hG).trans
    (mul_le_mul_of_nonneg_right hmass hE)

end
end Candidate.FourthPower.KernelFamilyEnergy
