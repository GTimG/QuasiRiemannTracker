/- Copyright (c) 2026 Sil. Apache-2.0.
The literal inverse restoration theorem. Its input is a downward-closed
restricted-family estimate, not an unspecified residual function. This is
a transfer theorem; it does not by itself prove the mixed moment or source.
-/
import Candidate.Feedback.FourthPower.RestorationFamily
import Candidate.Feedback.FourthPower.KernelFamilyEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RestorationInverseEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelMarkedRows KernelRowProfiles KernelRowPools
open KernelPhysicalScalars KernelFamilyEnergy RestorationFamily
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

def frozenChoices (T : Finset α) (S : Finset PrimeIdeal) : Finset (T → S) :=
  Finset.univ.filter Function.Injective

/-- No ordinary puncture is introduced at a kernel-frozen supplying prime.
It is excluded only from the remaining marked coefficients. -/
theorem inverse_expansion (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    row true S χ pool β P W₁ W₂ b X₁ X₂ =
      ∑ T : Finset α, ∑ t ∈ frozenChoices T S,
        ∑ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
          scalar χ S (ordinarySeriesFor true) (markedSeriesFor true)
            (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t d *
          row false S χ (fun i : {i // i ∉ T} => pool i.val)
            (crossBeta T S t β) (fun i => P i.val) W₁ W₂ b
            (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2) := by
  rw [row,natural_rectangle_expansion true S χ pool β P W₁ W₂ b X₁ X₂ hX₁ hX₂]
  apply Finset.sum_congr rfl
  intro T _
  rw [frozenChoices,Finset.sum_filter]
  apply Finset.sum_congr (by ext; simp)
  intro t _
  by_cases ht : Function.Injective t
  · simp only [ht,ite_true]
    apply Finset.sum_congr rfl
    intro d _
    rw [inverse_remaining_row]
  · simp only [ht,ite_false]

/-- Uniform inverse transfer in a positive physical norm. The hypothesis
names the actual restricted row, all shorter ordinary scales and bounded
common marked coefficients. Every inverse scalar and cross-hole is supplied
by the exact expansion above and the proved central kernel mass. -/
theorem inverse_energy_exact (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (T : Finset α) (t : T → S), Function.Injective t →
        ∀ Y₁ Y₂ : ℝ, 0 < Y₁ → Y₁ ≤ X₁ → 0 < Y₂ → Y₂ ≤ X₂ →
        (∑ u ∈ rows, ρ u * ‖row false S (χ u)
          (fun i : {i // i ∉ T} => pool i.val) (crossBeta T S t β) (fun i => P i.val) W₁ W₂ b Y₁ Y₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖row true S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤
        C*X^ε*E := by
  choose C hC hbound using fun T : Finset α =>
    actual_subpower_energy (α:=T) true B ε hB hε
  let M := 1+∑ T : Finset α, C T
  have hM : 0 < M := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) => (hC T).le)
    dsimp [M]; linarith
  have hCM (T : Finset α) : C T ≤ M := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=C) (fun T _ => (hC T).le) (Finset.mem_univ T)
    dsimp [M]; linarith
  refine ⟨(Fintype.card (Finset α) : ℝ)^2*M,by positivity,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ hroot
  let D := divisorPool (supportedRectangle S b X₁ X₂)
  let G (T : Finset α) (t : T → S) (d : Id × Id) (u : Row) :=
    row false S (χ u) (fun i : {i // i ∉ T} => pool i.val)
      (crossBeta T S t β) (fun i => P i.val) W₁ W₂ b
      (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)
  let F (T : Finset α) (u : Row) := ∑ t ∈ frozenChoices T S, ∑ d ∈ D,
    scalar (χ u) S (ordinarySeriesFor true) (markedSeriesFor true)
      (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val) t d * G T t d u
  have hG (T : Finset α) (t : T → S) (ht : Function.Injective t) (d : Id × Id) (hd : d ∈ D) :
      (∑ u ∈ rows, ρ u*‖G T t d u‖^2) ≤ E := by
    have hs := divisor_supported hd
    have h₁ := shortened_positive_le hX₁ hs.1
    have h₂ := shortened_positive_le hX₂ hs.2.1
    exact hroot T t ht _ _ h₁.1 h₁.2 h₂.1 h₂.2
  have hF (T : Finset α) : (∑ u ∈ rows, ρ u*‖F T u‖^2) ≤ M*X^ε*E := by
    have hh := hbound T X hX S hS (frozenChoices T S)
      (fun t ht => (Finset.mem_filter.mp ht).2) (fun _ => D)
      (fun _ _ d hd => ⟨(divisor_supported hd).1,(divisor_supported hd).2.1⟩)
      (fun _ _ d hd => (divisor_supported hd).2.2)
      rows ρ χ (fun i : T => pool i.val) (fun i : T => β i.val) (fun i : T => P i.val)
      (fun i => hP i.val) (fun i => hp i.val) (fun i => hβ i.val)
      (G T) E hE hρ (fun t ht d hd => hG T t (Finset.mem_filter.mp ht).2 d hd)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCM T) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hE)
  have hid (u : Row) : row true S (χ u) pool β P W₁ W₂ b X₁ X₂ = ∑ T : Finset α, F T u := by
    exact inverse_expansion S (χ u) pool β P W₁ W₂ b X₁ X₂ hX₁ hX₂
  simp_rw [hid]
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ F F (fun _ => 1)
    (M*X^ε*E) hρ (fun _ => zero_le_one) (by intros; simp) hF
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    mul_assoc] using hh

/-- Compatibility corollary with a stronger input. -/
theorem inverse_energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (T : Finset α) (β' : {i // i ∉ T} → Id → ℂ),
        (∀ i I, I ∈ pool i.val → ‖β' i I‖ ≤ B) →
        ∀ Y₁ Y₂ : ℝ, 0 < Y₁ → Y₁ ≤ X₁ → 0 < Y₂ → Y₂ ≤ X₂ →
        (∑ u ∈ rows, ρ u * ‖row false S (χ u)
          (fun i : {i // i ∉ T} => pool i.val) β' (fun i => P i.val) W₁ W₂ b Y₁ Y₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖row true S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤
        C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := inverse_energy_exact (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ hroot
  apply hbound X hX S hS rows ρ χ pool β P hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ
  intro T t _ Y₁ Y₂ hY₁ hc₁ hY₂ hc₂
  exact hroot T (crossBeta T S t β) (crossBeta_bound T S t β pool B hB hβ)
    Y₁ Y₂ hY₁ hc₁ hY₂ hc₂

end
end Candidate.Feedback.FourthPower.RestorationInverseEnergy
