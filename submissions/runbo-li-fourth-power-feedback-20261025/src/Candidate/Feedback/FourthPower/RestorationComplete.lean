/- Copyright (c) 2026 Sil. Apache-2.0.
Complete central-energy restoration to the original product of natural
prime slots. All transfer inputs are literal restricted-family statements.
The mixed moment supplying that input is a separate analytic obligation.
-/
import Candidate.Feedback.FourthPower.RestorationInverseEnergy
import Candidate.Feedback.FourthPower.RestorationCollisionEnergy
import Candidate.Feedback.FourthPower.ReferencePrimeEnclosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 600000
namespace Candidate.Feedback.FourthPower.RestorationComplete
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelCollisionEnergy RestorationFamily
open KernelRowProfiles KernelRowPools ReferencePrimeEnclosure
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

omit [Fintype α] in
/-- Finite enumeration instances do not change the actual row. This equality
avoids reducing large decision procedures while composing subtype families. -/
theorem row_fintype_irrel (h₁ h₂ : Fintype α) (inv : Bool) (S : Finset PrimeIdeal)
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    @row α h₁ inv S χ pool β P W₁ W₂ b X₁ X₂ =
      @row α h₂ inv S χ pool β P W₁ W₂ b X₁ X₂ := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  cases h
  rfl

/-- From the actual downward-closed restricted estimate to the full original
natural product, uniformly in the characters, positive physical weights,
ordinary profiles, marked pools and the original coefficients with only
the finite exclusions produced by the two exact decompositions. No endpoint or source
estimate is assumed implicitly: the sole analytic input is displayed. -/
theorem full_energy_exact (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (r : Setoid α) (tc : {q // ¬singletonBlock r q} → S)
        (T : Finset {q // singletonBlock r q}) (ti : T → S), Function.Injective ti →
        ∀ Y₁ Y₂ : ℝ, 0 < Y₁ → Y₁ ≤ X₁ → 0 < Y₂ → Y₂ ≤ X₂ →
        (∑ u ∈ rows, ρ u*‖row false S (χ u)
          (fun q : {q : {q // singletonBlock r q} // q ∉ T} =>
            pool (singletonRepresentative r q.val))
          (crossBeta T S ti (RestorationCollisionEnergy.collisionBeta r S tc β))
          (fun q => P (singletonRepresentative r q.val)) W₁ W₂ b Y₁ Y₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ C*X^ε*E := by
  obtain ⟨Cc,hCc,hcollision⟩ := RestorationCollisionEnergy.collision_energy_exact
    (α:=α) B (ε/2) hB (half_pos hε)
  choose Ci hCi hinverse using fun r : Setoid α =>
    RestorationInverseEnergy.inverse_energy_exact (α:={q // singletonBlock r q})
      B (ε/2) (zero_le_one.trans hB) (half_pos hε)
  let M := 1+∑ r : Setoid α, Ci r
  have hM : 0 < M := by
    have hh := Finset.sum_nonneg (fun r (_ : r ∈ (Finset.univ : Finset (Setoid α))) => (hCi r).le)
    dsimp [M]; linarith
  have hiM (r : Setoid α) : Ci r ≤ M := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=Ci) (fun r _ => (hCi r).le) (Finset.mem_univ r)
    dsimp [M]; linarith
  refine ⟨Cc*M,mul_pos hCc hM,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ hroot
  have hinj (r : Setoid α) (tc : {q // ¬singletonBlock r q} → S) :
      (∑ u ∈ rows, ρ u*‖row true S (χ u)
        (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q))
        (RestorationCollisionEnergy.collisionBeta r S tc β)
        (fun q => P (singletonRepresentative r q)) W₁ W₂ b X₁ X₂‖^2) ≤ M*X^(ε/2)*E := by
    let β' := RestorationCollisionEnergy.collisionBeta r S tc β
    have hβ' : ∀ q I, I ∈ pool (singletonRepresentative r q) → ‖β' q I‖ ≤ B :=
      maskedBeta_bound _ _ _ B (zero_le_one.trans hB) (fun q=>hβ (singletonRepresentative r q))
    have hh := hinverse r X hX S hS rows ρ χ
      (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q)) β'
      (fun q => P (singletonRepresentative r q))
      (fun q => hP (singletonRepresentative r q))
      (fun q => hp (singletonRepresentative r q)) hβ'
      W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ (by
        intro T ti hti Y₁ Y₂ hY₁ hY₁le hY₂ hY₂le
        apply (le_of_eq ?_).trans (hroot r tc T ti hti Y₁ Y₂ hY₁ hY₁le hY₂ hY₂le)
        apply Finset.sum_congr rfl
        intro u _
        apply congrArg (fun z : ℂ => ρ u*‖z‖^2)
        apply row_fintype_irrel)
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hiM r) (Real.rpow_nonneg (zero_le_one.trans hX) _)) hE)
  have hh := hcollision X hX S hS rows ρ χ pool β P hpool hP hp hβ
    W₁ W₂ b X₁ X₂ (M*X^(ε/2)*E) (by positivity) hρ (by
      intro r tc
      apply (le_of_eq ?_).trans (hinj r tc)
      apply Finset.sum_congr rfl
      intro u _
      apply congrArg (fun z : ℂ => ρ u*‖z‖^2)
      apply row_fintype_irrel)
  apply hh.trans_eq
  calc
    _ = (Cc*M)*(X^(ε/2)*X^(ε/2))*E := by ring
    _ = _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hX),show ε/2+ε/2=ε by ring]

/-- Compatibility corollary with a stronger input. -/
theorem full_energy (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (r : Setoid α) (T : Finset {q // singletonBlock r q})
        (β' : {q : {q // singletonBlock r q} // q ∉ T} → Id → ℂ),
        (∀ q I, I ∈ pool (singletonRepresentative r q.val) → ‖β' q I‖ ≤ B) →
        ∀ Y₁ Y₂ : ℝ, 0 < Y₁ → Y₁ ≤ X₁ → 0 < Y₂ → Y₂ ≤ X₂ →
        (∑ u ∈ rows, ρ u*‖row false S (χ u)
          (fun q : {q : {q // singletonBlock r q} // q ∉ T} =>
            pool (singletonRepresentative r q.val))
          β' (fun q => P (singletonRepresentative r q.val)) W₁ W₂ b Y₁ Y₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := full_energy_exact (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ hroot
  apply hbound X hX S hS rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hX₁ hX₂ hE hρ
  intro r tc T ti _ Y₁ Y₂ hY₁ hc₁ hY₂ hc₂
  exact hroot r T (crossBeta T S ti (RestorationCollisionEnergy.collisionBeta r S tc β))
    (crossBeta_bound T S ti _ _ B (zero_le_one.trans hB)
      (maskedBeta_bound _ _ _ B (zero_le_one.trans hB) (fun q=>hβ (singletonRepresentative r q))))
    Y₁ Y₂ hY₁ hc₁ hY₂ hc₂

/-- The restored family is the original Hecke product, at the two original
frequencies, with the original annular normalization of every marked slot. -/
theorem full_natural_product (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ t₁ t₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b) (hW₂ : Function.support W₂ ⊆ Set.Iic b)
    (hχ : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (henclose : ∀ I, Supported I →
      ((Ideal.absNorm I : ℝ) ≤ b*X₁ ∨ (Ideal.absNorm I : ℝ) ≤ b*X₂) →
      primeSupport I ⊆ primeValues S) :
    fullRow S χ pool β P (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ =
      (HeckeDyadic.polynomial χ false W₁ X₁ 0 (2*Real.pi*t₁)*
        HeckeDyadic.polynomial χ false W₂ X₂ 0 (2*Real.pi*t₂))*
      ∏ i, CenteredMomentCommonMaskExpansion.naturalSlot χ (pool i) (β i) (P i) := by
  unfold fullRow
  rw [enclosed_phase_pair χ S W₁ W₂ b X₁ X₂ t₁ t₂ hX₁ hX₂ hW₁ hW₂ hχ henclose]

/-- Uniform finite physical bounds also prove convergence of the full
positive physical energy, not just an inequality for a conventionally zero
value of a divergent series. -/
theorem full_series {Row : Type*} (ρ : Row → ℝ) (χ : Row → Character)
    (S : Finset PrimeIdeal) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ) (hρ : ∀ u, 0 ≤ ρ u)
    (hfinite : ∀ rows : Finset Row,
      (∑ u ∈ rows, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ E) :
    Summable (fun u => ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ∧
      (∑' u, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ E := by
  have hn (u : Row) : 0 ≤ ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2 :=
    mul_nonneg (hρ u) (sq_nonneg _)
  exact ⟨summable_of_sum_le hn hfinite,Real.tsum_le_of_sum_le hn hfinite⟩

end
end Candidate.Feedback.FourthPower.RestorationComplete
