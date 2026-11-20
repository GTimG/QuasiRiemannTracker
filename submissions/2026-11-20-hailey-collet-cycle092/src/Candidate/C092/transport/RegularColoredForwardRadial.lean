/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual compact positive radial versions of the independent-color forward
reduction and common-puncture extraction. No lattice multiplicity is lost. -/
import Candidate.C092.transport.RegularColoredForwardDeletion
import Candidate.C092.transport.RegularColoredForwardPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentCommonMaskExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open Candidate.FourthPower
open QRH.SilDensitySplit.CubeFree.FP
open KernelRowPools KernelRowProfiles KernelMarkedRows KernelAssignmentReindex ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

def radialWeight (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (z : O) : ℝ :=
  if keep z then (Φ (‖eisEmbedding z‖^2/K)).re else 0

private theorem radialWeight_nonneg (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (z : O) :
    0 ≤ radialWeight keep Φ K z := by unfold radialWeight; split_ifs; exact hΦ z; exact le_rfl

private theorem finite_radial_le (f : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ))
    (K radial : ℝ) (hK : 0 < K) (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z ∈ rows, radialWeight keep Φ K z * ‖f z‖^2) ≤ radialEnergy f keep Φ K := by
  have h := (compact_radial_summable f keep Φ K radial hK hs).sum_le_tsum rows
    (fun z _ => by split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
  apply (le_of_eq ?_).trans h
  apply Finset.sum_congr rfl
  intro z hz
  unfold radialWeight
  split_ifs <;> ring

private theorem radial_of_finite (f : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K E : ℝ)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re)
    (hfinite : ∀ rows : Finset O, (∑ z ∈ rows, radialWeight keep Φ K z * ‖f z‖^2) ≤ E) :
    radialEnergy f keep Φ K ≤ E := by
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z => by
    split_ifs; exact mul_nonneg (sq_nonneg _) (hΦ z); exact le_rfl)
  intro rows
  apply (le_of_eq ?_).trans (hfinite rows)
  apply Finset.sum_congr rfl
  intro z hz
  unfold radialWeight
  split_ifs <;> ring

/-- Actual positive radial forward estimate with two distinct ordinary
characters, exact shortened scales and the complete remaining live factor. -/
theorem radial_forward_polynomial_energy (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Q.val.absNorm : ℝ) ≤ X) →
      ∀ (χ : O → Character) (ω₁ ω₂ : Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (I.absNorm : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ t₁ t₂ E : ℝ),
      0 ≤ b → 0 < X₁ → 0 < X₂ → 0 ≤ E →
      Function.support W₁ ⊆ Set.Iic b → Function.support W₂ ⊆ Set.Iic b →
      ∀ (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ), 0 < K →
      Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial →
      (∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) →
      (∀ z, keep z → ∀ I, ¬Supported I → idealCoeff (χ z) I = 0) →
      (∀ I, Supported I →
        ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) → primeSupport I ⊆ primeValues S) →
      (∀ (T : Finset α) (frozen : T → S), Function.Injective frozen →
        ∀ d ∈ divisorPool (supportedRectangle S b X₁ X₂),
          radialEnergy (fun z =>
            HeckeDyadic.polynomial ((χ z).product ω₁) false W₁ (X₁/(d.1.absNorm : ℝ)) 0 (2*Real.pi*t₁) *
            HeckeDyadic.polynomial ((χ z).product ω₂) false W₂ (X₂/(d.2.absNorm : ℝ)) 0 (2*Real.pi*t₂) *
            remainingSum T (naturalCoefficients (χ z) S pool β P) frozen (fun _ => 1)) keep Φ K ≤ E) →
      radialEnergy (fun z => weightedSum (naturalCoefficients (χ z) S pool β P)
        (fun slot => row (χ z) (idealCoeff ω₁) (idealCoeff ω₂) (supportedRectangle S b X₁ X₂)
          (sourceValue false S slot) (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) X₁ X₂)) keep Φ K ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := finite_forward_polynomial_energy (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS χ ω₁ ω₂ pool β P hP hp hβ W₁ W₂ b X₁ X₂ t₁ t₂ E hb hX₁ hX₂ hE hW₁ hW₂
    keep Φ K radial hK hs hΦ hχ henclose hchildren
  apply radial_of_finite _ keep Φ K _ hΦ
  intro rows
  let rows' := rows.filter keep
  have h := hbound X hX S hS rows' (radialWeight keep Φ K) χ ω₁ ω₂ pool β P hP hp hβ
    W₁ W₂ b X₁ X₂ t₁ t₂ E hb hX₁ hX₂ hE hW₁ hW₂
    (fun z _ => radialWeight_nonneg keep Φ K hΦ z)
    (fun z hz => hχ z (Finset.mem_filter.mp hz).2) henclose
    (fun T frozen hf d hd => (finite_radial_le _ keep Φ K radial hK hs hΦ rows').trans
      (hchildren T frozen hf d hd))
  apply (le_of_eq ?_).trans h
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : keep z <;> simp only [radialWeight,hk,ite_true,ite_false,zero_mul]

/-- The original harmonic common-divisor extraction for two independent
ordinary characters, in the exact native compact radial norm. -/
theorem radial_pair_shared_energy [DecidableEq α] (F : Finset α) (b M : α → ℝ)
    (hM : ∀ j ∈ F, 0 ≤ M j) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Finset Id) (hR : ∀ I ∈ R, Prime I)
      (χ₁ χ₂ χ : O → Character) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
      (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      0 < X₁ → 0 < X₂ →
      (∀ j ∈ F, ∀ I ∈ pool j, Prime I) → (∀ j ∈ F, 0 < P j) →
      (∀ j ∈ F, ∀ I ∈ pool j, ‖β j I‖ ≤ M j) →
      (∀ j ∈ F, ∀ I ∈ pool j, β j I ≠ 0 → (I.absNorm : ℝ) ≤ b j * P j) →
      ∀ (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial E : ℝ), 0 < K →
      Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial →
      (∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) → 0 ≤ E →
      (∀ D₁ ∈ R.powerset, ∀ D₂ ∈ R.powerset, ∀ J ∈ F.powerset,
        radialEnergy (fun z => HeckeDyadic.polynomial (χ₁ z) false W₁
            (X₁/(Ideal.absNorm (∏ I ∈ D₁, I) : ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ₂ z) false W₂ (X₂/(Ideal.absNorm (∏ I ∈ D₂, I) : ℝ)) 0 0 *
          ∏ j ∈ F \ J, naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K ≤ E) →
      radialEnergy (fun z => HeckeDyadic.polynomial ((χ₁ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        HeckeDyadic.polynomial ((χ₂ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏ j ∈ F, naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K ≤
        C*(Ideal.absNorm (∏ I ∈ R, I) : ℝ)^ε*E := by
  obtain ⟨C,hC,hbound⟩ := finite_pair_shared_energy F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ₁ χ₂ χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs keep Φ K radial E hK hsΦ hΦ hE hchild
  apply radial_of_finite _ keep Φ K _ hΦ
  intro rows
  exact hbound rows (radialWeight keep Φ K) (fun z _ => radialWeight_nonneg keep Φ K hΦ z)
    R hR χ₁ χ₂ χ (fun _ => W₁) (fun _ => W₂) (fun _ => X₁) (fun _ => X₂)
    (fun _ => pool) (fun _ => β) (fun _ => P) (fun _ => hX₁) (fun _ => hX₂)
    (fun _ => hp) (fun _ => hP) (fun _ => hβ) (fun _ => hs) E hE
    (fun D₁ hD₁ D₂ hD₂ J hJ => (finite_radial_le _ keep Φ K radial hK hsΦ hΦ rows).trans
      (hchild D₁ hD₁ D₂ hD₂ J hJ))

#print axioms radial_forward_polynomial_energy
#print axioms radial_pair_shared_energy
end
end QRH.Cycle092.RegularColoredForward
