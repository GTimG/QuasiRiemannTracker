/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine separated common pair costs one fixed polynomial Fourier weight. -/
import Candidate.C092.transport.TerminalProfileUniformPair
import Submissions.sil_density_split_20261026.CubeFree.Packet.ProfileSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
open QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation
local notation "O" => HeckeFamily.O

theorem common_pair_payment (S : Finset (ℕ×ℕ)) {C : ℝ} (hC : 0 < C) :
    ∃ J : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ e : Fin 2×Fin 2, ∀ τ : ℝ×ℝ,
      C^4*((commonPair e τ).control S)^2 ≤ K*pairWeight J τ := by
  obtain ⟨n,D,hD,hd⟩ := commonPair_control_sq S
  refine ⟨2*n,C^4*D,by positivity,?_⟩
  intro e τ
  exact (mul_le_mul_of_nonneg_left (hd e τ) (by positivity)).trans_eq (by ring)

/-- Actual fixed unit-supplier output, with all source constants fixed before
e and Fourier τ, restores to one fixed Fourier weight. Independent ordinary
characters and height arrays, original marks and row keeps are retained. -/
theorem common_pair_energy (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S)
    {C : ℝ} (hC : 0 < C) :
    ∃ J : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ (ρ : Type) (rows : Finset ρ) (η₁ η₂ : Character)
      (m₁ A₁ m₂ A₂ z : ρ→O) (t₁ t₂ X₁ X₂ : ρ→ℝ)
      (V : ℝ→ℂ) (e : Fin 2×Fin 2) (τ : ℝ×ℝ)
      (opened : ρ→Bool) (R : ρ→ℝ) (marks : ρ→ℂ) (E : ℝ), 0 ≤ E →
      actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
        ((unitPair S C (commonPair e τ)).profile 0)
        ((unitPair S C (commonPair e τ)).profile 1) opened R marks ≤ E →
      actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
        ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) opened R marks ≤
        K*pairWeight J τ*E := by
  obtain ⟨J,K,hK,hb⟩ := common_pair_payment S hC
  refine ⟨J,K,hK,?_⟩
  intro ρ rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V e τ opened R marks E hE hunit
  exact (homogeneous_of_unit rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
    (commonPair e τ) opened R marks S hS hC E hunit).trans
    (mul_le_mul_of_nonneg_right (hb e τ) hE)

#print axioms common_pair_payment
#print axioms common_pair_energy
end
end QRH.Cycle092.TerminalProfileUniform
