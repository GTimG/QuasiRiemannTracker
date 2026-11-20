/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Either original coordinate may be the genuine long P6 column. -/
import Candidate.C092.transport.TerminalProfileUniformTwisted
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional
open QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation
local notation "O" => HeckeFamily.O

theorem distinct_profile_controls {a b : ℝ} (p : Profiles a b) (S : Finset (ℕ×ℕ))
    (i j : Fin 2) (hij : i ≠ j) :
    sourceControl S (p.profile i)*sourceControl S (p.profile j) = p.control S := by
  fin_cases i <;> fin_cases j <;> simp_all [Profiles.control,mul_comm]

theorem native_common_pair_energy_either (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S) {C : ℝ} (hC : 0 < C) :
    ∃ J : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ (ρ : Type) (rows : Finset ρ) (η₁ η₂ : Character)
      (m₁ A₁ m₂ A₂ z : ρ→O) (tLong XLong XShort σ freq : ρ→ℝ)
      (V : ℝ→ℂ) (e : Fin 2×Fin 2) (τ : ℝ×ℝ) (iLong iShort : Fin 2), iLong ≠ iShort →
    ∀ (opened : ρ→Bool) (Dstar D : ρ→ℝ) (marks : ρ→ℂ) (E : ℝ), 0 ≤ E →
      nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
        ((unitPair S C (commonPair e τ)).profile iLong)
        ((unitPair S C (commonPair e τ)).profile iShort) opened Dstar D marks ≤ E →
      nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
        ((commonPair e τ).profile iLong) ((commonPair e τ).profile iShort) opened Dstar D marks ≤
        K*pairWeight J τ*E := by
  obtain ⟨J,K,hK,hb⟩ := common_pair_payment S hC
  refine ⟨J,K,hK,?_⟩
  intro ρ rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V e τ iLong iShort hij opened Dstar D marks E hE hunit
  rw [nativeEnergy_reconstruct rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
    ((commonPair e τ).profile iLong) ((commonPair e τ).profile iShort) opened Dstar D marks S hS hC,
    distinct_profile_controls (commonPair e τ) S iLong iShort hij]
  exact (mul_le_mul_of_nonneg_left hunit (by positivity)).trans
    (mul_le_mul_of_nonneg_right (hb e τ) hE)

#print axioms native_common_pair_energy_either
end
end QRH.Cycle092.TerminalProfileUniform
