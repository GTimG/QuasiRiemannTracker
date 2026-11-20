/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal native P6 energy: independent long height and rowwise short shifts. -/
import Candidate.C092.transport.TerminalProfileUniform
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional HeckeInverseAmplification
open QRH.Cycle092.OrdinaryColumn
open QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation
local notation "O" => HeckeFamily.O

def nativeEnergy {ρ : Type} (rows : Finset ρ) (η₁ η₂ : Character)
    (m₁ A₁ m₂ A₂ z : ρ→O) (tLong XLong XShort σ freq : ρ→ℝ)
    (V : ℝ→ℂ) (W₁ W₂ : 𝓢(ℝ,ℂ)) (opened : ρ→Bool) (Dstar D : ρ→ℝ)
    (marks : ρ→ℂ) : ℝ :=
  ∑ r ∈ rows, ‖original η₁ (m₁ r) (A₁ r) (z r) (W₁:ℝ→ℂ) (tLong r) (XLong r)*
    original η₂ (m₂ r) (A₂ r) (z r)
      (twistProfile (TerminalActualRow.shortProfile V W₂ (opened r) (Dstar r) (D r)) (σ r) (freq r))
      0 (XShort r)*marks r‖^2

theorem nativeEnergy_reconstruct {ρ : Type} (rows : Finset ρ) (η₁ η₂ : Character)
    (m₁ A₁ m₂ A₂ z : ρ→O) (tLong XLong XShort σ freq : ρ→ℝ)
    (V : ℝ→ℂ) (W₁ W₂ : 𝓢(ℝ,ℂ)) (opened : ρ→Bool) (Dstar D : ρ→ℝ) (marks : ρ→ℂ)
    (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S) {C : ℝ} (hC : 0 < C) :
    nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V W₁ W₂ opened Dstar D marks =
    C^4*(sourceControl S W₁*sourceControl S W₂)^2*
      nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
        (unitProfile S C W₁) (unitProfile S C W₂) opened Dstar D marks := by
  let c₁ := C*sourceControl S W₁
  let c₂ := C*sourceControl S W₂
  have hc₁ : 0 ≤ c₁ := mul_nonneg hC.le (sourceControl_nonneg _ _)
  have hc₂ : 0 ≤ c₂ := mul_nonneg hC.le (sourceControl_nonneg _ _)
  have hlong : (W₁:ℝ→ℂ) = fun x => (c₁:ℂ)*unitProfile S C W₁ x := by
    funext x
    have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (unitProfile_reconstruct S hS hC W₁)
    simpa only [smul_apply,Complex.real_smul] using he.symm
  have hshort (r : ρ) :
      twistProfile (TerminalActualRow.shortProfile V W₂ (opened r) (Dstar r) (D r)) (σ r) (freq r) =
      fun x => (c₂:ℂ)*twistProfile
        (TerminalActualRow.shortProfile V (unitProfile S C W₂) (opened r) (Dstar r) (D r)) (σ r) (freq r) x := by
    funext x
    rw [←actualShort_eq_native,←actualShort_eq_native]
    unfold twistProfile
    rw [actualShort_reconstruct S hS hC]
    ring
  unfold nativeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hlong,hshort,original_profile_mul,original_profile_mul]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc₁,abs_of_nonneg hc₂]
  dsimp [c₁,c₂]
  ring

/-- One fixed Fourier weight for the exact native shifted energy. The unit
energy bound is the genuine supplier output, consumed without altering rows. -/
theorem native_common_pair_energy (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S) {C : ℝ} (hC : 0 < C) :
    ∃ J : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ (ρ : Type) (rows : Finset ρ) (η₁ η₂ : Character)
      (m₁ A₁ m₂ A₂ z : ρ→O) (tLong XLong XShort σ freq : ρ→ℝ)
      (V : ℝ→ℂ) (e : Fin 2×Fin 2) (τ : ℝ×ℝ)
      (opened : ρ→Bool) (Dstar D : ρ→ℝ) (marks : ρ→ℂ) (E : ℝ), 0 ≤ E →
      nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
        ((unitPair S C (commonPair e τ)).profile 0)
        ((unitPair S C (commonPair e τ)).profile 1) opened Dstar D marks ≤ E →
      nativeEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
        ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) opened Dstar D marks ≤
        K*pairWeight J τ*E := by
  obtain ⟨J,K,hK,hb⟩ := common_pair_payment S hC
  refine ⟨J,K,hK,?_⟩
  intro ρ rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V e τ opened Dstar D marks E hE hunit
  rw [nativeEnergy_reconstruct rows η₁ η₂ m₁ A₁ m₂ A₂ z tLong XLong XShort σ freq V
    ((commonPair e τ).profile 0) ((commonPair e τ).profile 1) opened Dstar D marks S hS hC]
  exact (mul_le_mul_of_nonneg_left hunit (by positivity)).trans
    (mul_le_mul_of_nonneg_right (hb e τ) hE)

#print axioms nativeEnergy_reconstruct
#print axioms native_common_pair_energy
end
end QRH.Cycle092.TerminalProfileUniform
