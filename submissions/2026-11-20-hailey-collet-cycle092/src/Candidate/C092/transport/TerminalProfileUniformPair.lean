/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Two genuine Profiles, early finite gates, and exact bilinear homogeneity. -/
import Candidate.C092.transport.TerminalProfileUniformEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap ContDiff BigOperators
open Set OAI OAI.SevenEighths HeckeFamily CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles
local notation "O" => HeckeFamily.O

def unitPair {a b : ℝ} (S : Finset (ℕ×ℕ)) (C : ℝ) (p : Profiles a b) : Profiles a b where
  profile := fun i => unitProfile S C (p.profile i)
  support := fun i => (unitProfile_support S C (p.profile i)).trans (p.support i)

def UnitGates {a b : ℝ} (V : ℝ→ℂ) (lo hi : ℝ) (orders : Finset ℕ)
    (extra : Finset (ℕ×ℕ)) (p : Profiles a b) : Prop :=
  (∀ i,sourceControl extra (p.profile i) ≤ 1) ∧
  ∀ i, ∀ j ∈ orders, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
    (1+|t|)^j*‖mellin (p.profile i) ((σ:ℂ)+t*Complex.I)‖ ≤ 1 ∧
    ∀ R ∈ Icc (0:ℝ) 4,
      (1+|t|)^j*‖mellin (ratioProfile V (p.profile i) R) ((σ:ℂ)+t*Complex.I)‖ ≤ 1

/-- This bank is chosen after the unit-bound supplier's finite orders, before
BOTH original profiles, Fourier parameters, rows and independent heights. -/
theorem actual_pair_unit_bank (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (orders : Finset ℕ) (extra : Finset (ℕ×ℕ)) :
    ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ extra ⊆ S ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ p : Profiles a b, UnitGates V lo hi orders extra (unitPair S C p) ∧
      ∀ i,(C*sourceControl S (p.profile i)) • (unitPair S C p).profile i = p.profile i := by
  obtain ⟨S,hS,hex,C,hC,hb⟩ := actual_unit_profile_bank V hV a b ha lo hi orders extra
  refine ⟨S,hS,hex,C,hC,?_⟩
  intro p
  have hc i := hb (p.profile i) (p.support i)
  exact ⟨⟨fun i => (hc i).2.2.1,fun i => (hc i).2.2.2⟩,fun i => (hc i).2.1⟩

/-- Apply an actual unit-profile supplier result and restore the original
finite energy. This is algebraic transport; it supplies no analytic premise. -/
theorem homogeneous_of_unit {ρ : Type} {a b : ℝ} (rows : Finset ρ) (η₁ η₂ : Character)
    (m₁ A₁ m₂ A₂ z : ρ→O) (t₁ t₂ X₁ X₂ : ρ→ℝ)
    (V : ℝ→ℂ) (p : Profiles a b) (opened : ρ→Bool) (R : ρ→ℝ) (marks : ρ→ℂ)
    (S : Finset (ℕ×ℕ)) (hS : (0,0) ∈ S) {C : ℝ} (hC : 0 < C) (E : ℝ)
    (hunit : actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
      ((unitPair S C p).profile 0) ((unitPair S C p).profile 1) opened R marks ≤ E) :
    actualEnergy rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
      (p.profile 0) (p.profile 1) opened R marks ≤ C^4*(p.control S)^2*E := by
  rw [actualEnergy_reconstruct rows η₁ η₂ m₁ A₁ m₂ A₂ z t₁ t₂ X₁ X₂ V
    (p.profile 0) (p.profile 1) opened R marks S hS hC]
  exact mul_le_mul_of_nonneg_left hunit (by positivity)

#print axioms actual_pair_unit_bank
#print axioms homogeneous_of_unit
end
end QRH.Cycle092.TerminalProfileUniform
