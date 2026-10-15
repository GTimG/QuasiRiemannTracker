/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.SecondZero.Source
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62SecondZero
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- The raw-volume gate comes from the actual nonzero frozen allocation;
no nominal child volume replaces the live residual plain factors. -/
theorem actual_common_volume_cap (N : ℕ) (b : ℝ) (hb : 1 ≤ b)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (hs : s.upper ≤ b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Z A c padding : ℝ) (hZ : 1 < Z) (hgeo : b^N ≤ Z^padding)
    (hvol : volume s ≤ Z^A) (hC : Z^c ≤ (C.absNorm : ℝ)) :
    Fintype.card (liveIndices B.val) ≤ N ∧
    volume (child s C R B τ t) ≤ Z^(A-c+padding) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hcn : 0 < Z^c := Real.rpow_pos_of_pos hz _
  refine ⟨(live_card_le B.val).trans hcard,?_⟩
  apply (common_volume_le N b hb s hcard hs C R B τ t hne).trans
  calc
    _ ≤ Z^padding*Z^A/Z^c := by
      apply div_le_div₀ (by positivity) _ hcn hC
      exact mul_le_mul hgeo hvol (volume_pos s).le (Real.rpow_nonneg hz.le _)
    _ = _ := by
      rw [←Real.rpow_add hz,←Real.rpow_sub hz]
      congr 1
      ring

/-- The extracted source uses its actual twice-child cap, including removal
from either plain pool and the full extracted prime-power divisor. -/
theorem actual_twice_volume_cap (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1 ≤ b) (h₁ : 1 ≤ b₁) (h₂ : 1 ≤ b₂)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P ≠ 0)
    (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (hslot : ∀ i, ∀ I ∈ (child s C R B τ t).slots i, IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (Z A c w padding : ℝ) (hZ : 1 < Z) (hgeo : geometry N b b₁ b₂ ≤ Z^padding)
    (hvol : volume s ≤ Z^A) (hC : Z^c ≤ (C.absNorm : ℝ))
    (hQN : Z^w ≤ (Q.absNorm : ℝ)^k) :
    Fintype.card (liveIndices Bp.val) ≤ N ∧
    0 ≤ sourceRadius (twiceChild s C R B τ t Q k Bp υ v) ∧
    volume (twiceChild s C R B τ t Q k Bp υ v) ≤ Z^(A-c-w+padding) ∧
    sourceRadius (twiceChild s C R B τ t Q k Bp υ v) ≤ Z^(A-c-w+padding) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hden : Z^(c+w) ≤ (C.absNorm : ℝ)*(Q.absNorm : ℝ)^k := by
    rw [Real.rpow_add hz]
    exact mul_le_mul hC hQN (Real.rpow_nonneg hz.le _) (by positivity)
  have hcp := twice_caps N b b₁ b₂ hb h₁ h₂ s hcard he C R B τ t hne
    Q hQ k hslot Bp υ v
  have hpower : geometry N b b₁ b₂*(volume s/((C.absNorm : ℝ)*(Q.absNorm : ℝ)^k)) ≤
      Z^(A-c-w+padding) := by
    rw [←mul_div_assoc]
    calc
      _ ≤ Z^padding*Z^A/Z^(c+w) := by
        apply div_le_div₀ (by positivity) _ (Real.rpow_pos_of_pos hz _) hden
        exact mul_le_mul hgeo hvol (volume_pos s).le (Real.rpow_nonneg hz.le _)
      _ = _ := by
        rw [←Real.rpow_add hz,←Real.rpow_sub hz]
        congr 1
        ring
  exact ⟨(live_card_le Bp.val).trans ((live_card_le B.val).trans hcard),
    hcp.2.1,hcp.2.2.1.trans hpower,hcp.2.2.2.trans hpower⟩

end
end OAI.SevenEighths.Cycle62SecondZero
#print axioms OAI.SevenEighths.Cycle62SecondZero.actual_common_volume_cap
#print axioms OAI.SevenEighths.Cycle62SecondZero.actual_twice_volume_cap
