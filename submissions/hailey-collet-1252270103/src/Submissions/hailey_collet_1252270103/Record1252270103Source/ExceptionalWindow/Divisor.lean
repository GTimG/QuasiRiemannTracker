/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The exact artificial seed factor and its full finite Möbius harmonic payment. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.ExceptionalWindow.Pair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter UniqueFactorizationMonoid
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

lemma corrected_seed_exact {ι : Type*} [Fintype ι] (s : Input ι)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ) :
    correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ =
      (seed.absNorm:ℝ)^εL/(seed.absNorm:ℝ) *
        correctedExceptionalBudget s S W₁ W₂ Φ Q C D 1 U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  unfold correctedExceptionalBudget
  simp only [map_one, Nat.cast_one, Real.one_rpow, mul_one, div_one]
  ring

/-- One constant, before the exponent and the entire moving finite ideal family.
The sum is full: all original Möbius weights, including zeros, remain present. -/
theorem full_seed_mass_subpower (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ H : ℝ, 0<H ∧ ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      ∀ (εL : ℝ), 0≤εL → ∀ (Ls : Finset (Ideal O)),
      (∀ L∈Ls, (L.absNorm:ℝ)≤Z^B) →
      (∑ L∈Ls, ‖(moebius L:ℂ)‖*((L.absNorm:ℝ)^εL/(L.absNorm:ℝ))) ≤
        H*Z^(δ+B*εL) := by
  obtain ⟨H,hH,hbound⟩ := CenteredMomentMobiusHarmonicMass.full_mass_subpower B δ hB hδ
  refine ⟨H,hH,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro εL hεL Ls hLs
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hp (L : Ideal O) (hL : L∈Ls) : (L.absNorm:ℝ)^εL≤Z^(B*εL) := by
    calc
      _≤(Z^B)^εL := Real.rpow_le_rpow (Nat.cast_nonneg _) (hLs L hL) hεL
      _=Z^(B*εL) := (Real.rpow_mul hZ0.le B εL).symm
  calc
    _≤∑ L∈Ls, Z^(B*εL)*(‖(moebius L:ℂ)‖/(L.absNorm:ℝ)) := by
      apply Finset.sum_le_sum
      intro L hL
      have hh := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hp L hL) (Nat.cast_nonneg L.absNorm)) (norm_nonneg (moebius L:ℂ))
      convert hh using 1 <;> ring
    _=Z^(B*εL)*(∑ L∈Ls, ‖(moebius L:ℂ)‖/(L.absNorm:ℝ)) := (Finset.mul_sum ..).symm
    _≤Z^(B*εL)*(H*Z^δ) := mul_le_mul_of_nonneg_left
      (hZ.2 Ls (fun L hL _ => hLs L hL)) (Real.rpow_nonneg hZ0.le _)
    _=H*Z^(δ+B*εL) := by rw [Real.rpow_add hZ0]; ring
end
end OAI.SevenEighths.Record1252270103Source.ExceptionalWindow
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.corrected_seed_exact
#print axioms OAI.SevenEighths.Record1252270103Source.ExceptionalWindow.full_seed_mass_subpower
