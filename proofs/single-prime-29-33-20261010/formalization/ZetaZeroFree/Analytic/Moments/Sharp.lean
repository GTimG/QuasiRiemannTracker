import ZetaZeroFree.Analytic.Moments.FixedFactor
import OAI.NumberTheory.DirichletL.Moments.RadicalFamily

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open HeckeFamily HeckeDyadic CenteredMomentRadialEligibleEnergy
open CenteredMomentNaturalRowSource ConcreteTraceCRT QuadraticInitialBound Filter
local notation "O" => HeckeFamily.O

/-- The sharp row family retains every natural character zero and the common puncture. -/
def cutoffState (η : Character) (R : Ideal O) (Φ : 𝓢(ℝ, ℂ))
    (Z B radial Cfixed m q : ℝ)
    (hZ : 1 ≤ Z) (hm : 0 ≤ m) (hq : 0 ≤ q)
    (hη : (η.modulus.absNorm : ℝ) ≤ Cfixed * Z ^ q)
    (hR : R ≠ 0) (hRnorm : (R.absNorm : ℝ) ≤ Z ^ B)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hp : ∀ x, 0 ≤ (Φ x).re) : NaturalPlainState Z B radial Cfixed where
  character := η
  puncture := R
  radial := {
    keep := fun z => z ≠ 0 ∧ (naturalPlainCharacter η z).residue ≠ 1
    profile := Φ
    scale := Z ^ m
    scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
    nonneg := fun z => hp _ }
  rowWidth := m
  characterWidth := q
  displayedSupport := ⊤
  displayed_squarefree := by rw [← Ideal.one_eq_top]; exact squarefree_one
  displayed_bound := by simpa using Real.one_le_rpow hZ hq
  displayed_zeros := le_top
  base_ge_one := hZ
  row_nonneg := hm
  character_nonneg := hq
  scale_eq := rfl
  modulus_bound := hη
  puncture_ne_zero := hR
  puncture_bound := by
    have hn : R.radical.absNorm ≤ R.absNorm := Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I := R))))
    exact (by exact_mod_cast hn : (R.radical.absNorm : ℝ) ≤ R.absNorm).trans hRnorm
  radial_support := hs
  row_ne_zero := fun _ hz => hz.1
  row_nonprincipal := fun _ hz => hz.2

/-- This finite presentation bridge imposes no product-length or lower-conductor restriction. -/
theorem finite_mixed_from_all_nonprincipal
    (a b radial B L Mcap ε Z Cfixed t m q : ℝ)
    (J : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (hZ : 1 ≤ Z) (hm : 0 ≤ m) (hq : 0 ≤ q) (hmq : m + q ≤ Mcap)
    (ht : 0 ≤ t) (hfixed : Cfixed ≤ Z ^ t)
    (hend : AllNonprincipalAt a b radial B L (Mcap + t) ε Z J S C)
    (η : Character) (hη : (η.modulus.absNorm : ℝ) ≤ Cfixed * Z ^ q)
    (R : Ideal O) (hR : R ≠ 0) (hRnorm : (R.absNorm : ℝ) ≤ Z ^ B)
    (Φ : 𝓢(ℝ, ℂ))
    (hΦs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hΦp : ∀ x, 0 ≤ (Φ x).re)
    (hΦ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, Φ x = 1)
    (rows : Finset O)
    (hrows : ∀ z ∈ rows, z ≠ 0)
    (hnp : ∀ z ∈ rows, (naturalPlainCharacter η z).residue ≠ 1)
    (hnorm : ∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ Z ^ m)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (hb : 0 ≤ b)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (X₁ X₂ t₁ t₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hL₁ : X₁ ≤ Z ^ L) (hL₂ : X₂ ≤ Z ^ L) :
    ∑ z ∈ rows,
      ‖polynomial (excluded (naturalPlainCharacter η z) R) false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter η z) R) false W₂ X₂ 0 t₂‖ ^ 2 ≤
      C * diagonalControl Φ *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + t + ε) := by
  let s := cutoffState η R Φ Z B radial Cfixed m q hZ hm hq hη hR hRnorm hΦs hΦp
  have he := sharp_sum_le_energy s rows (fun z hz => ⟨hrows z hz, hnp z hz⟩)
    hnorm hΦ1 W₁ W₂ a b hb hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂
  have hp := padded_plain_bound a b radial B L Mcap ε Z Cfixed t J S C ht hfixed
    hend s hmq hRnorm W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂
  exact he.trans hp

end
end ZetaZeroFree.Analytic.Moments.D3
