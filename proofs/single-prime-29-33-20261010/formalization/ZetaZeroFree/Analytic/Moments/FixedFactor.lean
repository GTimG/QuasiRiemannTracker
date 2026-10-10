import ZetaZeroFree.Analytic.Moments.Source

namespace ZetaZeroFree.Analytic.Moments.D3
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open HeckeFamily HeckeDyadic CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPolynomialEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource ConcreteTraceCRT QuadraticInitialBound Filter
local notation "O" => HeckeFamily.O

/-- A fixed conductor factor costs an arbitrarily small effective-width padding. -/
def padState {Z B radial Cfixed : ℝ}
    (s : NaturalPlainState Z B radial Cfixed) (t : ℝ)
    (ht : 0 ≤ t) (hC : Cfixed ≤ Z ^ t) : NaturalPlainState Z B radial 1 where
  character := s.character
  puncture := s.puncture
  radial := s.radial
  rowWidth := s.rowWidth
  characterWidth := s.characterWidth + t
  displayedSupport := s.displayedSupport
  displayed_squarefree := s.displayed_squarefree
  displayed_bound := s.displayed_bound.trans
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith))
  displayed_zeros := s.displayed_zeros
  base_ge_one := s.base_ge_one
  row_nonneg := s.row_nonneg
  character_nonneg := add_nonneg s.character_nonneg ht
  scale_eq := s.scale_eq
  modulus_bound := by
    have hz : 0 < Z := zero_lt_one.trans_le s.base_ge_one
    apply s.modulus_bound.trans
    simpa only [one_mul, mul_one, Real.rpow_add hz, mul_comm] using
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hz.le s.characterWidth)
  puncture_ne_zero := s.puncture_ne_zero
  puncture_bound := s.puncture_bound
  radial_support := s.radial_support
  row_ne_zero := s.row_ne_zero
  row_nonprincipal := s.row_nonprincipal

theorem padState_width {Z B radial Cfixed : ℝ}
    (s : NaturalPlainState Z B radial Cfixed) (t : ℝ)
    (ht : 0 ≤ t) (hC : Cfixed ≤ Z ^ t) :
    (padState s t ht hC).width = s.width + t := by
  simp only [NaturalPlainState.width, padState]
  ring

theorem padState_energy {Z B radial Cfixed : ℝ}
    (s : NaturalPlainState Z B radial Cfixed) (t : ℝ)
    (ht : 0 ≤ t) (hC : Cfixed ≤ Z ^ t)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (X₁ X₂ t₁ t₂ : ℝ) :
    (padState s t ht hC).energy W₁ W₂ X₁ X₂ t₁ t₂ =
      s.energy W₁ W₂ X₁ X₂ t₁ t₂ := rfl

theorem eventually_fixed_factor (Cfixed t : ℝ) (ht : 0 < t) :
    ∀ᶠ Z : ℝ in atTop, Cfixed ≤ Z ^ t :=
  (tendsto_rpow_atTop ht).eventually (eventually_ge_atTop Cfixed)

theorem padded_plain_bound
    (a b radial B L Mcap ε Z Cfixed t : ℝ) (J : ℕ)
    (S : Finset (ℕ × ℕ)) (C : ℝ) (ht : 0 ≤ t) (hC : Cfixed ≤ Z ^ t)
    (hend : AllNonprincipalAt a b radial B L (Mcap + t) ε Z J S C)
    (s : NaturalPlainState Z B radial Cfixed) (hw : s.width ≤ Mcap)
    (hR : (s.puncture.absNorm : ℝ) ≤ Z ^ B)
    (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (X₁ X₂ t₁ t₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hL₁ : X₁ ≤ Z ^ L) (hL₂ : X₂ ≤ Z ^ L) :
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤
      C * diagonalControl s.radial.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
        (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + t + ε) := by
  have hp := hend (padState s t ht hC)
    (by rw [padState_width]; linarith) hR W₁ W₂ hs₁ hs₂
    X₁ X₂ t₁ t₂ hX₁ hX₂ hL₁ hL₂
  have hprofile : (padState s t ht hC).radial.profile = s.radial.profile := rfl
  rw [padState_energy, padState_width, hprofile] at hp
  exact hp

/-- A radial majorant equal to one on the unit interval bounds the sharp row cutoff. -/
theorem sharp_sum_le_energy
    {Z B radial Cfixed : ℝ} (s : NaturalPlainState Z B radial Cfixed)
    (rows : Finset O)
    (hrow : ∀ z ∈ rows, s.radial.keep z)
    (hnorm : ∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ s.radial.scale)
    (hone : ∀ x ∈ Set.Icc (0 : ℝ) 1, s.radial.profile x = 1)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (a b : ℝ) (hb : 0 ≤ b)
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b)
    (X₁ X₂ t₁ t₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ∑ z ∈ rows,
      ‖polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
          false W₂ X₂ 0 t₂‖ ^ 2 ≤ s.energy W₁ W₂ X₁ X₂ t₁ t₂ := by
  let χ := fun z : O => excluded (naturalPlainCharacter s.character z) s.puncture
  let f := fun z : O => polynomial (χ z) false W₁ X₁ 0 t₁ *
    polynomial (χ z) false W₂ X₂ 0 t₂
  have hsum : Summable (fun z : O => if s.radial.keep z then
      ‖f z‖ ^ 2 * (s.radial.profile (‖eisEmbedding z‖ ^ 2 / s.radial.scale)).re
      else 0) := by
    simpa only [mul_one, f] using pair_radial_summable χ (fun _ => 1)
      (fun _ => t₁) (fun _ => t₂) W₁ W₂ a b a b X₁ X₂ 1 hb hb hX₁ hX₂
      hs₁ hs₂ (by intro z; simp) s.radial.keep s.radial.profile
      s.radial.scale s.radial.scale_pos
  have heq : (∑ z ∈ rows, ‖f z‖ ^ 2) = ∑ z ∈ rows,
      if s.radial.keep z then
        ‖f z‖ ^ 2 * (s.radial.profile (‖eisEmbedding z‖ ^ 2 / s.radial.scale)).re
      else 0 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hx : ‖eisEmbedding z‖ ^ 2 / s.radial.scale ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) s.radial.scale_pos.le,
        (div_le_one s.radial.scale_pos).mpr ?_⟩
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      exact hnorm z hz
    simp only [ite_eq_left (hrow z hz), hone _ hx, Complex.one_re, mul_one]
  rw [heq]
  exact sum_le_hasSum rows (fun z _ => by
    split_ifs with hk
    · exact mul_nonneg (sq_nonneg _) (s.radial.nonneg z)
    · exact le_rfl) hsum.hasSum

end
end ZetaZeroFree.Analytic.Moments.D3
