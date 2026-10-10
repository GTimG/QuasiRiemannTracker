import OAI.NumberTheory.DirichletL.Moments.NaturalMaskedFloor

namespace ZetaZeroFree.Analytic.Moments

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentRadialEligibleEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def naturalPlainCharacter (η : Character) (z : O) : Character :=
  if hz : z ≠ 0 then (naturalRow η z hz).character else η

/-- The unmarked induction state admits fixed nonprincipal inducing rows.
Displayed moving zeros stay in the character modulus even when their exponent vanishes. -/
structure NaturalPlainState (Z B bΦ Cfixed : ℝ) where
  character : Character
  puncture : Ideal O
  radial : Radial
  rowWidth : ℝ
  characterWidth : ℝ
  displayedSupport : Ideal O
  displayed_squarefree : Squarefree displayedSupport
  displayed_bound : (displayedSupport.absNorm : ℝ) ≤ Z ^ characterWidth
  displayed_zeros : character.modulus ≤ displayedSupport
  base_ge_one : 1 ≤ Z
  row_nonneg : 0 ≤ rowWidth
  character_nonneg : 0 ≤ characterWidth
  scale_eq : radial.scale = Z ^ rowWidth
  modulus_bound : (character.modulus.absNorm : ℝ) ≤ Cfixed * Z ^ characterWidth
  puncture_ne_zero : puncture ≠ 0
  puncture_bound : (puncture.radical.absNorm : ℝ) ≤ Z ^ B
  radial_support : Function.support (radial.profile : ℝ → ℂ) ⊆ Set.Iic bΦ
  row_ne_zero : ∀ z, radial.keep z → z ≠ 0
  row_nonprincipal : ∀ z, radial.keep z → (naturalPlainCharacter character z).residue ≠ 1

namespace NaturalPlainState
variable {Z B bΦ Cfixed : ℝ}

def width (s : NaturalPlainState Z B bΦ Cfixed) : ℝ := s.rowWidth + s.characterWidth

def energy (s : NaturalPlainState Z B bΦ Cfixed)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (X₁ X₂ t₁ t₂ : ℝ) : ℝ :=
  radialEnergy (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false W₁ X₁ 0 t₁ *
    polynomial (excluded (naturalPlainCharacter s.character z) s.puncture)
      false W₂ X₂ 0 t₂) s.radial.keep s.radial.profile s.radial.scale

def restrictLive (s : NaturalPlainState Z B bΦ Cfixed) : NaturalPlainState Z B bΦ Cfixed :=
  { s with
    radial := { s.radial with
      keep := fun z => s.radial.keep z ∧
        s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) ≠ 0 }
    row_ne_zero := fun z hk => s.row_ne_zero z hk.1
    row_nonprincipal := fun z hk => s.row_nonprincipal z hk.1 }

lemma energy_restrictLive (s : NaturalPlainState Z B bΦ Cfixed)
    (W₁ W₂ : 𝓢(ℝ, ℂ)) (X₁ X₂ t₁ t₂ : ℝ) :
    s.restrictLive.energy W₁ W₂ X₁ X₂ t₁ t₂ = s.energy W₁ W₂ X₁ X₂ t₁ t₂ := by
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · by_cases hp : s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) = 0
    · simp [restrictLive, hk, hp]
    · simp [restrictLive, hk, hp]
  · simp [restrictLive, hk]

end NaturalPlainState

/-- The zero-slot mixed moment contract with uniform smooth and height orders.
The unconditional endpoint is proved in `Moments.Unconditional`. -/
def ZeroOnlyAt (a b bΦ B Cfixed L M ε Z : ℝ) (J : ℕ)
    (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalPlainState Z B bΦ Cfixed, s.width ≤ M →
  ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
    Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
  ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.energy W₁ W₂ X₁ X₂ t₁ t₂ ≤ C * diagonalControl s.radial.profile *
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
       (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
      (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (s.width + ε)

theorem mixed_height_profile_control (a b : ℝ) (ha : 0 < a) (S : Finset (ℕ × ℕ)) :
    ∃ J : ℕ, ∃ T : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ))
        (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
        (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b) (t₁ t₂ : ℝ),
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂))) ^ 2 ≤
          C * ((T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
               (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J := by
  obtain ⟨n, T, C, hC, he⟩ := normPowerProfile_source_control a b ha S
  refine ⟨2 * n, T, C ^ 4, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    (mul_le_mul (he W₁ hs₁ t₁) (he W₂ hs₂ t₂) (apply_nonneg _ _) (by positivity)) 2
  apply hh.trans_eq
  simp only [mul_pow, ← pow_mul, Nat.mul_comm n 2]
  ring

lemma mixed_height_energy_eq (a b : ℝ) (ha : 0 < a) (χ : O → Character)
    (r : Radial) (R : Ideal O) (W₁ W₂ : 𝓢(ℝ, ℂ))
    (hs₁ : Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b) (X₁ X₂ t₁ t₂ : ℝ) :
    radialEnergy (fun z => polynomial (excluded (χ z) R) false
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁) X₁ 0 0 *
      polynomial (excluded (χ z) R) false
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) X₂ 0 0) r.keep r.profile r.scale =
    radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale := by
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial]

/-- An unconditional width floor. The puncture budget is separate from effective width,
and the row condition includes nonprincipal characters of fixed conductor. -/
theorem mixed_width_floor (a b ε B ρ : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ : O → Character) (r : Radial) (R : Ideal O) (Z m q Q X₁ X₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → 0 ≤ q → 0 ≤ Q → r.scale = Z ^ m →
        m + q ≤ ρ → (R.radical.absNorm : ℝ) ≤ Z ^ B →
        (∀ z, r.keep z → (χ z).residue ≠ 1) →
        (∀ z, r.keep z → ((χ z).modulus.absNorm : ℝ) ≤ Q * Z ^ (m + q)) →
        0 < X₁ → 0 < X₂ →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
          C * Q ^ 4 * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 * Z ^ (m + q + 4 * ρ + ε) := by
  let η : ℝ := ε / (B + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hBη : B * η ≤ ε := by
    have he : η * (B + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨S, C, hC, he⟩ := CenteredMomentNaturalMaskedFloor.excluded_pair a b η ha hb hη
  refine ⟨S, C, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Z m q Q X₁ X₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  have hh := he W₁ W₂ hs₁ hs₂ χ r R (Q * Z ^ (m + q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχ hmod
  rw [hscale, max_eq_right (Real.one_le_rpow hZ hm)] at hh
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hd := diagonalControl_nonneg r.profile
  have hmask' : (R.radical.absNorm : ℝ) ^ η ≤ Z ^ ε := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hmask hη.le).trans
    rw [← Real.rpow_mul hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hBη
  have hp : Z ^ m * (Z ^ (m + q)) ^ 4 ≤ Z ^ (m + q + 4 * ρ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  rw [hscale]
  apply hh.trans
  calc
    _ = (C * Q ^ 4 * diagonalControl r.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2) *
        ((R.radical.absNorm : ℝ) ^ η * (Z ^ m * (Z ^ (m + q)) ^ 4)) := by ring
    _ ≤ (C * Q ^ 4 * diagonalControl r.profile *
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2) *
        (Z ^ ε * Z ^ (m + q + 4 * ρ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hmask' hp (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add hz]; ring

theorem mixed_width_floor_height (a b ε B ρ : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (χ : O → Character) (r : Radial) (R : Ideal O) (Z m q Q X₁ X₂ t₁ t₂ : ℝ),
        R ≠ 0 → 1 ≤ Z → 0 ≤ m → 0 ≤ q → 0 ≤ Q → r.scale = Z ^ m →
        m + q ≤ ρ → (R.radical.absNorm : ℝ) ≤ Z ^ B →
        (∀ z, r.keep z → (χ z).residue ≠ 1) →
        (∀ z, r.keep z → ((χ z).modulus.absNorm : ℝ) ≤ Q * Z ^ (m + q)) →
        0 < X₁ → 0 < X₂ →
        radialEnergy (fun z => polynomial (excluded (χ z) R) false W₁ X₁ 0 t₁ *
          polynomial (excluded (χ z) R) false W₂ X₂ 0 t₂) r.keep r.profile r.scale ≤
          C * Q ^ 4 * diagonalControl r.profile *
            ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁) *
             (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)) ^ 2 *
            (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + 4 * ρ + ε) := by
  obtain ⟨S₀, C₀, hC₀, he⟩ := mixed_width_floor a b ε B ρ ha hb hε hB
  obtain ⟨J, S, C₁, hC₁, hheight⟩ := mixed_height_profile_control a b ha S₀
  refine ⟨J, S, C₀ * C₁, by positivity, ?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Z m q Q X₁ X₂ t₁ t₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hsV₁ : Function.support (V₁ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
  have hsV₂ : Function.support (V₂ : ℝ → ℂ) ⊆ Set.Icc a b :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂
  have hh := he V₁ V₂ hsV₁ hsV₂ χ r R Z m q Q X₁ X₂ hR hZ hm hq hQ hscale hρ hmask hχ hmod hX₁ hX₂
  rw [mixed_height_energy_eq a b ha χ r R W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂] at hh
  have hd := diagonalControl_nonneg r.profile
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hheight W₁ W₂ hs₁ hs₂ t₁ t₂)
      (by positivity : 0 ≤ C₀ * Q ^ 4 * diagonalControl r.profile))
    (Real.rpow_nonneg (zero_le_one.trans hZ) _)).trans_eq
  ring

theorem zero_only_floor (a b bΦ B Cfixed L ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hbΦ : 0 < bΦ) (hB : 0 ≤ B) (hfixed : 0 < Cfixed) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, ZeroOnlyAt a b bΦ B Cfixed L (ε / 8) ε Z J S C := by
  obtain ⟨J, S, C₀, hC₀, he⟩ := mixed_width_floor_height a b (ε / 2) B (ε / 8)
    ha hb (by positivity) hB
  let F : ℝ := fixedConductorFactor
  have hF : 0 < F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0)))
  let Q : ℝ := Cfixed * F * bΦ
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨J, S, C₀ * Q ^ 4, by positivity, ?_⟩
  intro Z s hwidth W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ _ _
  let r : Radial := { s.radial with keep := fun z => s.radial.keep z ∧
      (s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) ≠ 0) }
  have hmod (z : O) (hk : r.keep z) :
      ((naturalPlainCharacter s.character z).modulus.absNorm : ℝ) ≤ Q * Z ^ (s.rowWidth + s.characterWidth) := by
    have hz := s.row_ne_zero z hk.1
    have hzn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ * Z ^ s.rowWidth := by
      rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
      exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hk.2)
    have hh : ((naturalRow s.character z hz).character.modulus.absNorm : ℝ) ≤
        (s.character.modulus.absNorm : ℝ) * F * ((Ideal.span {z}).absNorm : ℝ) := by
      dsimp [F]
      exact_mod_cast (naturalRow s.character z hz).natural_modulus_bound
    simp only [naturalPlainCharacter, dite_eq_left hz]
    apply hh.trans
    calc
      _ ≤ (Cfixed * Z ^ s.characterWidth) * F * (bΦ * Z ^ s.rowWidth) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right s.modulus_bound hF.le) hzn
          (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hfixed.le
            (Real.rpow_nonneg (zero_le_one.trans s.base_ge_one) _)) hF.le)
      _ = _ := by dsimp [Q]; rw [Real.rpow_add (zero_lt_one.trans_le s.base_ge_one)]; ring
  have hh := he W₁ W₂ hs₁ hs₂ (naturalPlainCharacter s.character) r s.puncture
    Z s.rowWidth s.characterWidth Q X₁ X₂ t₁ t₂ s.puncture_ne_zero s.base_ge_one
    s.row_nonneg s.character_nonneg hQ.le s.scale_eq hwidth s.puncture_bound
    (fun z hz => s.row_nonprincipal z hz.1) hmod hX₁ hX₂
  have hid : s.energy W₁ W₂ X₁ X₂ t₁ t₂ = radialEnergy
      (fun z => polynomial (excluded (naturalPlainCharacter s.character z) s.puncture) false W₁ X₁ 0 t₁ *
        polynomial (excluded (naturalPlainCharacter s.character z) s.puncture) false W₂ X₂ 0 t₂)
      r.keep r.profile r.scale := by
    unfold NaturalPlainState.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : s.radial.keep z
    · by_cases hp : s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / s.radial.scale) = 0
      · simp [r, hk, hp]
      · simp [r, hk, hp]
    · simp [r, hk]
  rw [hid]
  have hex : s.rowWidth + s.characterWidth + 4 * (ε / 8) + ε / 2 = s.width + ε := by
    dsimp [NaturalPlainState.width]
    ring
  rw [hex] at hh
  exact hh

end
end ZetaZeroFree.Analytic.Moments
