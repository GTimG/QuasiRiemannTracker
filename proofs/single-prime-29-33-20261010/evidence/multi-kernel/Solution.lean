import ZetaZeroFree.Analytic.Final

namespace SinglePrime2933
open scoped _root_.DirichletCharacter
theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact ZetaZeroFree.Analytic.dirichletL_ne_zero_of_twenty_nine_thirty_thirds_lt_re χ hs hpole

theorem zeta {s : ℂ} (hs : (29 / 33 : ℝ) < s.re) (hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  exact ZetaZeroFree.Analytic.riemannZeta_ne_zero_of_twenty_nine_thirty_thirds_lt_re hs hpole

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hs : (29 / 33 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) :
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact ZetaZeroFree.Analytic.heckeL_ne_zero_of_twenty_nine_thirty_thirds_lt_re χ hs hpole
end SinglePrime2933

namespace SinglePrime2933
noncomputable section
universe u
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open ZetaZeroFree.Analytic.Moments.D3
open HeckeFamily HeckeDyadic CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CanonicalRowCompletion CanonicalQuadraticSieve Filter
local notation "O" => HeckeFamily.O
theorem appendixD3 (a b B L Mcap ε Cν : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ m q : ℝ, 0 ≤ m → 0 ≤ q → m + q ≤ Mcap →
      ∀ ν : Character, (ν.modulus.absNorm : ℝ) ≤ Cν →
        (∀ I : Ideal O, ¬ Supported I → idealCoeff ν I = 0) →
      ∀ (ι : Type u) [Fintype ι] (p : ι → O),
        (∀ i, Supported (Ideal.span {p i})) →
      ∀ e : ι → ℕ, (∀ i, 0 < e i) →
        (∏ i, ((Ideal.span {p i}).absNorm : ℝ)) ≤ Z ^ q →
      ∃ η : Character,
        (∀ I : Ideal O, idealCoeff η I =
          idealCoeff ν I * ∏ i, (idealRowHom (p i) I) ^ e i) ∧
        (∀ k : O, k ≠ 0 → ∀ R : Ideal O, R ≠ 0 → ∀ I : Ideal O,
          idealCoeff (excluded (naturalPlainCharacter η k) R) I =
            if IsCoprime I R then
              (idealCoeff ν I * ∏ i, (idealRowHom (p i) I) ^ e i) * idealRowHom k I
            else 0) ∧
        ∀ R : Ideal O, R ≠ 0 → (R.absNorm : ℝ) ≤ Z ^ B →
        ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
          (∀ z ∈ rows, (excluded (naturalPlainCharacter η z) R).residue ≠ 1) →
          (∀ z ∈ rows, ((Ideal.span {z}).absNorm : ℝ) ≤ Z ^ m) →
        ∀ W₁ W₂ : 𝓢(ℝ, ℂ), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
          Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
        ∀ X₁ X₂ t₁ t₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
          ∑ z ∈ rows,
            ‖polynomial (excluded (naturalPlainCharacter η z) R) false W₁ X₁ 0 t₁ *
              polynomial (excluded (naturalPlainCharacter η z) R) false W₂ X₂ 0 t₂‖ ^ 2 ≤
            C * (compactNorm J W₁ * compactNorm J W₂) ^ 2 *
              (1 + ‖t₁‖) ^ J * (1 + ‖t₂‖) ^ J * Z ^ (m + q + ε) := by
  exact ZetaZeroFree.Analytic.Moments.D3.mixed_plain_moment_radical a b B L Mcap ε Cν ha hB hM hε
end
end SinglePrime2933
