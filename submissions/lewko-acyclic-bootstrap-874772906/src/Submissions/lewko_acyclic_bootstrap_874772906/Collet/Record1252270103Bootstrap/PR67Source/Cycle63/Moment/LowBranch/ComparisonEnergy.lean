import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.ReflectedEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.SecondLevelComparison
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The energy of the comparison daughter of a state of the second step: the old moment at the width of the state, for
the comparison pair of plain factors, from the facts of the position of the state. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open Cycle63FirstGeometry

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A plain factor whose length is positive is the power of `Z` with that length. -/
theorem eq_rpow_length {Z X : ℝ} (hZ : 1 < Z) (hX : 0 < X) (hlen : 0 < length Z X) : X = Z ^ length Z X := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  rw [length_eq_max_logb hZ hX] at hlen ⊢
  have hlog : 0 < Real.logb Z X := by
    rcases lt_max_iff.mp hlen with h | h
    · exact absurd h (lt_irrefl 0)
    · exact h
  rw [max_eq_right hlog.le, Real.rpow_logb hZ0 hZ.ne' hX]

/-- The energy of the comparison daughter of a state of the second step, from the facts that the comparison pair of
plain factors fits. The state `s` has width `W`, plain factors `X₁`, `X₂` of lengths `x₁`, `x₂` and slots of length
`z`. The comparison pair is `Z^Lc` and `Z^(x₁ + x₂ - Lc)` (the pair `comparisonFirstAt Z Lc`,
`comparisonSecondAt Z Lc X₁ X₂`) for any real `Lc`. The facts are: the plain lengths are positive with sum at most
`W`; the comparison length is in `[0, W/4]` and `x₁ + x₂ - Lc` is nonnegative; the comparison pair exceeds the unit by
at most the margin `δ` (`Lc + (x₁ + x₂ - Lc) + 6 slotPrice z ≤ W + δ`); and its reflected state, the long factor
reflected with the slack `ξ`, leaves the margin `δ` (`max 0 (W - (x₁ + x₂ - Lc) + ξ) + Lc + 6 slotPrice z + δ ≤ W`).
Then the energy of the daughter is at most the old moment at the width of the state, up to `Z^ε₀`. This is
`reflected_masked_energy_core` at the slot price, the margin `δ` and the slack `ξ`; the constants precede the base
`Z`, the character `η₀`, the ideal `Q` and the state. The facts are the output of `Cycle63.comparison_core_of_facts`;
the statement is invariant under the change of base `Z ↦ Z^W`. -/
theorem punctured_comparison_energy_of_fits
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε δ ξ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (K : ℝ), 0 ≤ K →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε Cycle63.Optimization.slotPrice Z η₀ Q
        degree S K →
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      ∀ (x₁ x₂ z W Lc : ℝ),
        x₁ = length Z X₁ → x₂ = length Z X₂ → z = ∑ i ∈ J, w i → W = s.width →
        0 < x₁ → 0 < x₂ → x₁ + x₂ ≤ W → 0 ≤ Lc → Lc ≤ W / 4 → 0 ≤ x₁ + x₂ - Lc →
        Lc + (x₁ + x₂ - Lc) + 6 * Cycle63.Optimization.slotPrice * z ≤ W + δ →
        max 0 (W - (x₁ + x₂ - Lc) + ξ) + Lc + 6 * Cycle63.Optimization.slotPrice * z + δ ≤ W →
      energy s.character s.mask 1 t W₁ W₂
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) (comparisonFirstAt Z Lc) (comparisonSecondAt Z Lc X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cr * (K + 1) * diagonalControl s.radial.profile * (sourceControl U W₁ * sourceControl U W₂) ^ 2 *
        (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀) := by
  have hκ := Cycle63.Optimization.slotPrice_mem
  obtain ⟨Cr, Jexp, U, hCr, hev⟩ := reflected_masked_energy_core (α := α) M H hH Wslot aslot bslot a b bΦ Bmask L
    Lslot lo hi Mcap ε Cycle63.Optimization.slotPrice δ ξ ε₀ degree S haslot hWs hWc ha hlo hhi hbΦ
    hBmask hMcap hε (by linarith only [hκ.1]) hδ hξ hε₀
  refine ⟨Cr, Jexp, U, hCr, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η₀ Q K hK hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
    x₁ x₂ z W Lc hx₁ hx₂ hz hWeq hpos₁ hpos₂ hsum hLc0 hLc4 hal0 hover hrefl
  have hZ1 : 1 < Z := hZ.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hWnn : 0 ≤ W := by linarith only [hLc0, hLc4]
  -- the plain factors are the powers of `Z` with their lengths
  have hX₁eq : X₁ = Z ^ x₁ := by
    have := eq_rpow_length hZ1 hX₁ (hx₁ ▸ hpos₁)
    rwa [← hx₁] at this
  have hX₂eq : X₂ = Z ^ x₂ := by
    have := eq_rpow_length hZ1 hX₂ (hx₂ ▸ hpos₂)
    rwa [← hx₂] at this
  have hY₂ : comparisonSecondAt Z Lc X₁ X₂ = Z ^ (x₁ + x₂ - Lc) := by
    have h := comparisonSecondAt_pow Z Lc x₁ x₂ hZ1
    rwa [← hX₁eq, ← hX₂eq] at h
  have hY₁ : comparisonFirstAt Z Lc = Z ^ Lc := rfl
  rw [hY₂, hY₁]
  have hlen₁ : length Z (Z ^ Lc) = Lc := by rw [length_rpow Z Lc hZ1, max_eq_right hLc0]
  have hlen₂ : length Z (Z ^ (x₁ + x₂ - Lc)) = x₁ + x₂ - Lc := by
    rw [length_rpow Z _ hZ1, max_eq_right hal0]
  refine hZ.2 η₀ Q K hK hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL W₁ W₂ hs₁ hs₂ (Z ^ Lc)
    (Z ^ (x₁ + x₂ - Lc)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hLc4, hWeq, hsL, hWnn]))
    (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith only [hsum, hLc0, hWeq, hsL])) ?_ ?_
  · rw [hlen₁, hlen₂, ← hz, ← hWeq]
    exact hover
  · rw [hlen₁, hlen₂, ← hz, ← hWeq]
    exact hrefl

/-- The energy of the comparison daughter of a state of the second step is bounded by the old moment at the width of
the state, up to `Z^ε₀`. The comparison pair of plain factors is `Z^Lc` and `Z^(x₁ + x₂ - Lc)` (the pair
`comparisonFirstAt Z Lc`, `comparisonSecondAt Z Lc X₁ X₂`), for the comparison length
`Lc = W * secondComparisonLength (x₁/W) (x₂/W) (z/W)`, over all the slots `J`, in a state `s` of width `W` whose plain
lengths `x₁`, `x₂` are the lengths of the plain factors `X₁`, `X₂` and whose slot length `z` is that of the slots. The
facts of the position of the state (`hfacts`, about the ratios `x/W`), its overshoot over the old capacity (`hF`: at
most `δ`) and the margin (`hmargin`: `δ + ξ` at most a hundredth of the width) are the hypotheses; the statement is
invariant under the change of base `Z ↦ Z^W`. It is `punctured_comparison_energy_of_fits` with the facts of
`comparison_core_of_facts`. -/
theorem punctured_comparison_energy
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε δ ξ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (K : ℝ), 0 ≤ K →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε Cycle63.Optimization.slotPrice Z η₀ Q
        degree S K →
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (W₁ W₂ : 𝓢(ℝ, ℂ)), Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
        Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      ∀ (G : ℕ) (x₁ x₂ z W Lc : ℝ), 0 < G →
        x₁ = length Z X₁ → x₂ = length Z X₂ → z = ∑ i ∈ J, w i → W = s.width →
        (Cycle63.childPosition (1 / G) (x₁ / W) (x₂ / W) (z / W)).Facts →
        x₁ + x₂ + 6 * Cycle63.Optimization.slotPrice * z - W ≤ δ → δ + ξ ≤ W / 100 →
        Lc = W * Cycle63.Optimization.secondComparisonLength (x₁ / W) (x₂ / W) (z / W) →
      energy s.character s.mask 1 t W₁ W₂
        (fun i : J => primePool M H bslot (Z ^ (w i)))
        (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
        (fun i : J => Z ^ (w i)) (comparisonFirstAt Z Lc) (comparisonSecondAt Z Lc X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cr * (K + 1) * diagonalControl s.radial.profile * (sourceControl U W₁ * sourceControl U W₂) ^ 2 *
        (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀) := by
  obtain ⟨Cr, Jexp, U, hCr, hev⟩ := punctured_comparison_energy_of_fits (α := α) M H hH Wslot aslot bslot a b bΦ
    Bmask L Lslot lo hi Mcap ε δ ξ ε₀ degree S haslot hWs hWc ha hlo hhi hbΦ hBmask hMcap hε hδ hξ hε₀
  refine ⟨Cr, Jexp, U, hCr, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η₀ Q K hK hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ G
    x₁ x₂ z W Lc hG hx₁ hx₂ hz hWeq hfacts hF hmargin hLc
  have hz0 : 0 ≤ z := by
    rw [hz]
    exact Finset.sum_nonneg fun i _ => hw i
  have hWpos : 0 < W := by linarith only [hmargin, hξ, hδ]
  obtain ⟨hpos₁, hpos₂, hsum, hLc0, hLc4, hal0, hover, hrefl⟩ :=
    Cycle63.comparison_core_of_facts hG hz0 hWpos hfacts hF hmargin (by linarith only [hmargin, hξ]) hLc
  exact hZ.2 η₀ Q K hK hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
    x₁ x₂ z W Lc hx₁ hx₂ hz hWeq hpos₁ hpos₂ hsum hLc0 hLc4 hal0 hover hrefl

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
