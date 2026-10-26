import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.ReflectedEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- A LOW child whose state exceeds the old capacity by at most `δ` after the fixed slot deletion, and whose reflected state
has margin `δ`, is bounded by the old moment with the constants of the reflection. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyPaidBands
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot CenteredMomentInductionEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional QuadraticInitialBound

universe u
variable {α : Type u}
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A LOW child whose capacity fails by at most `δ` after the fixed slot deletion, and whose reflected state has margin
`δ`, is bounded by the old moment up to the constants of the reflection: the deleted slots are paid on the LOW rows at
the price `q` each. -/
theorem reflected_low_incumbent [Fintype α]
    (Wslot : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ δ ξ ε₀ : ℝ) (degree : ℕ)
    (S : Finset (ℕ × ℕ))
    (haslot : 0 < aslot) (hWs : Function.support Wslot ⊆ Set.Icc aslot bslot) (hWc : Continuous Wslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hMcap : 0 ≤ Mcap)
    (hε : 0 ≤ ε) (hκ : 1/6 ≤ κ) (hδ : 0 ≤ δ) (hξ : 0 < ξ) (hε₀ : 0 < ε₀) :
    ∃ (Cr : ℝ) (Jexp : ℕ) (U : Finset (ℕ × ℕ)), 0 < Cr ∧ S ⊆ U ∧ degree ≤ Jexp ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (η₀ : Character) (Q : Ideal O) (C₀ C₁ : ℝ), 0 ≤ C₀ → 0 ≤ C₁ →
      ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀ →
      PositiveAt (α := α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q degree S C₁ →
      ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ) (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) → (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
      0 ≤ height → (∀ i, |v i| ≤ height) →
      ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap → s.width ≤ L →
      ∀ (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
      ∀ (q d mesh : ℝ), 0 ≤ q → 0 ≤ d → 0 ≤ mesh → (∀ i ∈ J, w i ≤ mesh) →
      ∀ (B : α → ℝ), (∀ i ∈ J, 0 ≤ B i) →
      (∀ z, s.radial.keep z → low z → ∀ i ∈ J,
        ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
          (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I) t (Z ^ (w i))‖ ^ 2 ≤
          B i * Z ^ (q * w i)) →
      length Z X₁ + length Z X₂ + 6 * κ * ((∑ i ∈ J, w i) - d) ≤ s.width + δ →
      (max 0 (s.width - length Z X₂ + ξ) + length Z X₁ + 6 * κ * ((∑ i ∈ J, w i) - d) + δ ≤ s.width ∨
        max 0 (s.width - length Z X₁ + ξ) + length Z X₂ + 6 * κ * ((∑ i ∈ J, w i) - d) + δ ≤ s.width) →
      ∃ R : Finset α, R ⊆ J ∧
        energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
          (fun i : J => primePool M H bslot (Z ^ (w i)))
          (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
          (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
        ((∏ i ∈ R, B i) * Z ^ (q * (d + mesh))) *
          ((C₀ + Cr * (C₁ + 1)) * diagonalControl s.radial.profile * (p.control U) ^ 2 *
            (1 + |t| + height) ^ Jexp * Z ^ (s.width + ε + ε₀)) := by
  obtain ⟨Cr, Jexp, U, hCr, hSU, hdJ, hev⟩ := reflected_remaining_energy_bound (α := α) M H hH Wslot aslot
    bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ δ ξ ε₀ degree S haslot hWs hWc ha hlo hhi hbΦ hBmask hMcap hε hκ
    hδ hξ hε₀
  refine ⟨Cr, Jexp, U, hCr, hSU, hdJ, ?_⟩
  filter_upwards [hev] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro η₀ Q C₀ C₁ hC₀ hC₁ hzero hpos J θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL low p
    X₁ X₂ hX₁ hX₂ hc₁ hc₂ q d mesh hq hd hm hwm B hB hslot hover hrefl
  obtain ⟨R, hR, hsum, hcover, he⟩ := fixed_low_energy s low J (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (σ i) (v i) I)
    t X₁ X₂ q d mesh hX₁ hX₂ hq hd hm w B (fun i _ => hw i) hwm hB hslot
  refine ⟨R, hR, he.trans (mul_le_mul_of_nonneg_left ?_ ?_)⟩
  · apply hZ.2 η₀ Q C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs hsL p
      X₁ X₂ hX₁ hX₂ hc₁ hc₂
    rcases hcover with hRJ | hdR
    · exact Or.inl hRJ
    · right
      have hsplit := Finset.sum_sdiff hR (f := w)
      have h6 : 6 * κ * (∑ i ∈ J \ R, w i) ≤ 6 * κ * ((∑ i ∈ J, w i) - d) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      refine ⟨by linarith, ?_⟩
      rcases hrefl with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  · exact mul_nonneg (Finset.prod_nonneg (fun i hi => hB i (hR hi)))
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)

end
end OAI.SevenEighths.Cycle63Moment.LowBranch

end Record1252270103Bootstrap.PR67
