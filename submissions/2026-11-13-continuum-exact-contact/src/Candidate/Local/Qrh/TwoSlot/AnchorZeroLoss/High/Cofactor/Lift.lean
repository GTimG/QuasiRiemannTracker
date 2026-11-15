/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The sixth-power decomposition `raw_sixth_weighted_sum` and the ideal series
`ideal_sixth_power_summable` are Hailey Collet's (Record12518109Gain/RootCompletion.lean,
LocalMoment/RawSixthDensity.lean, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor.Restore
import Submissions.hailey_collet_1252270103.Record12518109Gain.RootCompletion

/-!
# High.Cofactor.Lift

From sixth-free cores to ALL nonzero frequencies.

Every nonzero frequency is `h = c·B⁶` (`sixthFrequencyEquiv`) with a sixth-free core `c : FreeRow`
and a cofactor ideal `B`; `∑_{h∈R} f h = ∑_B ∑_{c ∈ sixthFreeFiber R B} f (c·B⁶)` (HC
`raw_sixth_weighted_sum`). If every occupied cofactor class is bounded by `A · N(B)^(-1)` — the
cofactor count `(M-d)/6 = log_Z N(B)` — then the whole sum is `≤ A · D_δ · X^δ`
(`cofactor_sum_le`, `X ≥` all raw norms; the series `∑ N(B)^(-1-6δ)` converges).

`cofactor_energy_le` states this with exponents: if the class of `B` is `≤ K Z^g` with
`g ≤ E - log_Z N(B)`, then `∑_R f ≤ K D Z^(E + δ M)` (`X = Z^M`).

`high_cofactor_energy` is the HIGH form: with core width `d_B = M - 6 log_Z N(B) ∈ [0, M]`,
* large cores (`2/25 < d_B`): class energy `≤ K Z^(d_B + highPriceF(P,S,d_B) + λ)` (the core
  batch energy of `High.Batch`, rescaled by `Cofactor.Restore.scaled_*`);
* tiny cores (`d_B ≤ 2/25`): class energy `≤ K Z^(d_B + (3/4)P + S + λ)`;
give the HIGH energy over all rows `≤ K D Z^(M + highPriceF(P,S,M) + λ + δ M)`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open LocalMoment HeckeFamily HeckeInverseAmplification ConcretePrimeRowBridge ProbeHighRowFamily
open ProbePhysical Record12518109GainRoot
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- An occupied cofactor class has `N(B)⁶ ≤ X`. -/
theorem cofactor_norm_le (R : Finset NonzeroFrequency) (X : ℝ)
    (hR : ∀ h ∈ R, rawFrequencyNorm h ≤ X) (B : NZIdeal)
    (hB : B ∈ (sixthPairs R).image Prod.snd) :
    (B.val.absNorm : ℝ) ^ 6 ≤ X := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
  have hr := hR _ ((mem_sixthPairs R p).mp hp)
  rw [raw_sixth_norm] at hr
  have h1 := rowNorm_ge_one p.1
  have h0 : (0 : ℝ) ≤ (p.2.val.absNorm : ℝ) ^ 6 := by positivity
  nlinarith

/-- An occupied cofactor class has a nonempty core fiber. -/
theorem cofactor_fiber_nonempty (R : Finset NonzeroFrequency) (B : NZIdeal)
    (hB : B ∈ (sixthPairs R).image Prod.snd) : (sixthFreeFiber R B).Nonempty := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨p.1, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩⟩

/-- **Cofactor lift.** -/
theorem cofactor_sum_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency → ℝ) (X A : ℝ),
      1 ≤ X → 0 ≤ A → (∀ h ∈ R, rawFrequencyNorm h ≤ X) →
      (∀ B : NZIdeal, (sixthFreeFiber R B).Nonempty →
        (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤
          A * (B.val.absNorm : ℝ) ^ (-1 : ℝ)) →
      (∑ h ∈ R, f h) ≤ A * D * X ^ δ := by
  let w : NZIdeal → ℝ := fun B => (B.val.absNorm : ℝ) ^ (-6 * ((1 + 6 * δ) / 6))
  have hw : Summable w := ideal_sixth_power_summable ((1 + 6 * δ) / 6) (by linarith)
  have hw0 (B : NZIdeal) : 0 ≤ w B := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D : ℝ := (∑' B : NZIdeal, w B) + 1
  have hsum : 0 ≤ ∑' B : NZIdeal, w B := tsum_nonneg hw0
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro R f X A hX hA hR hB
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hn (B : NZIdeal) : 1 ≤ (B.val.absNorm : ℝ) := by
    have hp : 0 < B.val.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  let roots := (sixthPairs R).image Prod.snd
  have hterm (B : NZIdeal) (hBr : B ∈ roots) :
      (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤ A * X ^ δ * w B := by
    refine (hB B (cofactor_fiber_nonempty R B hBr)).trans ?_
    have hN0 : 0 < (B.val.absNorm : ℝ) := zero_lt_one.trans_le (hn B)
    have hN6 := cofactor_norm_le R X hR B hBr
    -- `N^(-1) = N^(6δ) · N^(-(1+6δ)) ≤ X^δ · w B`
    have hsplit : (B.val.absNorm : ℝ) ^ (-1 : ℝ) =
        (B.val.absNorm : ℝ) ^ (6 * δ) * w B := by
      dsimp [w]
      rw [← Real.rpow_add hN0]
      congr 1; ring
    have hpow : (B.val.absNorm : ℝ) ^ (6 * δ) ≤ X ^ δ := by
      have : (B.val.absNorm : ℝ) ^ (6 * δ) = ((B.val.absNorm : ℝ) ^ (6 : ℕ)) ^ δ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
      rw [this]
      exact Real.rpow_le_rpow (by positivity) hN6 hδ.le
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA) (hw0 B)
  rw [raw_sixth_weighted_sum]
  calc
    _ ≤ ∑ B ∈ roots, A * X ^ δ * w B := Finset.sum_le_sum hterm
    _ = A * X ^ δ * ∑ B ∈ roots, w B := by rw [Finset.mul_sum]
    _ ≤ A * X ^ δ * D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (hw.sum_le_tsum _ (fun B _ => hw0 B)).trans (by dsimp [D]; linarith)
    _ = A * D * X ^ δ := by ring

/-- The cofactor lift with exponents: class energy `≤ K Z^g`, `g ≤ E - log_Z N(B)`. -/
theorem cofactor_energy_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency → ℝ) (Z M E K : ℝ),
      1 < Z → 0 ≤ M → 0 ≤ K → (∀ h ∈ R, rawFrequencyNorm h ≤ Z ^ M) →
      (∀ B : NZIdeal, (sixthFreeFiber R B).Nonempty → ∃ g : ℝ,
        g ≤ E - Real.logb Z (B.val.absNorm : ℝ) ∧
        (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤ K * Z ^ g) →
      (∑ h ∈ R, f h) ≤ K * D * Z ^ (E + δ * M) := by
  obtain ⟨D, hD, hlift⟩ := cofactor_sum_le δ hδ
  refine ⟨D, hD, ?_⟩
  intro R f Z M E K hZ hM hK hR hB
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hX : 1 ≤ Z ^ M := Real.one_le_rpow hZ.le hM
  have h := hlift R f (Z ^ M) (K * Z ^ E) hX (by positivity) hR (fun B hne => by
    obtain ⟨g, hg, hs⟩ := hB B hne
    have hN0 : 0 < (B.val.absNorm : ℝ) := by
      have hp : 0 < B.val.absNorm :=
        Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
      exact_mod_cast hp
    refine hs.trans ?_
    have he : Z ^ (E - Real.logb Z (B.val.absNorm : ℝ)) =
        Z ^ E * (B.val.absNorm : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_sub hZ0, Real.rpow_logb hZ0 hZ.ne' hN0, Real.rpow_neg_one, div_eq_mul_inv]
    calc K * Z ^ g ≤ K * Z ^ (E - Real.logb Z (B.val.absNorm : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hg) hK
      _ = K * Z ^ E * (B.val.absNorm : ℝ) ^ (-1 : ℝ) := by rw [he]; ring)
  have he : (Z ^ M) ^ δ = Z ^ (δ * M) := by rw [← Real.rpow_mul hZ0.le, mul_comm]
  rw [he] at h
  calc (∑ h ∈ R, f h) ≤ K * Z ^ E * D * Z ^ (δ * M) := h
    _ = K * D * Z ^ (E + δ * M) := by rw [Real.rpow_add hZ0]; ring

/-- The core width of a cofactor class: `Z^(d_B) = Z^M / N(B)⁶`. -/
def coreWidth (Z M : ℝ) (B : NZIdeal) : ℝ := M - 6 * Real.logb Z (B.val.absNorm : ℝ)

theorem coreWidth_le (Z M : ℝ) (hZ : 1 < Z) (B : NZIdeal) : coreWidth Z M B ≤ M := by
  have hn : 1 ≤ (B.val.absNorm : ℝ) := by
    have hp : 0 < B.val.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  have := Real.logb_nonneg hZ hn
  unfold coreWidth; linarith

/-- An occupied cofactor class has core width `≥ 0` (its cores have norm `≥ 1`). -/
theorem coreWidth_nonneg (R : Finset NonzeroFrequency) (Z M : ℝ) (hZ : 1 < Z)
    (hR : ∀ h ∈ R, rawFrequencyNorm h ≤ Z ^ M) (B : NZIdeal)
    (hB : (sixthFreeFiber R B).Nonempty) : 0 ≤ coreWidth Z M B := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  obtain ⟨u, hu⟩ := hB
  obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
  have hBr : B ∈ (sixthPairs R).image Prod.snd := Finset.mem_image.mpr ⟨p, hp, hpB⟩
  have h6 := cofactor_norm_le R (Z ^ M) hR B hBr
  have hN0 : 0 < (B.val.absNorm : ℝ) := by
    have hp : 0 < B.val.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  have hl := (Real.logb_le_logb hZ (by positivity) (Real.rpow_pos_of_pos hZ0 M)).mpr h6
  rw [Real.logb_rpow hZ0 hZ.ne', Real.logb_pow] at hl
  unfold coreWidth; push_cast at hl; linarith

/-- **HIGH energy over all nonzero frequencies** from the per-cofactor core energies. -/
theorem high_cofactor_energy (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a0 a1 k : ℝ), 0 ≤ k → k ≤ 3 / 4 →
      ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency → ℝ) (Z M P S K lam : ℝ),
      1 < Z → 0 ≤ M → 0 ≤ S → 0 ≤ K → (∀ h ∈ R, rawFrequencyNorm h ≤ Z ^ M) →
      (∀ B : NZIdeal, (sixthFreeFiber R B).Nonempty →
        (2 / 25 < coreWidth Z M B →
          (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤
            K * Z ^ (coreWidth Z M B + highPriceF a0 a1 k P S (coreWidth Z M B) + lam)) ∧
        (coreWidth Z M B ≤ 2 / 25 →
          (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤
            K * Z ^ (coreWidth Z M B + 3 / 4 * P + S + lam))) →
      (∑ h ∈ R, f h) ≤ K * D * Z ^ (M + highPriceF a0 a1 k P S M + lam + δ * M) := by
  obtain ⟨D, hD, hlift⟩ := cofactor_energy_le δ hδ
  refine ⟨D, hD, ?_⟩
  intro a0 a1 k hk0 hk1 R f Z M P S K lam hZ hM hS hK hR hB
  have h := hlift R f Z M (M + highPriceF a0 a1 k P S M + lam) K hZ hM hK hR (fun B hne => by
    have hd0 := coreWidth_nonneg R Z M hZ hR B hne
    have hdM := coreWidth_le Z M hZ B
    have hlog : Real.logb Z (B.val.absNorm : ℝ) = (M - coreWidth Z M B) / 6 := by
      unfold coreWidth; ring
    rcases lt_or_ge (2 / 25) (coreWidth Z M B) with hbig | htiny
    · refine ⟨_, ?_, (hB B hne).1 hbig⟩
      have := restored_price_le (a0 := a0) (a1 := a1) (P := P) hk0 hk1
        (show 0 < coreWidth Z M B by linarith) hdM hS
      rw [hlog]; linarith
    · refine ⟨_, ?_, (hB B hne).2 htiny⟩
      have := tiny_restored_le (a0 := a0) (a1 := a1) (k := k) (P := P) (S := S) (M := M) hd0 htiny
      rw [hlog]; linarith)
  simpa only [add_assoc] using h

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
