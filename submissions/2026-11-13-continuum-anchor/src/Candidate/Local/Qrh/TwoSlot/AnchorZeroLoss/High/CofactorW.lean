/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.BatchMax
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor.Lift

/-!
# High.CofactorW

`Cofactor.Lift.high_cofactor_energy` for the floored price `highPriceFW`:
per-cofactor core energies (large cores against `highPriceFW` at the core width, tiny cores
`≤ 2/25` against the tiny-core exponent `(3/4) P + S`) give the HIGH energy over all nonzero frequencies
`≤ K D Z^(M + highPriceFW(P,S,M) + λ + δM)`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
variable [shift : WitnessShift]
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open LocalMoment HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open Cofactor
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- **HIGH energy over all nonzero frequencies, floored price.** -/
theorem high_cofactor_energyW (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a0 a1 k wlo : ℝ), 0 ≤ k → k ≤ 3 / 4 →
      ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency → ℝ) (Z M P S K lam : ℝ),
      1 < Z → 0 ≤ M → 0 ≤ S → 0 ≤ K → (∀ h ∈ R, rawFrequencyNorm h ≤ Z ^ M) →
      (∀ B : NZIdeal, (sixthFreeFiber R B).Nonempty →
        (2 / 25 < coreWidth Z M B →
          (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤
            K * Z ^ (coreWidth Z M B + highPriceFW a0 a1 k wlo P S (coreWidth Z M B) + lam)) ∧
        (coreWidth Z M B ≤ 2 / 25 →
          (∑ u ∈ sixthFreeFiber R B, f (sixthFrequencyEquiv (u, B))) ≤
            K * Z ^ (coreWidth Z M B + 3 / 4 * P + S + lam))) →
      (∑ h ∈ R, f h) ≤ K * D * Z ^ (M + highPriceFW a0 a1 k wlo P S M + lam + δ * M) := by
  obtain ⟨D, hD, hlift⟩ := cofactor_energy_le δ hδ
  refine ⟨D, hD, ?_⟩
  intro a0 a1 k wlo hk0 hk1 R f Z M P S K lam hZ hM hS hK hR hB
  have h := hlift R f Z M (M + highPriceFW a0 a1 k wlo P S M + lam) K hZ hM hK hR (fun B hne => by
    have hd0 := coreWidth_nonneg R Z M hZ hR B hne
    have hdM := coreWidth_le Z M hZ B
    have hlog : Real.logb Z (B.val.absNorm : ℝ) = (M - coreWidth Z M B) / 6 := by
      unfold coreWidth; ring
    rcases lt_or_ge (2 / 25) (coreWidth Z M B) with hbig | htiny
    · refine ⟨_, ?_, (hB B hne).1 hbig⟩
      have := restored_price_leW (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) hk0 hk1
        (show 0 < coreWidth Z M B by linarith) hdM hS
      rw [hlog]; linarith
    · refine ⟨_, ?_, (hB B hne).2 htiny⟩
      have := tiny_restored_leW (a0 := a0) (a1 := a1) (k := k) (wlo := wlo) (P := P) (S := S)
        (M := M) htiny
      rw [hlog]; linarith)
  simpa only [add_assoc] using h

end
end Qrh.TwoSlot.AnchorZeroLoss.High
