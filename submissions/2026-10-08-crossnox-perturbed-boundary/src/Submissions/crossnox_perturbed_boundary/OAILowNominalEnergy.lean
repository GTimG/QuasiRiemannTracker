/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowNominalEnergy.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowSelectedBound
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalEnergy

namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.ProbePhysical

open CompletedGauss CanonicalQuadraticSieve RayFourExpansion

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_selected_nominal_energy
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (ht : 0 ≤ t) (htSmall : t ≤ 1 / 6)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (Ck b ε : ℝ) (hCk : 0 < Ck) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i → (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K)) (R : Finset O),
        (∀ z ∈ R, z ≠ 0 ∧
          elementNorm z ≤ Ck * Z ^ (5 / 6 - t - 2 * lowUnselectedLength ell J)) →
      ∀ X : ℝ, 0 < X →
        Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ X →
        X ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
      ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (Y : Fin K → ℝ) (θ : ℝ) (σ : RayRing),
        (∑ z ∈ R,
          ‖lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η (fun i => canonicalSlotSupport (T i)) J W Y θ)
            η S hS (lowSelectedIdeal (fun i => canonicalSlotSupport (T i)) J)
            X θ σ z‖ ^ 2) ≤
          C * (1 + ‖θ‖) ^ degree *
            Z ^ ((5 / 6 - t - 2 * lowUnselectedLength ell J) +
              max 0 ((lowUnselectedLength ell J - 1 / 6 + 5 * t) / 4) +
              507 * ε) := by
  obtain ⟨degree, C, Z₀, hC, hZ₀, he⟩ :=
    perturbed_low_selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  refine ⟨degree, C, hC, ?_⟩
  filter_upwards [eventually_low_selected_caps ell hell b ε hε,
    Filter.eventually_ge_atTop Z₀] with Z hc hZ
  refine ⟨hc.1, ?_⟩
  intro T hT hout hdis hnorm J R hR X hX hXlo hXhi W hW Y θ σ
  have hd : 0 ≤ lowUnselectedLength ell J :=
    Finset.sum_nonneg (fun i _ => hell i)
  have hs : 0 ≤ lowSelectedLength ell J :=
    Finset.sum_nonneg (fun i _ => hell i.val)
  have hlength := lowLength_sum ell J
  have hd1 : lowUnselectedLength ell J ≤ 1 / 6 + t := by linarith
  have hscap : lowSelectedLength ell J ≤
      1 / 6 + t - lowUnselectedLength ell J := by linarith
  have hscale := lowCentralShift_scale Z X
    (lowSelectedLength ell J + ε / 2) hc.1 hX
  rw [← hscale]
  apply he Z t (lowUnselectedLength ell J)
    (lowSelectedLength ell J + ε / 2)
    (lowCentralShift Z X (lowSelectedLength ell J + ε / 2))
    hZ ht htSmall hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) ε
      hc.1 hX hε.le hXlo hXhi)
    R hR T hT hout hdis J
    (fun i => max 1 (b * Z ^ (ell i.val)))
    (fun i => le_max_left _ _)
    (fun i P hP => (hnorm i.val P hP).trans (le_max_right _ _))
    (hc.2 J) W hW Y θ σ

end SevenEighths.ProbePhysical

end

end OAI
