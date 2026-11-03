/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowGaussianDyad.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowCentralTuple
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad

namespace OAI

noncomputable section

open scoped Classical ContDiff SchwartzMap

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

open CompletedGauss CanonicalQuadraticSieve RayFourExpansion

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_central_gaussian_dyad
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (ht : 0 ≤ t) (htSmall : t ≤ 1 / 30)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 M : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hM : 0 ≤ M)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWM : ∀ x, ‖W1 x‖ ≤ M) :
    ∃ degree : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i →
          a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧
          (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K)) (U : ℝ), 0 < U →
        Z ^ (1 + lowSelectedLength ell J - ε / 2) ≤ U →
        U ≤ Z ^ (1 + lowSelectedLength ell J + ε / 2) →
      ∀ (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (V : SchwartzMap ℝ ℂ)
        (hV : HasCompactSupport (V : ℝ → ℂ)),
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1
          (fun i => canonicalSlotSupport (T i))
          W (fun i => Z ^ (ell i)) J
          (Z ^ (xBase - t / 2))
          (Z ^ (yBase - t / 2)) U
          (Z ^ (1 + lowSelectedLength ell J)) V hV‖ ≤
          C * Z ^ (lowBase - t / 4 + 254 * ε) *
            gaussianJointMoment V hV degree
              (U / Z ^ (1 + lowSelectedLength ell J)) := by
  obtain ⟨degree, C, hC, he⟩ :=
    perturbed_low_central_compensated_tuple η S hS hbad
      ell hell t ht htSmall hsum a b ε ha hε hε1
      W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM
      hW0 hW1 hW0s hW1s hWM
  refine ⟨degree, C, hC, ?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro θ
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW θ

end SevenEighths.ProbePhysical

end

end OAI
