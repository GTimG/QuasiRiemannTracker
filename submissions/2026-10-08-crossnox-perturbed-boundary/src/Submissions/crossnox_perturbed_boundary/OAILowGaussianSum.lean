/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowGaussianSum.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowGaussianCentral
import Submissions.crossnox_perturbed_boundary.OAILowGaussianRemote
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianSum

namespace OAI

noncomputable section

open scoped Classical ContDiff SchwartzMap

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

open CompletedGauss CanonicalQuadraticSieve

local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem perturbed_low_all_gaussian_dyads
    (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀ P ∈ S, P.IsMaximal) (hbad : fixedBadPrimes ⊆ S)
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (ht : 0 ≤ t) (htSmall : t ≤ 1 / 30)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (a b ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V : ℝ → ℂ))
    (W0 W1 : ℝ → ℂ) (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hab1 : a1 < b1) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀ x, ‖W0 x‖ ≤ B0)
    (hWB1 : ∀ x, ‖W1 x‖ ≤ B1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1 < Z ∧
      ∀ (T : Fin K → Finset PrimeIdeal),
        (∀ i P, P ∈ T i → Supported P.val) →
        (∀ i P, P ∈ T i → P.val ∉ S) →
        Pairwise (fun i j => Disjoint (T i) (T j)) →
        (∀ i P, P ∈ T i →
          a * Z ^ (ell i) ≤ (Ideal.absNorm P.val : ℝ) ∧
          (Ideal.absNorm P.val : ℝ) ≤ b * Z ^ (ell i)) →
      ∀ (J : Finset (Fin K))
        (W : Fin K → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
        let f := fun j : ℕ =>
          lowCommonDyad η (calibrationForSet S hS)
            W0 W1 (fun i => canonicalSlotSupport (T i))
            W (fun i => Z ^ (ell i)) J
            (Z ^ (xBase - t / 2))
            (Z ^ (yBase - t / 2)) ((2 : ℝ) ^ j)
            (Z ^ (1 + lowSelectedLength ell J)) V hV
        Summable f ∧
          ‖∑' j : ℕ, f j‖ ≤
            C * Z ^ (lowBase - t / 4 + 256 * ε) := by
  obtain ⟨Cc, hCc, hcentral⟩ :=
    perturbed_low_central_gaussian_dyads η S hS hbad
      ell hell t ht htSmall hsum a b ε ha hε hε1
      V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1
      hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr, hCr, hremote⟩ :=
    perturbed_low_remote_gaussian_dyads S hS
      ell hell t ht htSmall hsum b ε hε V hV
      W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
      hW0 hW1 hWB0 hWB1
  refine ⟨Cc + Cr, add_pos hCc hCr, ?_⟩
  filter_upwards [hcentral, hremote] with Z hc hr
  refine ⟨hc.1, ?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT
    (fun i P hP => (hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _
    (fun j => lowRemote Z (lowSelectedLength ell J) ε ((2 : ℝ) ^ j))
    hc'.1 hr'.1
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hp : Z ^ (-1 : ℝ) ≤
      Z ^ (lowBase - t / 4 + 256 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hc.1.le (by
      have hbase : 0 ≤ lowBase := by norm_num [lowBase, skew]
      linarith)
  calc
    _ ≤ Cc * Z ^ (lowBase - t / 4 + 256 * ε) +
        Cr * Z ^ (-1 : ℝ) := add_le_add hc'.2 hr'.2
    _ ≤ Cc * Z ^ (lowBase - t / 4 + 256 * ε) +
        Cr * Z ^ (lowBase - t / 4 + 256 * ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _ = _ := by ring

end SevenEighths.ProbePhysical

end

end OAI
