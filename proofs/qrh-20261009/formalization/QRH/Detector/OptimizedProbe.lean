import QRH.Geometry
import OAI.NumberTheory.DirichletL.Detector.CanonicalPhysicalRows
import OAI.NumberTheory.DirichletL.Detector.GaussianCommon

/-! The optimized physical probe uses the original Gauss sums, calibration,
actual characters and compensated tuple operation at the exact manuscript scales.
The row-triple identity below is an equality, not an asserted analytic bound. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.QRHOptimizedProbe
open ProbePhysical HeckeInverseAmplification CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def optimizedProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ → ℂ) (slots : Fin K → Finset O)
    (W : Fin K → ℝ → ℂ) (lengths : Fin K → ℝ) (Z : ℝ) : ℂ :=
  compensatedPhysicalProbe η C W0 W1 slots W (fun i => Z ^ lengths i)
    (Z ^ QRH.lx) (Z ^ QRH.ly) Z

theorem optimized_product_scale {K : ℕ} (lengths : Fin K → ℝ) (Z : ℝ)
    (hZ : 0 < Z) (hsum : (∑ i, lengths i) = QRH.ell) :
    (Z ^ QRH.lx * Z ^ QRH.ly) * (∏ i, Z ^ lengths i) = Z := by
  rw [← Real.rpow_add hZ, ← Real.rpow_sum_of_pos hZ, ← Real.rpow_add hZ, hsum]
  have hid : QRH.lx + QRH.ly + QRH.ell = 1 := by
    dsimp [QRH.lx, QRH.ly, QRH.M]
    ring
  rw [hid, Real.rpow_one]

theorem optimized_row_triples {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal) (hpS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (slots : Fin K → Finset O) (hp : ∀ i a, a ∈ slots i → a ≠ 0)
    (W : Fin K → ℝ → ℂ) (lengths : Fin K → ℝ) (Z : ℝ) (hZ : 0 < Z) :
    optimizedProbe η (calibrationForSet S hS) W0 W1 slots W lengths Z =
      ∑ p : ((i : Fin K) → {a : O // a ∈ slots i}),
        (∏ i, W i (elementNorm (p i).val / Z ^ lengths i)) *
        compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1
          (fun i => (p i).val) (Z ^ QRH.lx) (Z ^ QRH.ly) Z := by
  exact compensatedPhysicalProbe_eq_row_triples η S hS hpS hbad hSne W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 slots hp W (fun i => Z ^ lengths i)
    (Z ^ QRH.lx) (Z ^ QRH.ly) Z (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ

theorem optimized_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀ P ∈ S, P.IsMaximal) (hpS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (hSne : S.Nonempty)
    (T : Fin K → Finset PrimeIdeal) (hT : ∀ i P, P ∈ T i → Supported P.val)
    (W : Fin K → ℝ → ℂ) (lengths : Fin K → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1) (Z : ℝ) (hZ : 0 < Z) :
    optimizedProbe η (calibrationForSet S hS) W0 W1
      (fun i => canonicalSlotSupport (T i)) W lengths Z =
      ∑' u : FreeRow, ∑ P : (∀ i, ↥(T i)),
        (∏ i, W i ((Ideal.absNorm (P i).val.val : ℝ) / Z ^ lengths i)) *
        rowIntegral η S (calibrationForSet S hS) (fun i => primaryGenerator (P i).val.val)
          W0 W1 (Z ^ QRH.lx) (Z ^ QRH.ly) Z u := by
  exact compensatedPhysicalProbe_eq_canonical_rows η S hS hpS hbad hSne T hT W
    (fun i => Z ^ lengths i) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z ^ QRH.lx) (Z ^ QRH.ly) Z (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ

end SevenEighths.QRHOptimizedProbe
end
end OAI
