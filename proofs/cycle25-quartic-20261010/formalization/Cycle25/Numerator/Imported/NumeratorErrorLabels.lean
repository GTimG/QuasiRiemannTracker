import Cycle25.Numerator.Imported.NumeratorErrorPrimeSum
import Cycle25.Numerator.Imported.NumeratorMassDamping
import Cycle25.Numerator.Imported.NumeratorPrimeSeparation

/-! Summing positive coefficient masses over all independent error-prime labels. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

theorem finite_label_damped_mass {ι : Type*} [Fintype ι] {α : ι → Type*}
    (A : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ) (hN : ∀ i e, 0 < N i e)
    (weight : ι → ℂ) (B : ι → ℝ) (L rho M : ℝ)
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) ≤ M*B i) :
    Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ∧
    (∑' e : Σ i, α i, ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) ≤
      M * ∑ i, ‖weight i‖*B i := by
  have he (i : ι) (e : α i) : ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho = ‖weight i‖ *
      (‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) * max 1 (L*N i e)^rho) := by
    rw [norm_mul]
    ring
  have hfs (i : ι) : Summable (fun e => ‖weight i*A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L*N i e)^rho) := by
    simp_rw [he]
    exact (hs i).mul_left _
  have hsum : Summable (fun e : Σ i, α i => ‖weight e.1 * A e.1 e.2‖ *
      (N e.1 e.2)^(-(1 / 2 : ℝ)) * max 1 (L*N e.1 e.2)^rho) := by
    apply (summable_sigma_of_nonneg (fun e => by have := hN e.1 e.2; positivity)).mpr
    exact ⟨hfs,(hasSum_fintype _).summable⟩
  refine ⟨hsum,?_⟩
  rw [hsum.tsum_sigma,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp_rw [he,tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left (hm i) (norm_nonneg _)).trans_eq (by ring)

theorem errorProductSize_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (P : ι → ProbePhysical.PrimeIdeal) (hP : Function.Injective P) :
    errorProductSize u (Finset.univ.image P) = ∏ i, 2880 * errorSize u (P i) := by
  unfold errorProductSize
  calc
    _ = ∏ Q ∈ Finset.univ.image P, 2880 * errorSize u Q :=
      Finset.prod_coe_sort _ _
    _ = _ := Finset.prod_image hP.injOn

theorem error_label_mass_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) =
      ∏ i, ∑ P : T i, 2880 * ‖weight i P‖ * errorSize u P.val := by
  calc
    _ = ∑ P : ∀ i, T i, ∏ i, 2880 * ‖weight i (P i)‖ * errorSize u (P i).val := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [norm_prod,errorProductSize_image u _ (hdis P),←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      ring
    _ = _ := (Fintype.prod_sum (fun i => fun P : T i =>
      2880 * ‖weight i P‖ * errorSize u P.val)).symm

theorem error_label_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : FreeRow) (T : ι → Finset ProbePhysical.PrimeIdeal)
    (hdis : ∀ P : ∀ i, T i, Function.Injective (fun i => (P i).val))
    (weight : ∀ i, T i → ℂ) (B : ι → ℝ)
    (hm : ∀ i, (∑ P : T i, ‖weight i P‖ * errorSize u P.val) ≤ B i) :
    (∑ P : ∀ i, T i, ‖∏ i, weight i (P i)‖ *
      errorProductSize u (Finset.univ.image (fun i => (P i).val))) ≤
      ∏ i, 2880 * B i := by
  rw [error_label_mass_factor u T hdis weight]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg (fun P hP => mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) (errorSize_nonneg u P.val))
  · intro i hi
    calc
      _ = 2880 * ∑ P : T i, ‖weight i P‖ * errorSize u P.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P hP
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm i) (by norm_num)

end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
