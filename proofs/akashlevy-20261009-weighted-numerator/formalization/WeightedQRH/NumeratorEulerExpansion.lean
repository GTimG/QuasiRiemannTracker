import WeightedQRH.NumeratorUnramifiedMass
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Absolutely convergent expansion of a product of local polynomials.  Indexing
by finite prime subsets and their degree choices retains an explicit positive
scale for every term; regrouping equal ideals is unnecessary for Mellin inversion.
-/
noncomputable section
open scoped BigOperators NNReal
namespace WeightedQRH.Numerator

def EulerIndex (ι : Type*) (n : ℕ) := Σ s : Finset ι, (s → Fin n)

def eulerTerm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (e : EulerIndex ι n) : ℂ :=
  ∏ p : e.1, f p.val (e.2 p)

def localMass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (p : ι) : ℝ :=
  ∑ j, ‖f p j‖

theorem euler_fiber_mass {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, ‖eulerTerm f ⟨s, j⟩‖) = ∏ p ∈ s, localMass f p := by
  classical
  simp only [tsum_fintype, eulerTerm, norm_prod, localMass]
  exact (Fintype.prod_sum (fun p : s => fun j : Fin n => ‖f p.val j‖)).symm.trans
    (Finset.prod_coe_sort s (fun p => ∑ j, ‖f p j‖))

/-- Absolute convergence is obtained from summable local coefficient masses. -/
theorem euler_expansion_summable_norm {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) : Summable (fun e : EulerIndex ι n => ‖eulerTerm f e‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro s
    exact (hasSum_fintype _).summable
  · simpa only [euler_fiber_mass, localMass] using
      summable_finsetProd_of_summable_nonneg
        (fun p => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hf

theorem euler_fiber_sum {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ) (s : Finset ι) :
    (∑' j : s → Fin n, eulerTerm f ⟨s, j⟩) = ∏ p ∈ s, ∑ j, f p j := by
  classical
  simp only [tsum_fintype, eulerTerm]
  rw [← Fintype.prod_sum]
  exact Finset.prod_coe_sort s (fun p => ∑ j, f p j)

/-- Exact product expansion, with no change to the original local factors. -/
theorem euler_expansion_hasProd {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    HasProd (fun p => 1 + ∑ j, f p j) (∑' e : EulerIndex ι n, eulerTerm f e) := by
  have hs := (euler_expansion_summable_norm f hf).of_norm
  have hsum := hs.hasSum.sigma (fun s => (hs.sigma_factor s).hasSum)
  simp only [euler_fiber_sum] at hsum
  exact hasProd_one_add_of_hasSum_prod hsum

theorem euler_expansion_eq_tprod {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∏' p, (1 + ∑ j, f p j)) = ∑' e : EulerIndex ι n, eulerTerm f e :=
  (euler_expansion_hasProd f hf).tprod_eq

theorem euler_expansion_mass_le_exp {ι : Type*} {n : ℕ} (f : ι → Fin n → ℂ)
    (hf : Summable (localMass f)) :
    (∑' e : EulerIndex ι n, ‖eulerTerm f e‖) ≤ Real.exp (∑' p, localMass f p) := by
  classical
  have hnonneg (p : ι) : 0 ≤ localMass f p :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hs := euler_expansion_summable_norm f hf
  change (∑' e : (Σ s : Finset ι, s → Fin n), ‖eulerTerm f e‖) ≤ _
  rw [hs.tsum_sigma]
  simp only [euler_fiber_mass]
  apply (summable_finsetProd_of_summable_nonneg hnonneg hf).tsum_le_of_sum_le
  intro T
  calc
    (∑ s ∈ T, ∏ p ∈ s, localMass f p) ≤
        ∑ s ∈ (T.biUnion id).powerset, ∏ p ∈ s, localMass f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hs)
      · intro s hs hst
        exact Finset.prod_nonneg (fun p _ => hnonneg p)
    _ = ∏ p ∈ T.biUnion id, (1 + localMass f p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p ∈ T.biUnion id, localMass f p) :=
      Real.prod_one_add_le_exp_sum _ hnonneg
    _ ≤ _ := Real.exp_le_exp.mpr (hf.sum_le_tsum _ (fun _ _ => hnonneg _))

def positiveCpowHom (w : ℂ) : ℝ≥0 →* ℂ where
  toFun q := (q : ℂ) ^ w
  map_one' := by simp
  map_mul' q r := by
    convert! Complex.mul_cpow_ofReal_nonneg q.property r.property w using 1
    simp only [NNReal.coe_mul, Complex.ofReal_mul]
    rfl

def eulerScale {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0) (e : EulerIndex ι n) : ℝ≥0 :=
  ∏ p : e.1, Q p.val ^ (e.2 p).val

def eulerCoefficient {ι : Type*} {n : ℕ} (c : ι → Fin n → ℂ)
    (e : EulerIndex ι n) : ℂ := ∏ p : e.1, c p.val (e.2 p)

def localMellinTerm {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (p : ι) (j : Fin n) : ℂ :=
  c p j * ((Q p : ℂ) ^ (-w)) ^ j.val

theorem eulerTerm_mellin {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (c : ι → Fin n → ℂ) (w : ℂ) (e : EulerIndex ι n) :
    eulerTerm (localMellinTerm Q c w) e =
      eulerCoefficient c e * (eulerScale Q e : ℂ) ^ (-w) := by
  classical
  unfold eulerTerm localMellinTerm eulerCoefficient eulerScale
  rw [Finset.prod_mul_distrib]
  congr 1
  have he := map_prod (positiveCpowHom (-w)) (fun p : e.1 => Q p.val ^ (e.2 p).val)
    Finset.univ
  simp only [map_pow, positiveCpowHom, MonoidHom.coe_mk, OneHom.coe_mk] at he
  exact he.symm

theorem eulerScale_one_le {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (e : EulerIndex ι n) : 1 ≤ eulerScale Q e := by
  apply Finset.one_le_prod
  intro p hp
  exact one_le_pow₀ (hQ p.val)

theorem euler_coefficient_weight_eq {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ) (e : EulerIndex ι n) :
    ‖eulerTerm (localMellinTerm Q c (sigma : ℂ)) e‖ =
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma) := by
  rw [eulerTerm_mellin, norm_mul]
  have hpos : 0 < (eulerScale Q e : ℝ) := by
    have h := eulerScale_one_le Q hQ e
    exact lt_of_lt_of_le zero_lt_one h
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.neg_re, Complex.ofReal_re]

theorem euler_coefficients_summable_weight {ι : Type*} {n : ℕ} (Q : ι → ℝ≥0)
    (hQ : ∀ p, 1 ≤ Q p) (c : ι → Fin n → ℂ) (sigma : ℝ)
    (hf : Summable (localMass (localMellinTerm Q c (sigma : ℂ)))) :
    Summable (fun e : EulerIndex ι n =>
      ‖eulerCoefficient c e‖ * (eulerScale Q e : ℝ) ^ (-sigma)) := by
  simpa only [euler_coefficient_weight_eq Q hQ c sigma] using
    euler_expansion_summable_norm (localMellinTerm Q c (sigma : ℂ)) hf

end WeightedQRH.Numerator
