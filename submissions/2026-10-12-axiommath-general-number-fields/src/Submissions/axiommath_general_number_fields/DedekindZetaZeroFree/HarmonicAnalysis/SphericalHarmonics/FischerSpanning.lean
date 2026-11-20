/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/SphericalHarmonics/FischerSpanning.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Analysis.HarmonicPolynomials.FiniteFischerDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
open KPCplxIntertwinerEigenvalues
open scoped BigOperators

theorem unit_radius_spanning (p : MvPolynomial (Fin 3) ℂ) :
    ∃ (I : Finset ℕ) (h : ℕ → MvPolynomial (Fin 3) ℂ),
      (∀ ℓ ∈ I, h ℓ ∈ harmonicPolynomials ℓ) ∧
      ∀ x : Fin 3 → ℝ, (∑ i : Fin 3, x i ^ 2) = 1 →
        MvPolynomial.eval (fun i => (x i : ℂ)) p =
          ∑ ℓ ∈ I, MvPolynomial.eval (fun i => (x i : ℂ)) (h ℓ) := by
  classical
  have H (d : ℕ) := homogeneous_fischer (MvPolynomial.homogeneousComponent_mem d p)
  choose h hh he using H
  let S : Finset (Σ _ : ℕ, ℕ) := (Finset.range (p.totalDegree + 1)).sigma
    (fun d => Finset.range (d / 2 + 1))
  let degree : (Σ _ : ℕ, ℕ) → ℕ := fun a => a.1 - 2 * a.2
  let I := S.image degree
  let q : ℕ → MvPolynomial (Fin 3) ℂ := fun ℓ =>
    ∑ a ∈ S with degree a = ℓ, h a.1 a.2
  refine ⟨I, q, ?_, ?_⟩
  · intro ℓ hℓ
    apply (harmonicPolynomials ℓ).sum_mem
    intro a ha
    obtain ⟨ha, hdeg⟩ := Finset.mem_filter.mp ha
    obtain ⟨hd, hk⟩ := Finset.mem_sigma.mp ha
    have hk' : a.2 ≤ a.1 / 2 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hh' := hh a.1 a.2 hk'
    simpa only [degree, hdeg] using hh'
  · intro x hx
    have hr : MvPolynomial.eval (fun i => (x i : ℂ)) radiusQuadratic = 1 := by
      simp only [radiusQuadratic, map_sum, map_pow, MvPolynomial.eval_X]
      exact_mod_cast hx
    have hs : MvPolynomial.eval (fun i => (x i : ℂ)) p =
        ∑ a ∈ S, MvPolynomial.eval (fun i => (x i : ℂ)) (h a.1 a.2) := by
      rw [← MvPolynomial.sum_homogeneousComponent p, map_sum]
      simp_rw [he, map_sum, map_mul, map_pow, hr, one_pow, one_mul]
      exact Finset.sum_sigma' _ _ _
    rw [hs]
    simp only [q, map_sum]
    exact (Finset.sum_fiberwise_of_maps_to (s := S) (t := I) (g := degree)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (fun a => MvPolynomial.eval (fun i => (x i : ℂ)) (h a.1 a.2))).symm

end DedekindZetaZeroFree.ComplexFractionalInverse.FiniteFischerRaw
