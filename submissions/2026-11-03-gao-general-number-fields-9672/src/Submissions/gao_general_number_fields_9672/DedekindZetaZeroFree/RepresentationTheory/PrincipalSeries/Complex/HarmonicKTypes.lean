/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/PrincipalSeries/Complex/HarmonicKTypes.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module
public import Mathlib.Algebra.MvPolynomial.PDeriv

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts MeasureTheory
open scoped BigOperators

noncomputable def compactSphereCoordinate (k : ComplexSU2) : Fin 3 → ℂ :=
  let m : Matrix (Fin 2) (Fin 2) ℂ := k
  ![(2 * (m 1 0 * star (m 1 1)).re : ℝ),
    (2 * (m 1 0 * star (m 1 1)).im : ℝ),
    (‖m 1 0‖ ^ 2 - ‖m 1 1‖ ^ 2 : ℝ)]

noncomputable def polynomialLaplacian :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, (MvPolynomial.pderiv i).toLinearMap.comp
    (MvPolynomial.pderiv i).toLinearMap

noncomputable def harmonicPolynomials (ℓ : ℕ) : Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℂ ℓ ⊓ polynomialLaplacian.ker

noncomputable def compactRestriction (s : ℝ) : PrincipalSeries s →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun f k := f (complexSU2Embedding k)
  map_add' f h := rfl
  map_smul' c f := rfl

noncomputable def polynomialCompactRestriction :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] (ComplexSU2 → ℂ) where
  toFun p k := MvPolynomial.eval (compactSphereCoordinate k) p
  map_add' p q := by ext k; simp
  map_smul' c p := by ext k; simp

noncomputable def harmonicKType (s : ℝ) (ℓ : ℕ) : Submodule ℂ (PrincipalSeries s) :=
  ((harmonicPolynomials ℓ).map polynomialCompactRestriction).comap (compactRestriction s)

def IsKInvariant (s : ℝ) (U : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∀ (k : compactSubgroup) (f : PrincipalSeries s), f ∈ U → pi s k f ∈ U

def KEquivalent (s : ℝ) (U V : Submodule ℂ (PrincipalSeries s)) : Prop :=
  ∃ e : U ≃ₗ[ℂ] V, ∀ (k : compactSubgroup) (u v : U),
    (v : PrincipalSeries s) = pi s k u →
      (e v : PrincipalSeries s) = pi s k (e u)

end DedekindZetaZeroFree.KPCplxHarmonicIntertwinerSpectrum
