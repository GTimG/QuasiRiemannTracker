/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Quotients/MultiplicativeBalancedTilingAndIntegration.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Ideals.AllowedGenerators
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.SixthPowerCompactCover
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.MeasureTheory.BorelCocompactTransversals
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Lattices.SixthPowerUnitDiscreteness

@[expose] public section

open MeasureTheory
open scoped nonZeroDivisors ENNReal

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

local instance : MeasurableSpace A.G1 := borel _
local instance : BorelSpace A.G1 := ⟨rfl⟩

theorem exists_multiplicative_quotient_balanced_tiling :
    ∃ (K_bal D : Set A.G1), IsCompact K_bal ∧
      (∀ y : A.G1, ∃ γ : A.Gamma1, (γ : A.G1) * y ∈ K_bal) ∧
      MeasurableSet D ∧ IsCompact (closure D) ∧ D ⊆ K_bal ∧
      (∀ y : A.G1, ∃! γ : A.Gamma1, (γ : A.G1) * y ∈ D) := by
  obtain ⟨n, V, hV, hcover⟩ :=
    exists_finite_relativelyCompact_quotient_slices (G := A.G1) A.Gamma1
  obtain ⟨D, hDmeas, hDcomp, htiling⟩ :=
    exists_measurable_relativelyCompact_exact_transversal_of_finite_slices
      A.G1 A.Gamma1 n V (fun i => (hV i).1) (fun i => (hV i).2.1)
      (fun i => (hV i).2.2) hcover
  refine ⟨closure D, D, hDcomp, ?_, hDmeas, hDcomp, subset_closure, htiling⟩
  intro y
  obtain ⟨γ, hγ, _⟩ := htiling y
  exact ⟨γ, subset_closure hγ⟩

end
end SArithmeticData
end DedekindZetaZeroFree
