/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Smooth/CompactOrbitL2.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped Classical Topology ENNReal
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.CompactOrbitL2

variable {X : Type*} [MeasurableSpace X]

 def scalarL2 (μ : Measure X) : Submodule ℂ (X → ℂ) where
  carrier := {f | MemLp f 2 μ}
  zero_mem' := MemLp.zero
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c _ hf => hf.const_smul c

 theorem span_memLp {ι : Type*} (μ : Measure X) (o : ι → X → ℂ)
    (ho : ∀ i, MemLp (o i) 2 μ) :
    ∀ f ∈ Submodule.span ℂ (Set.range o), MemLp f 2 μ := by
  have hs : Submodule.span ℂ (Set.range o) ≤ scalarL2 μ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ho i
  exact fun f hf => hs hf

end DedekindZetaZeroFree.KPMsSameContinuationGreen.NativeBoundaryH1.CompactOrbitL2

end
