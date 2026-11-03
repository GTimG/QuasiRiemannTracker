/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/MeasureTheory/Quotients/FiberInvariantSections.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

open Topology Set MeasureTheory

theorem continuousOn_section_of_fiber_invariance
    {E X Z : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Z] {q : E → X} {S : Set E} {f : E → Z} {s : X → E}
    (hq : Continuous q) (hqo : IsOpenMap q) (hS : IsOpen S)
    (hs : ∀ x ∈ q '' S, s x ∈ S ∧ q (s x) = x)
    (hf : ContinuousOn f S)
    (hfi : ∀ a ∈ S, ∀ b ∈ S, q a = q b → f a = f b) :
    ContinuousOn (f ∘ s) (q '' S) := by
  let qr : S → q '' S := fun a => ⟨q a, mem_image_of_mem q a.property⟩
  have hqc : Continuous qr := (hq.comp continuous_subtype_val).subtype_mk _
  have hqro : IsOpenMap qr := (hqo.restrict hS).codRestrict _
  have hqrs : Function.Surjective qr := by
    rintro ⟨x, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  rw [continuousOn_iff_continuous_restrict]
  apply (hqro.isQuotientMap hqc hqrs).continuous_iff.mpr
  have he : ((q '' S).domRestrict (f ∘ s)) ∘ qr = S.domRestrict f := by
    funext a
    exact hfi _ (hs (q a) (mem_image_of_mem q a.property)).1 _ a.property
      (hs (q a) (mem_image_of_mem q a.property)).2
  rw [he]
  exact continuousOn_iff_continuous_restrict.mp hf

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
