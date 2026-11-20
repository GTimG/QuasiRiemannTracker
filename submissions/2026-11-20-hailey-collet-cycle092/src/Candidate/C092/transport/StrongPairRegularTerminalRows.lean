/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact retained-row response partitions, with fixed-cell medium windows. -/
import Candidate.C092.transport.StrongPairRegularTerminalDispatch
import Candidate.C092.transport.StrongPairRegularTerminalFibers

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source

/-- The three actual measured-response classes cover every original row
once. Low is cut at the checked fixed threshold, not at a grid endpoint. -/
theorem terminal_response_partition {Row : Type*} [Fintype Row]
    (response value : Row→ℝ) {threshold upper : ℝ} (h : threshold ≤ upper) :
    (∑ u,value u) =
      (∑ u∈Finset.univ.filter (fun u=>response u ≤ threshold),value u)+
      (∑ u∈Finset.univ.filter (fun u=>upper < response u),value u)+
      (∑ u∈Finset.univ.filter (fun u=>threshold < response u ∧ response u ≤ upper),value u) := by
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hl : response u ≤ threshold
  · have hh : ¬upper < response u := not_lt.mpr (hl.trans h)
    simp only [hl,hh,not_lt.mpr hl,false_and,ite_true,ite_false,add_zero]
  · by_cases hh : upper < response u
    · have hm : ¬(threshold < response u ∧ response u ≤ upper) := fun hm=>not_le.mpr hh hm.2
      simp only [hl,hh,hm,ite_false,ite_true,zero_add,add_zero]
    · have hm : threshold < response u ∧ response u ≤ upper := ⟨lt_of_not_ge hl,le_of_not_gt hh⟩
      simp [hl,hh,hm,not_le.mp hl,not_lt.mp hh]

/-- Finite windows are selected from the fixed early table using only the
real measured response and zero band. Every original row has exactly one
selected key; weights remain arbitrary and the actual row values unchanged. -/
theorem terminal_medium_window_partition {Row : Type*} [Fintype Row]
    {Je Jν : ℕ} (egrid : Fin Je→ℝ) (νgrid : Fin Jν→ℝ)
    (response band value : Row→ℝ) {step : ℝ}
    (hcover : ∀ u,∃ ie iv,egrid ie ≤ response u ∧ response u < egrid ie+step ∧
      max (egrid ie) (νgrid iv) ≤ band u ∧ band u < max (egrid ie) (νgrid iv)+step) :
    ∃ key : Row→Fin Je×Fin Jν,
      (∀ u,egrid (key u).1 ≤ response u ∧ response u < egrid (key u).1+step ∧
        max (egrid (key u).1) (νgrid (key u).2) ≤ band u ∧
        band u < max (egrid (key u).1) (νgrid (key u).2)+step) ∧
      (∑ u,value u)=∑ k : Fin Je×Fin Jν,
        ∑ u∈Finset.univ.filter (fun u=>key u=k),value u := by
  choose ie iv h using hcover
  exact ⟨fun u=>(ie u,iv u),h,terminal_sum_fibers _ value⟩

/-- Overlapping literal attaining-slot subclasses may be summed with their
true finite factor; no row cardinality bound is introduced. -/
theorem terminal_attaining_sum {Row Slot : Type*} [Fintype Row] [Fintype Slot]
    (classes : Slot→Finset Row) (value : Row→ℝ)
    (hvalue : ∀ u,0 ≤ value u) (hcover : ∀ u,∃ j,u∈classes j) :
    (∑ u,value u) ≤ ∑ j : Slot,∑ u∈classes j,value u := by
  calc
    _ ≤ ∑ u,∑ j : Slot,if u∈classes j then value u else 0 := by
      apply Finset.sum_le_sum
      intro u _
      obtain ⟨j,hj⟩ := hcover u
      have h := Finset.single_le_sum
        (s:=Finset.univ) (f:=fun k : Slot=>if u∈classes k then value u else 0)
        (fun k _=>by split_ifs; exact hvalue u; norm_num) (Finset.mem_univ j)
      simpa only [if_pos hj] using h
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp

#print axioms terminal_response_partition
#print axioms terminal_medium_window_partition
#print axioms terminal_attaining_sum
end
end QRH.Cycle092.StrongPair
