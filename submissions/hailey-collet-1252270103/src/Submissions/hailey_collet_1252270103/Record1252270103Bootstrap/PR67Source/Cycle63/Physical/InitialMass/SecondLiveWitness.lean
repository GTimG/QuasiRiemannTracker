import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRows
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap

/-- Nonvanishing of the original full block supplies a live row before any
ordinary/exceptional split or positive column majorant. -/
theorem actual_second_nonzero_live_row (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (hne : s.value W ≠ 0) : (secondLiveRows (fun _ : Unit => s)).Nonempty := by
  have hex := actual_second_batch_active_expression (fun _ : Unit => s)
    (fun _ => (1 : ℂ)) W
  simp only [Fintype.sum_unique, one_mul] at hex
  rw [hex] at hne
  obtain ⟨q,hq,_⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have h := (Finset.mem_filter.mp hq).2
  refine ⟨⟨q.1,q.2.2⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,h.2.1,h.2.2.2⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
