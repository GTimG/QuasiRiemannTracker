/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CopyWord
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ResponseExtraction
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FiniteSelection

/-! A rowwise extracted repeated word is chosen from ONE fixed finite
copied slot type. Every analytic moment is first applied to a fixed word;
only then is the finite multiplicity partition summed. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification

/-- The actual original responses give a source-admissible copied slot
subcollection on each row, at any requested bounded capacity. -/
theorem response_subcollections {Label Slot : Type} [DecidableEq Slot]
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {U Aroot : ℝ}
    (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot)
    (error : Slot→ℝ) (δ β smin loss mesh target zmax : ℝ) (K : ℕ)
    (hU : 1<U) (hwm : ∀s∈B.slots,B.widths s≤mesh)
    (herr : ∀s∈B.slots,0≤error s) (hδ : 0≤δ) (hβ : 0<β) (hsmin : 0<smin)
    (hs : smin≤∑ s∈B.slots,B.widths s)
    (hupper : ∀u∈B.rows,∀s∈B.slots,‖B.Q u s‖^2≤U^(B.widths s+error s))
    (herrors : (∑s∈B.slots,error s)≤loss)
    (hlower : ∀u∈B.rows,U^((δ+β)*(∑s∈B.slots,B.widths s)-loss)≤∏s∈B.slots,‖B.Q u s‖^2)
    (hbudget : 4*loss≤β*smin) (hm : 0≤mesh) (ht : 0≤target) (hmax : target≤zmax)
    (hK : zmax/(β*smin/2)+1≤(K:ℝ)) :
    ∀u∈B.rows,∃selected : Finset (Slot×Fin K),selected⊆(B.copy K).slots ∧
      target-mesh≤∑s∈selected,(B.copy K).widths s ∧
      (∑s∈selected,(B.copy K).widths s)≤target ∧
      U^(δ*(target-mesh))≤‖∏s∈selected,(B.copy K).Q u s‖^2 := by
  intro u hu
  obtain ⟨good,n,R,hg,hR,hn,hlo,hhi,hresp⟩ := bounded_response_word B.slots (B.Q u)
    B.widths error U δ β smin loss mesh target zmax K hU B.widthsNonneg hwm herr hδ hβ
    hsmin hs (hupper u hu) herrors (hlower u hu) hbudget hm ht hmax hK
  let hn' : n<K := Nat.lt_of_succ_le hn
  refine ⟨copyWord good R n K hn',copyWord_subset B.slots good R hg hR n K hn',?_,?_,?_⟩
  · change target-mesh≤∑s∈copyWord good R n K hn',B.widths s.1
    rwa [copyWord_sum]
  · change (∑s∈copyWord good R n K hn',B.widths s.1)≤target
    rwa [copyWord_sum]
  · change U^(δ*(target-mesh))≤‖∏s∈copyWord good R n K hn',B.Q u s.1‖^2
    rwa [copyWord_prod]

/-- All Sobolev tests share the same extracted word. The finite partition
is paid after each fixed word has received its genuine analytic estimate. -/
theorem chosen_subcollection_moments {Row Slot Index : Type*}
    [Fintype Slot] [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (w : Slot→ℝ) (q : Row→Slot→ℂ)
    (U response target : ℝ) (D : Index→Row→ℂ) (bound : Index→ℝ)
    (hbound : ∀ i,0≤bound i)
    (hselect : ∀u∈rows,∃T : Finset Slot,T⊆slots ∧ (∑s∈T,w s)≤target ∧
      U^response≤‖∏s∈T,q u s‖^2)
    (hmoment : ∀ i,∀T : Finset Slot,T⊆slots → (∑s∈T,w s)≤target →
      (∑u∈rows,‖D i u*(∏s∈T,q u s)‖^2)≤bound i) :
    ∃Q : Row→ℂ,(∀u∈rows,U^response≤‖Q u‖^2) ∧
      ∀i,(∑u∈rows,‖D i u*Q u‖^2)≤(Fintype.card (Finset Slot):ℝ)*bound i := by
  classical
  have hex (u : Row) : ∃T : Finset Slot,u∈rows → T⊆slots ∧ (∑s∈T,w s)≤target ∧
      U^response≤‖∏s∈T,q u s‖^2 := by
    by_cases hu : u∈rows
    · obtain ⟨T,hT,hwidth,hresp⟩ := hselect u hu
      exact ⟨T,fun _ => ⟨hT,hwidth,hresp⟩⟩
    · exact ⟨∅,fun hh => (hu hh).elim⟩
  choose select hselect using hex
  let Q := fun u => ∏s∈select u,q u s
  refine ⟨Q,fun u hu => (hselect u hu).2.2,?_⟩
  intro i
  let F := fun (T : Finset Slot) u => if T⊆slots ∧ (∑s∈T,w s)≤target
    then D i u*(∏s∈T,q u s) else 0
  have hfixed (T : Finset Slot) : (∑u∈rows,‖F T u‖^2)≤bound i := by
    by_cases hT : T⊆slots ∧ (∑s∈T,w s)≤target
    · simpa only [F,if_pos hT] using hmoment i T hT.1 hT.2
    · simpa only [F,if_neg hT,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero] using hbound i
  have he := rowwise_selection_energy rows F select (bound i) hfixed
  convert he using 1
  apply Finset.sum_congr rfl
  intro u hu
  dsimp [F,Q]
  rw [if_pos ⟨(hselect u hu).1,(hselect u hu).2.1⟩]

end
end Qrh.JointDetector.RepeatedMarks
