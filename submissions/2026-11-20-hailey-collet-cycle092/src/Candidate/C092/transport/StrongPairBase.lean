/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native independent-pair base: the genuine source on two duplicated whole-slot
subproducts, with a strict early rounding collar. -/
import Candidate.C092.transport.CofactorIndependentBridge

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.NativeStrip
open QRH.Cycle092.WholeSlot OAI.SevenEighths

/-- The two real native marked-fourth quotas. A positive common debit leaves
room for the whole-slot partition, while each source keeps its true cap. -/
theorem native_split_quotas {n y l : ℝ}
    (hy : sourceY ≤ y) (hy' : y ≤ sourceY/(H:ℝ))
    (hn : y ≤ n) (hr : n ≤ sourceRatio*y)
    (hl0 : 0 ≤ l) (hl : l < sourceWidth n y) :
    ∃ q₁ q₂ mesh : ℝ, 0 < mesh ∧
      0 ≤ q₁ ∧ q₁ < 3/20 ∧ q₁ < (1-2*n)/2 ∧
      0 ≤ q₂ ∧ q₂ < 3/20 ∧ q₂ < (1-2*y)/2 ∧
      n ≤ 1/2 ∧ y ≤ 1/2 ∧ l+mesh ≤ (q₁+q₂)/2 := by
  have hg := QRH.Cycle092Continuation.native_strip_gain hy hy'
  have hmean : l < (1-n-y)/2 := hl.trans (QRH.Cycle092Continuation.native_strip_width n hy hy')
  have hylo : (388/1000:ℝ) ≤ y := by norm_num [sourceY] at hy ⊢; linarith
  have hyhi : y ≤ (389/1000:ℝ) := by norm_num [sourceY,H,u] at hy'; linarith
  have hnhi : n ≤ (448/1000:ℝ) := by norm_num [sourceRatio] at hr; linarith
  let gap : ℝ := (1-n-y)/2-l
  let q₁ : ℝ := (1-2*n)/2-gap/2
  let q₂ : ℝ := (1-2*y)/2-gap/2
  refine ⟨q₁,q₂,gap/4,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals (try dsimp [q₁,q₂,gap])
  all_goals linarith

/-- A literal partition of all original slots. It uses only the fixed widths
and the early collar, before any ordinary row or ideal summation. -/
theorem partition_before_rows {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (w : Slot → ℝ) {l q₁ q₂ mesh : ℝ}
    (hm : 0 ≤ mesh) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsum : (∑ i, w i) ≤ l) (hbudget : l+mesh ≤ (q₁+q₂)/2) :
    ∃ F : Finset Slot, 2*(∑ i ∈ F,w i) ≤ q₁ ∧
      2*(∑ i ∈ Finset.univ\F,w i) ≤ q₂ := by
  obtain ⟨F,hF,hrest,_⟩ := select_before_rows w mesh (q₁/2) hw hwm hm (by linarith)
  refine ⟨F,by linarith,?_⟩
  have hh : max 0 ((∑ i,w i)-q₁/2+mesh) ≤ q₂/2 := by
    apply max_le <;> linarith
  linarith [hrest.trans hh]

/-- The same early partition on any live original subproduct. Inactive slots
are assigned width zero for the selection only; no native polynomial changes. -/
theorem partition_selected {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T : Finset Slot) (w : Slot → ℝ) {l q₁ q₂ mesh : ℝ}
    (hm : 0 ≤ mesh) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsum : (∑ i∈T, w i) ≤ l) (hbudget : l+mesh ≤ (q₁+q₂)/2) :
    ∃ F ⊆ T, 2*(∑ i∈F,w i) ≤ q₁ ∧ 2*(∑ i∈T\F,w i) ≤ q₂ := by
  let w' : Slot→ℝ := fun i=>if i∈T then w i else 0
  have hw' : ∀ i,0≤w' i := by
    intro i
    dsimp [w']
    split_ifs
    · exact hw i
    · exact le_rfl
  have hm' : ∀ i,w' i≤ mesh := by intro i; dsimp [w']; split_ifs <;> simp_all
  have hsum' : (∑ i,w' i)≤l := by
    simpa only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] using hsum
  obtain ⟨F,hF,hR⟩ := partition_before_rows w' hm hq₁ hq₂ hw' hm' hsum' hbudget
  refine ⟨F∩T,Finset.inter_subset_right,?_,?_⟩
  · have he : (∑ i∈F,w' i)=(∑ i∈F∩T,w i) := by
      simp only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter]
    simpa only [he] using hF
  · have he : (∑ i∈Finset.univ\F,w' i)=(∑ i∈T\(F∩T),w i) := by
      rw [show T\(F∩T)=(Finset.univ\F)∩T by ext i; simp; tauto]
      simp only [w',←Finset.sum_filter,Finset.filter_mem_eq_inter]
    simpa only [he] using hR

/-- These are actual native analytic suppliers, not a recurrence assumption.
Their source parameter is selected by the strict debit in native_mean_box;
the full live mark product is split between their duplicated fourths. -/
theorem native_split_sources
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y l : ℝ} (hy : sourceY ≤ y) (hy' : y ≤ sourceY/(H:ℝ))
    (hn : y ≤ n) (hr : n ≤ sourceRatio*y)
    (hl0 : 0 ≤ l) (hl : l < sourceWidth n y) :
    ∃ q₁ q₂ mesh : ℝ, 0 < mesh ∧
      UniformBox n n q₁ ∧ UniformBox y y q₂ ∧
      ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot] (w : Slot → ℝ),
      (∀ i, 0 ≤ w i) → (∀ i,w i ≤ mesh) → (∑ i,w i) ≤ l →
      ∃ F : Finset Slot, 2*(∑ i ∈ F,w i) ≤ q₁ ∧
        2*(∑ i ∈ Finset.univ\F,w i) ≤ q₂ := by
  obtain ⟨q₁,q₂,mesh,hm,hq₁,hcap₁,hmean₁,hq₂,hcap₂,hmean₂,hnhi,hyhi,hbudget⟩ :=
    native_split_quotas hy hy' hn hr hl0 hl
  refine ⟨q₁,q₂,mesh,hm,?_,?_,?_⟩
  · exact QRH.Cycle092.LowActual.native_mean_box hβ hnhi hnhi hq₁ hcap₁ (by linarith)
  · exact QRH.Cycle092.LowActual.native_mean_box hβ hyhi hyhi hq₂ hcap₂ (by linarith)
  · intro Slot _ _ w hw hwm hsum
    exact partition_before_rows w hm.le hq₁ hq₂ hw hwm hsum hbudget

#print axioms native_split_quotas
#print axioms native_split_sources
end
end QRH.Cycle092.StrongPair
