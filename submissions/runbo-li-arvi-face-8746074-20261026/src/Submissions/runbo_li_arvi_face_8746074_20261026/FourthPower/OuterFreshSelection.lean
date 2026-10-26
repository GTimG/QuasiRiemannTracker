/- Copyright (c) 2026 Sil. Apache-2.0.
The greedy block is an actual subset of the supplier's surviving slots.
Its logarithmic selected volume and the remaining width are exact, with
one upward mesh error for the whole block. No prime assignments enter the
choice, and no analytic estimate is assumed.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.GlobalSlotSelection
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshSource
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSelectedVolume
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshMixedCapacity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshSelection
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open MixedPrincipalPair MixedSupplierFourthRow MixedSupplierSource OuterFreshSource
open GlobalSlotSelection
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def liveWidth (L : Finset ι) (w : ι→ℝ) : ℝ := ∑i : {i // i∉Lᶜ},w i.val

def chosenSlots (L : Finset ι) (w : ι→ℝ) (rho mesh : ℝ)
    (hm : 0≤mesh) (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh) :
    Finset {i // i∉Lᶜ} :=
  selectedSlots Finset.univ (fun i : {i // i∉Lᶜ}=>w i.val) rho mesh hm
    (fun i _=>hw i.val) (fun i _=>hwm i.val)

theorem chosen_spec (L : Finset ι) (w : ι→ℝ) (rho mesh : ℝ)
    (hm : 0≤mesh) (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh) :
    Specification Finset.univ (fun i : {i // i∉Lᶜ}=>w i.val) rho mesh
      (chosenSlots L w rho mesh hm hw hwm) :=
  selectedSlots_spec _ _ _ _ _ _ _

/-- The source's actual slot scales, rather than a hypothetical selected
parameter, determine the exact volume used by the moment estimate. -/
theorem selected_volume (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (Z : ℝ) (hZ : 0<Z)
    (w : ι→ℝ) (hP : ∀i,s.P i=Z^(w i)) :
    MixedSelectedVolume.volume (supplierData s ha u L J)=
      Z^(∑j : J,w j.val.val) := by
  change (∏j : J,s.P j.val.val)=_
  simp_rw [hP]
  exact (Real.rpow_sum_of_pos hZ _ _).symm

theorem selected_log (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (Z : ℝ) (hZ : 1<Z)
    (w : ι→ℝ) (hP : ∀i,s.P i=Z^(w i)) :
    Real.logb Z (MixedSelectedVolume.volume (supplierData s ha u L J))=
      ∑j : J,w j.val.val := by
  rw [selected_volume s ha u L J Z (zero_lt_one.trans hZ) w hP,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

/-- Removing the selected supplier slots loses exactly their total width.
The nested residual index is the literal index used in the actual source. -/
theorem remaining_width (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (w : ι→ℝ) :
    (∑j : RestIndex (supplierData s ha u L J),w j.val.val)+
      (∑j : J,w j.val.val)=liveWidth L w := by
  have hrest : (∑j : RestIndex (supplierData s ha u L J),w j.val.val)=
      ∑j∈Finset.univ\J,w j.val := by
    exact (Finset.sum_subtype (F:=inferInstance)
      (p:=fun j : {i // i∉Lᶜ}=>j∉J) (Finset.univ\J)
      (by simp) (fun j=>w j.val)).symm
  rw [hrest,Finset.sum_coe_sort J (fun j : {i // i∉Lᶜ}=>w j.val)]
  exact Finset.sum_sdiff (Finset.subset_univ J) (f:=fun j=>w j.val)

/-- The large-width gates now refer to the selected volume and residual
slots of the actual supplier data. The reserve is uniform after the total
width floor; no separate lower bound on each marked slot is imposed. -/
theorem chosen_large_gates (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (w : ι→ℝ) (rho mesh : ℝ)
    (hm : 0≤mesh) (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,s.P i=Z^(w i))
    (hrho : 0<rho) (hlarge : rho<liveWidth L w) :
    let q:=supplierData s ha u L (chosenSlots L w rho mesh hm hw hwm)
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    let S:=∑j : RestIndex q,w j.val.val
    (43/100:ℝ)*liveWidth L w≤d ∧
      d≤(43/100:ℝ)*liveWidth L w+mesh ∧
      S+d=liveWidth L w ∧ rho/400<d-(3/4:ℝ)*S ∧ (3/4:ℝ)*S<d := by
  dsimp only
  let J:=chosenSlots L w rho mesh hm hw hwm
  have hj := large_branch Finset.univ J (fun i : {i // i∉Lᶜ}=>w i.val)
    rho mesh hrho (chosen_spec L w rho mesh hm hw hwm) hlarge
  have he := selected_log s ha u L J Z hZ w hP
  have hs := remaining_width s ha u L J w
  have hlo : (43/100:ℝ)*liveWidth L w≤∑j : J,w j.val.val := by
    rw [Finset.sum_coe_sort J (fun j : {i // i∉Lᶜ}=>w j.val)]
    exact hj.1
  have hhi : (∑j : J,w j.val.val)≤(43/100:ℝ)*liveWidth L w+mesh := by
    rw [Finset.sum_coe_sort J (fun j : {i // i∉Lᶜ}=>w j.val)]
    exact hj.2.1
  rw [he]
  exact ⟨hlo,hhi,hs,by linarith,by linarith⟩

theorem chosen_small (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (w : ι→ℝ) (rho mesh : ℝ)
    (hm : 0≤mesh) (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh)
    (hsmall : liveWidth L w≤rho) :
    chosenSlots L w rho mesh hm hw hwm=∅ ∧
    MixedSelectedVolume.volume
      (supplierData s ha u L (chosenSlots L w rho mesh hm hw hwm))=1 := by
  have he := (chosen_spec L w rho mesh hm hw hwm).2.1 hsmall
  refine ⟨he,?_⟩
  rw [he]
  simp only [MixedSelectedVolume.volume,supplierData,Finset.univ_eq_empty,
    Finset.prod_empty]

/-- The selected moment's pool, coefficient and profile hypotheses are
supplied by the original source record. No actual amplitude is replaced. -/
theorem supplier_admission (s : Source ι a b) (ha : 0<a) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ}) (Kslot : ℝ)
    (hM : ∀i,s.M i≤Kslot) :
    let q:=supplierData s ha u L J
    (∀i,0<q.P i) ∧
      (∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i) ∧
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1) ∧
      (∀i x,‖q.Wslot i x‖≤Kslot) ∧ 1≤MixedSelectedVolume.volume q := by
  dsimp only
  refine ⟨fun i=>zero_lt_one.trans_le (s.hP i),
    fun i I hI=>(s.hpn i I hI).2,fun i I _=>s.hν i I,
    fun i x=>(s.hWnorm i x).trans (hM i),?_⟩
  exact Finset.one_le_prod₀ (fun j _=>s.hP j.val.val)

theorem original_width_partition (L : Finset ι) (w : ι→ℝ) :
    liveWidth L w+(∑i : ↥Lᶜ,w i.val)=∑i,w i := by
  have hLive : liveWidth L w=∑i∈Finset.univ\Lᶜ,w i := by
    exact (Finset.sum_subtype (F:=inferInstance) (p:=fun i=>i∉Lᶜ)
      (Finset.univ\Lᶜ) (by simp) w).symm
  rw [hLive,Finset.sum_coe_sort Lᶜ w]
  exact Finset.sum_sdiff (Finset.subset_univ Lᶜ) (f:=w)

theorem frozen_volume_log (s : Source ι a b) (L : Finset ι)
    (Z : ℝ) (hZ : 1<Z) (w : ι→ℝ) (hP : ∀i,s.P i=Z^(w i)) :
    Real.logb Z (∏i : ↥Lᶜ,s.P i.val)=∑i : ↥Lᶜ,w i.val := by
  simp_rw [hP]
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans hZ),
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

/-- Freezing a supplying marked product pays its varying linear
conductor cost. Its log volume is subtracted from Q explicitly; it is
not included in a supposedly fixed constant. The full source capacity
improves by at least that amount because kappa is at least one. -/
theorem frozen_root_capacity (s : Source ι a b) (L : Finset ι)
    (Z : ℝ) (hZ : 1<Z) (w : ι→ℝ) (hw : ∀i,0≤w i)
    (hP : ∀i,s.P i=Z^(w i)) (P Q c Delta κ : ℝ) (hκ : 1≤κ)
    (hroot : P+κ*(∑i,w i)≤Q-c-Delta) :
    P+κ*liveWidth L w≤
      (Q-Real.logb Z (∏i : ↥Lᶜ,s.P i.val))-c-Delta := by
  rw [frozen_volume_log s L Z hZ w hP]
  have hsplit := original_width_partition L w
  have hf : 0≤∑i : ↥Lᶜ,w i.val := Finset.sum_nonneg (fun i _=>hw i.val)
  nlinarith

end
end Candidate.FourthPower.OuterFreshSelection

namespace Candidate.FourthPower.OuterFreshSelection
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open QRH.Record1252270103KernelMass CenteredMomentSectorLocalization
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedLiveNormalization MixedCommonCoefficient
open MixedSupplierFourthRow MixedSupplierSource OuterFreshSource
open OuterFreshSelectedWindow OuterFreshSelection OuterFreshMixedCapacity
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Before any second common extraction, the literal residual source
has the original ordinary prefix and exactly the unselected live slots.
Its root capacity therefore follows from the ORIGINAL source capacity.
The varying frozen slot volume is paid by subtracting its log from Q. -/
theorem residual_root_capacity (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (Z : ℝ) (hZ : 1<Z) (w : ι→ℝ) (hw : ∀i,0≤w i)
    (hP : ∀i,s.P i=Z^(w i)) (Q c Delta : ℝ)
    (hroot : Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*(∑i,w i)≤Q-c-Delta) :
    let q:=supplierData s ha u L J
    let r:=unavoidedResidual s ha cover u L J x
    Real.logb Z (r.T/pairNorm r.d)+(93/25:ℝ)*
        ((∑j : RestIndex q,w j.val.val)+Real.logb Z (MixedSelectedVolume.volume q))≤
      (Q-Real.logb Z (∏i : ↥Lᶜ,s.P i.val))-c-Delta := by
  have hf:=frozen_root_capacity s L Z hZ w hw hP
    (Real.logb Z (s.T/pairNorm s.d)) Q c Delta (93/25) (by norm_num) hroot
  have hd:=selected_log s ha u L J Z hZ w hP
  have hs:=remaining_width s ha u L J w
  dsimp only
  change Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*
      ((∑j : RestIndex (supplierData s ha u L J),w j.val.val)+
        Real.logb Z (MixedSelectedVolume.volume (supplierData s ha u L J)))≤_
  rw [hd,hs]
  exact hf

/-- Complete greedy-to-common-capacity composition for the actual
unavoided residual source. The original source, actual chosenSlots and
actual allocation determine every width in the conclusion.

Only the original root inequality and the separately paid first-stage
cutoff/reserve data remain numerical inputs. In particular there is no
assumed residual root, selected product width, common norm saving, native
gate or energy bound. The full ordinary prefix remains inside pairNorm. -/
theorem chosen_allocated_large_gate (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (w : ι→ℝ) (rhoFloor mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,s.P i=Z^(w i))
    (hrho : 0<rhoFloor) (hlarge : rhoFloor<liveWidth L w)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (hCE : CompletedGauss.primeSupport C=CompletedGauss.primeSupport E)
    (U : Finset (CommonIndex C E)) (G : Id) (hGE : G=C ∨ G=E)
    (Q c D0 Delta eDyad eDeclared Rdecl rhoMixed : ℝ)
    (hc : 0≤c) (heDyad : 0≤eDyad) (hD0 : -eDyad≤D0)
    (hroot : Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*(∑i,w i)≤Q-c-Delta)
    (hdeclared :
      (Q-Real.logb Z (∏i : ↥Lᶜ,s.P i.val))+(D0-c)-max (D0-c) 0-
        2*Real.logb Z (MixedSelectedVolume.volume
          (supplierData s ha u L (chosenSlots L w rhoFloor mesh hm hw hwm)))-
        Real.logb Z (normValue (commonFrequencyGenerator C E))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-eDeclared≤Rdecl)
    (hreserve : rhoMixed+
      (Fintype.card (RestIndex
        (supplierData s ha u L (chosenSlots L w rhoFloor mesh hm hw hwm))):ℝ)*
          Real.logb Z (2:ℝ)+4*mesh+eDyad+eDeclared≤Delta) :
    let J:=chosenSlots L w rhoFloor mesh hm hw hwm
    let q:=supplierData s ha u L J
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    ∀x : Frozen q,
    let r:=unavoidedResidual s ha cover u L J x
    ∀B : actualAllocations (tuplePools r) G,
      frozenCoefficient B.val G r.R r.ν r.Wslot r.P≠0→
      let live:=allocatedLiveSource r hb
        (unavoided_enclosure s ha cover u L J x) G B
      Real.logb Z (live.T/pairNorm live.d)+
          2*(∑j : liveIndices B.val,w j.val.val.val)+4*d≤Rdecl-rhoMixed ∧
        rhoFloor/400<d-(3/4:ℝ)*(∑j : liveIndices B.val,w j.val.val.val) ∧
        (3/4:ℝ)*(∑j : liveIndices B.val,w j.val.val.val)<d := by
  dsimp only
  intro x B hfrozen
  let J:=chosenSlots L w rhoFloor mesh hm hw hwm
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let d:=Real.logb Z (MixedSelectedVolume.volume q)
  let wr:RestIndex q→ℝ:=fun j=>w j.val.val
  have hchosen:=chosen_large_gates s ha u L w rhoFloor mesh hm hw hwm
    Z hZ hP hrho hlarge
  change (43/100:ℝ)*liveWidth L w≤d ∧
    d≤(43/100:ℝ)*liveWidth L w+mesh ∧
    (∑j : RestIndex q,wr j)+d=liveWidth L w ∧
    rhoFloor/400<d-(3/4:ℝ)*(∑j : RestIndex q,wr j) ∧
    (3/4:ℝ)*(∑j : RestIndex q,wr j)<d at hchosen
  have htotal:=hchosen.2.2.1
  have hlarge':rhoFloor<(∑j : RestIndex q,wr j)+d:=by
    rw [htotal]
    exact hlarge
  have hlo:(43/100:ℝ)*((∑j : RestIndex q,wr j)+d)≤d:=by
    rw [htotal]
    exact hchosen.1
  have hhi:d≤(43/100:ℝ)*((∑j : RestIndex q,wr j)+d)+mesh:=by
    rw [htotal]
    exact hchosen.2.1
  have hroot':Real.logb Z (r.T/pairNorm r.d)+(93/25:ℝ)*
      ((∑j : RestIndex q,wr j)+d)≤
      (Q-Real.logb Z (∏i : ↥Lᶜ,s.P i.val))-c-Delta:=
    residual_root_capacity s ha cover u L J x Z hZ w hw hP Q c Delta hroot
  have hwr:∀j : RestIndex q,0≤wr j:=fun j=>hw j.val.val
  have hPr:∀j : RestIndex q,r.P j=Z^(wr j):=fun j=>hP j.val.val
  have hWr:∀j : RestIndex q,Function.support (r.Wslot j)⊆Icc (1:ℝ) 2:=
    fun j=>s.hW j.val.val
  exact actual_allocated_large_gate r hb (unavoided_enclosure s ha cover u L J x)
    C E hC hE hCE U G hGE B Z wr hZ hwr hPr hWr hfrozen
    (Q-Real.logb Z (∏i : ↥Lᶜ,s.P i.val)) c D0 d Delta mesh eDyad
    eDeclared Rdecl rhoMixed rhoFloor hc heDyad hD0 hrho hlarge' hlo hhi
    hroot' hdeclared hreserve

end
end Candidate.FourthPower.OuterFreshSelection
