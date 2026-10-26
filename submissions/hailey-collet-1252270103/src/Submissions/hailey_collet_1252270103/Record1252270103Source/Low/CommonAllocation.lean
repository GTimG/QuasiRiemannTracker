/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact generic allocation ledger extracted from Record12518109RawCaps
PhysicalCap/FrozenLedger, retaining OpenAI/Gao common-allocation attribution.
No narrow source-cell or positive plain-floor admission is imported. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRadialData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonRawScale
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
import Submissions.hailey_collet_1252270103.Record12518109Source.Erasure

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Filter
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationChildSourceCaps QRH.Record12518109Source
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

def firstPlainReduction (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (Z : ℝ) (j : Fin 2) : ℝ := Real.logb Z ((B.val (Sum.inr j)).absNorm:ℝ)

theorem first_plain_reduction_bounds (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) (Z : ℝ) (hZ : 1<Z) :
    (∀j,0≤firstPlainReduction s C B Z j) ∧
      firstPlainReduction s C B Z 0+firstPlainReduction s C B Z 1≤Real.logb Z (C.absNorm:ℝ) := by
  have hn (j : α⊕Fin 2) : (1:ℝ)≤(B.val j).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  refine ⟨fun j=>Real.logb_nonneg hZ (hn _),?_⟩
  have hp : 1≤∏i : α,((B.val (Sum.inl i)).absNorm:ℝ) :=
    Finset.one_le_prod₀ (fun i _=>hn _)
  have hm := mul_le_mul_of_nonneg_left hp (plainNorm_pos B.val (alloc_ne s C B)).le
  have he:=product_norm B.val
  rw [allocation_product s C B] at he
  have hb : plainNorm B.val≤(C.absNorm:ℝ) := by rw [he];simpa using hm
  have hh:=Real.logb_le_logb_of_le hZ (plainNorm_pos B.val (alloc_ne s C B)) hb
  simpa only [plainNorm,firstPlainReduction,Real.logb_mul
    (alloc_norm_pos s C B _).ne' (alloc_norm_pos s C B _).ne'] using hh

def firstFrozenSlots (B : Tuple α) : Finset α :=
  Finset.univ.filter (fun i=>B (Sum.inl i)≠1)
def firstFrozenWidth (B : Tuple α) (w : α→ℝ) : ℝ := ∑i∈firstFrozenSlots B,w i

def firstNormFrozen (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (Z : ℝ) : ℝ := Real.logb Z (C.absNorm:ℝ)-
      (firstPlainReduction s C B Z 0+firstPlainReduction s C B Z 1)

theorem live_frozen_width_split (B : Tuple α) (w : α→ℝ) :
    (∑i∈liveIndices B,w i)=(∑i,w i)-firstFrozenWidth B w := by
  have hh:=Finset.sum_filter_add_sum_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) w
  dsimp only [liveIndices,firstFrozenWidth,firstFrozenSlots]
  linarith

theorem raw_reduction_frozen_log (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) (w : α→ℝ) (Z : ℝ) (hZ : 1<Z)
    (hscale : ∀i,s.P i=Z^(w i)) :
    Real.logb Z (rawReduction B.val s.P)=
      firstPlainReduction s C B Z 0+firstPlainReduction s C B Z 1+firstFrozenWidth B.val w := by
  have hplain:=Real.logb_mul (alloc_norm_pos s C B (Sum.inr 0)).ne'
    (alloc_norm_pos s C B (Sum.inr 1)).ne' (b:=Z)
  rw [rawReduction,Real.logb_mul (plainNorm_pos B.val (alloc_ne s C B)).ne'
    (Finset.prod_pos (fun i _=>frozenScale_pos B.val s.P s.P_pos i)).ne',
    Real.logb_prod _ _ (fun i _=>(frozenScale_pos B.val s.P s.P_pos i).ne')]
  change Real.logb Z (plainNorm B.val)+_= _
  rw [show Real.logb Z (plainNorm B.val)=
    firstPlainReduction s C B Z 0+firstPlainReduction s C B Z 1 by exact hplain]
  congr 1
  rw [firstFrozenWidth,firstFrozenSlots,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h:B.val (Sum.inl i)=1
  · simp [frozenScale,h]
  · simp only [frozenScale,ite_eq_right h,hscale i,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',ite_eq_left h]

/-- Both annular corrections are explicit and depend only on the original
slot count and fixed support endpoints. -/
theorem frozen_width_norm_bounds (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (w : α→ℝ) (Z lower upper : ℝ)
    (hZ : 1<Z) (hlower : 0<lower) (hslo : lower≤s.lower) (hshi : s.upper≤upper)
    (hscale : ∀i,s.P i=Z^(w i))
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    firstFrozenWidth B.val w-firstNormFrozen s C B Z≤
      -(Fintype.card α:ℝ)*Real.logb Z (min 1 lower) ∧
    firstNormFrozen s C B Z-firstFrozenWidth B.val w≤
      (Fintype.card α:ℝ)*Real.logb Z (max 1 upper) := by
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have ha : 0<min 1 lower:=lt_min zero_lt_one hlower
  have hb : 0<max 1 upper:=zero_lt_one.trans_le (le_max_left _ _)
  have hn:=actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos lower upper hlower
    (fun i x hx=>⟨hslo.trans (s.slot_support i hx).1,((s.slot_support i hx).2).trans hshi⟩) hne
  have hlo:=Real.logb_le_logb_of_le hZ (mul_pos (pow_pos ha _) hr) hn.1
  have hhi:=Real.logb_le_logb_of_le hZ
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (allocation_ne s C B))) hn.2
  rw [Real.logb_mul (pow_pos ha _).ne' hr.ne',Real.logb_pow,
    raw_reduction_frozen_log s C B w Z hZ hscale] at hlo
  rw [Real.logb_mul (pow_pos hb _).ne' hr.ne',Real.logb_pow,
    raw_reduction_frozen_log s C B w Z hZ hscale] at hhi
  dsimp only [firstNormFrozen]
  exact ⟨by linarith,by linarith⟩

theorem norm_frozen_le_common (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) (Z : ℝ) (hZ : 1<Z) :
    firstNormFrozen s C B Z≤Real.logb Z (C.absNorm:ℝ) := by
  have hh:=first_plain_reduction_bounds s C B Z hZ
  dsimp only [firstNormFrozen]
  linarith [hh.1 0,hh.1 1]

theorem eventual_frozen_annular_loss (N : ℕ) (lower upper ε : ℝ)
    (hlower : 0<lower) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
      -(N:ℝ)*Real.logb Z (min 1 lower)≤ε ∧
      (N:ℝ)*Real.logb Z (max 1 upper)≤ε := by
  have ha : 0<min 1 lower:=lt_min zero_lt_one hlower
  have hb : 0<max 1 upper:=zero_lt_one.trans_le (le_max_left _ _)
  have hal : Real.log (min 1 lower)≤0:=Real.log_nonpos ha.le (min_le_left _ _)
  have hbl : 0≤Real.log (max 1 upper):=Real.log_nonneg (le_max_left _ _)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop
    ((N:ℝ)*(-Real.log (min 1 lower)+Real.log (max 1 upper))/ε)),
    eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_,?_⟩
  all_goals
    unfold Real.logb
    have hh:=(div_le_iff₀ hε).mp hz
    have hn : (0:ℝ)≤N:=Nat.cast_nonneg _
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    nlinarith

theorem first_live_width_le (B : Tuple α) (w : α→ℝ) (S : Finset α) (b : ℝ)
    (hw : ∀i,0≤w i) (hS : S⊆liveIndices B) (htotal : (∑i,w i)≤b) :
    (∑i∈S,w i)≤b-firstFrozenWidth B w := by
  have hs:=(Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _=>hw i))
  rw [live_frozen_width_split] at hs
  linarith

/-- The erased set is chosen from widths before row data. Frozen and
removed widths share one residual budget, with only the whole-slot mesh. -/
theorem frozen_erasure_ledger (B : Tuple α) (w : α→ℝ) (S : Finset α)
    (b cap slotMesh : ℝ) (hw : ∀i,0≤w i) (hwm : ∀i∈S,w i≤slotMesh)
    (hS : S⊆liveIndices B) (htotal : (∑i,w i)≤b)
    (hmesh : 0≤slotMesh) (hcap : 0≤cap) (hfirst : cap≤b-firstFrozenWidth B w) :
    ∃R : Finset α,R⊆S ∧ (∑i∈S\R,w i)≤cap ∧
      (∑i∈R,w i)≤b-firstFrozenWidth B w-cap+slotMesh ∧
      firstFrozenWidth B w+(∑i∈R,w i)≤b-cap+slotMesh := by
  obtain ⟨R,hR,hleft,hprice⟩:=erase_to_first_cap S w slotMesh
    (b-firstFrozenWidth B w) cap hmesh hcap hfirst (fun i _=>hw i) hwm
    (first_live_width_le B w S b hw hS htotal)
  refine ⟨R,hR,?_,hprice,by linarith⟩
  convert hleft using 1
  congr 1
  ext j
  simp


/-- The zero-erasure branch is retained even when the requested cap exceeds all
remaining width. The removal choice depends only on widths and the common tuple. -/
theorem global_frozen_erasure (B : Tuple α) (w : α → ℝ) (S : Finset α)
    (b cap slotMesh : ℝ) (hw : ∀i,0 ≤ w i) (hwm : ∀i∈S,w i ≤ slotMesh)
    (hS : S ⊆ liveIndices B) (htotal : (∑i,w i) ≤ b)
    (hmesh : 0 ≤ slotMesh) (hcap : 0 ≤ cap) :
    ∃ R : Finset α,R ⊆ S ∧ (∑i∈S\R,w i) ≤ cap ∧
      (∑i∈R,w i) ≤ max 0 (b-firstFrozenWidth B w-cap)+slotMesh := by
  have hlive := first_live_width_le B w S b hw hS htotal
  have hnonneg : 0 ≤ b-firstFrozenWidth B w :=
    (Finset.sum_nonneg (fun i _=>hw i)).trans hlive
  obtain ⟨R,hR,hleft,hcost⟩ := erase_to_first_cap S w slotMesh
    (b-firstFrozenWidth B w) (min cap (b-firstFrozenWidth B w))
    hmesh (le_min hcap hnonneg) (min_le_right _ _)
    (fun i _=>hw i) hwm hlive
  refine ⟨R,hR,?_,?_⟩
  · convert hleft.trans (min_le_left _ _) using 1
    congr 1
    ext j
    simp
  ·
    have he : b-firstFrozenWidth B w-min cap (b-firstFrozenWidth B w) =
        max 0 (b-firstFrozenWidth B w-cap) := by
      rcases le_total cap (b-firstFrozenWidth B w) with h|h
      · rw [min_eq_left h,max_eq_right (by linarith)]
      · rw [min_eq_right h,max_eq_left (by linarith)];ring
    simpa only [he] using hcost

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.frozen_width_norm_bounds
#print axioms QRH.Record1252270103Low.eventual_frozen_annular_loss
#print axioms QRH.Record1252270103Low.global_frozen_erasure
