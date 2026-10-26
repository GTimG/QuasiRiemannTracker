import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainFirstProjectorShell
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentCommonHeightEnvelope CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondInputCapacitySource
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentSectorLocalization
open CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondHeightFamily
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open LocalMoment
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowPaymentSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- One common second allocation and one original row witness per original
nonzero block, selected before the complete row or ray sums. -/
theorem actual_main_low_family_choices {Label : Type*}
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : Label→ geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (second : Bool) :
    let d:=fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (j l).val.1 hz₁ hz₂ (j l).val.2
    ∃B₂ : (l : Label)→actualAllocations (d l).input.pools (if second then (d l).D else (d l).C),
      ∃_rwitness : (l : Label)→secondLiveRows (fun _:Unit=>(d l).block),
        ∀l,frozenCoefficient (B₂ l).val (if second then (d l).D else (d l).C) (d l).R
          (d l).input.ν (d l).input.W (d l).input.P≠0 ∧
          (d l).inactive∈inactiveSubsets (d l).C (d l).D := by
  intro d
  have h (l : Label) := actual_geometry_main_low_choices reflected s R seed Z Mrow amp ξ reserve b t N hZ
    key hz₁ hz₂ (j l) second
  choose B₂ rwitness hgood using h
  exact ⟨B₂,rwitness,hgood⟩

/-- The complete second family for selected first allocations, filtered by
the ORIGINAL full physical block before any ordinary or zero-bin restriction. -/
def mainLowSelectedNonzeroRows {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) :
    Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      (firstIndex l)) :=
  Finset.univ.filter (fun r=>
    (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key)∈
      geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)

def mainLowSelectedOriginal {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (r : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ :=
  ⟨⟨firstIndex r.val.1,r.val.2⟩,(Finset.mem_filter.mp r.property).2⟩

/-- Original nonzero membership supplies the genuine inactive-subset gate
for every selected block. It never asks that the restricted block be nonzero. -/
theorem actual_main_low_selected_inactive {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (r : mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ firstIndex) :
    ActualSecondBlockIndex.IsInactive r.val.2 := by
  exact (actual_geometry_main_original_admission reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ (mainLowSelectedOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂
      firstIndex r)).2

variable [Cycle63.AffineLedger] in
/-- A literal buffered bin in the complete signed row set. -/
def mainLowPaymentRows (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) : Finset O :=
  (rows.attach.filter (fun z=>select z=p ∧ bufferValue e p<((1+Cycle63.AffineLedger.q)/2))).image Subtype.val

variable [Cycle63.AffineLedger] in
theorem mem_main_low_payment_rows (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (z : O) :
    z∈mainLowPaymentRows rows select p ↔
      ∃hz : z∈rows,select ⟨z,hz⟩=p ∧ bufferValue e p<((1+Cycle63.AffineLedger.q)/2) := by
  simp only [mainLowPaymentRows,Finset.mem_image,Finset.mem_filter,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨x,hx,he⟩
    subst z
    exact ⟨x.property,hx⟩
  · rintro ⟨hz,hselect,hlow⟩
    exact ⟨⟨z,hz⟩,⟨hselect,hlow⟩,rfl⟩

variable [Cycle63.AffineLedger] in
theorem main_low_payment_rows_sum (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if select z=p ∧ bufferValue e p<((1+Cycle63.AffineLedger.q)/2) then f z.val else 0)=
      ∑z∈mainLowPaymentRows rows select p,f z := by
  rw [mainLowPaymentRows,Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · intro x _ y _ h
    exact Subtype.ext h

variable [Cycle63.AffineLedger] in
/-- All strict low rows occur in exactly one literal kernel bin. The
finite buffered index set is fixed before the moving rows or labels. -/
theorem main_low_payment_complete_low_sum (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if bufferValue e (select z)<((1+Cycle63.AffineLedger.q)/2) then f z.val else 0)=
      ∑p : BufferIndex e,∑z∈mainLowPaymentRows rows select p,f z := by
  calc
    _=∑z : rows,∑p : BufferIndex e,
        if select z=p ∧ bufferValue e p<((1+Cycle63.AffineLedger.q)/2) then f z.val else 0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [ite_and]
      simp
    _=∑p : BufferIndex e,∑z : rows,
        if select z=p ∧ bufferValue e p<((1+Cycle63.AffineLedger.q)/2) then f z.val else 0 := Finset.sum_comm
    _=_ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      exact main_low_payment_rows_sum rows select p f

/-- A single bounded shifted-height envelope is sufficient for every
occupied buffered bin. The bin index is chosen from genuine zero geometry. -/
theorem main_low_payment_height_bin {e : ℝ} (p : BufferIndex e)
    (hp : 1≤p.1.val) (v height T : ℝ) (hT : 0≤T)
    (hheight : |v|+height+T/2≤5*T) :
    |v|+height+T/2≤(3*p.1.val+2:ℕ)*T := by
  apply hheight.trans
  apply mul_le_mul_of_nonneg_right _ hT
  exact_mod_cast (show 5≤3*p.1.val+2 by omega)

/-- Both literal first-Mellin orientations fit the bounded kernel range.
The cutoff is common to all rows and does not restrict either shift globally. -/
theorem main_low_payment_shifted_height_envelope
    (second : Bool) (v height t u T : ℝ) (hT : 0≤T)
    (hsmall : 2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤T) :
    |v+2*Real.pi*(u-(if second then -t else t))|+height+T/2≤5*T := by
  have hs : |u-(if second then -t else t)|≤|u|+|t| := by
    cases second
    · simpa using abs_sub_le u 0 t
    · simpa using abs_sub_le u 0 (-t)
  have hmul : |2*Real.pi*(u-(if second then -t else t))|≤
      2*Real.pi*(|u|+|t|) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hv := (abs_add_le v (2*Real.pi*(u-(if second then -t else t)))).trans
    (add_le_add (le_refl |v|) hmul)
  nlinarith

/-- A strict small-tau inequality supplies the high-parameter gate for
EVERY member of the fixed finite zero-bin dictionary at one common threshold.
The threshold precedes source rows, characters, allocations and heights. -/
theorem eventual_main_low_payment_high_gate (e τ d η : ℝ)
    (hτ : 0<τ) (hgap : 2*τ<d*η) :
    ∀ᶠ Z : ℝ in Filter.atTop,1<Z ∧ 2<Z^τ ∧
      ∀p : BufferIndex e,(3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(Z^d)^η := by
  let B : ℕ := 3*bufferCount e+2
  let K : ℝ := 3+(B:ℝ)
  have hg : 0<d*η-2*τ := sub_pos.mpr hgap
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (Filter.eventually_gt_atTop (2:ℝ)),
    (tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop (K^2))]
    with Z hZ hT hpower
  refine ⟨hZ,hT,?_⟩
  intro p
  have hz : 0<Z := zero_lt_one.trans hZ
  have hscale : 1≤Z^τ := by linarith
  have hi : 3*p.1.val+2≤B := by
    dsimp only [B]
    have hp := p.1.isLt
    omega
  have hic : ((3*p.1.val+2:ℕ):ℝ)≤(B:ℝ) := by exact_mod_cast hi
  have hbound : 3+(3*p.1.val+2:ℕ)*Z^τ≤K*Z^τ := by
    have hm := mul_le_mul_of_nonneg_right hic (Real.rpow_nonneg hz.le τ)
    dsimp only [K]
    nlinarith
  have hsquare : (3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(K*Z^τ)^2 :=
    pow_le_pow_left₀ (by positivity) hbound 2
  calc
    (3+(3*p.1.val+2:ℕ)*Z^τ)^2≤(K*Z^τ)^2 := hsquare
    _=K^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [mul_comm,Real.rpow_mul hz.le]
      exact (Real.rpow_two _).symm
    _≤Z^(d*η-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hz.le _)
    _=Z^(d*η) := by rw [←Real.rpow_add hz]; congr 1; ring
    _=(Z^d)^η := by rw [Real.rpow_mul hz.le]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
