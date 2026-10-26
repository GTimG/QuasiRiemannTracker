import Candidate.Uneven.MainParameters
import Candidate.Uneven.MainLowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowRows
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCostPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainFirstProjectorShell

/- Original module: Candidate.Uneven.MainPhysicalRows. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.MainLow
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open Cycle63FinalNatural CenteredMomentEnergyState Cycle63Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondInputCapacitySource CenteredMomentSecondHeightFamily Cycle63Moment
open CenteredMomentFirstDiscardedEnergy LocalMoment
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowRowsSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

theorem actual_main_low_bin_admission (P : Plane)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p < ((1+P.q)/2))
    (hweight : 1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) :
    ActualLow M H hH st η₀ hQM hQη (((1+P.q)/2)) e (3*(p.1.val+1:ℕ)*T) z := by
  have hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 := by
    intro heq
    rw [heq] at hweight
    norm_num at hweight
  apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
  change geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) < (1+P.q)/2+2*e
  linarith [hbin.2.2.2.2.2.2.2.1]


end
end OAI.SevenEighths.MainPhysical
end

/- Original module: Candidate.Uneven.MainPhysicalRowsPayment. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.MainLow
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap
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
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance mainLowPaymentSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

def mainLowPaymentRows (P : Plane) (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) : Finset O :=
  (rows.attach.filter (fun z=> select z=p ∧ bufferValue e p < ((1+P.q)/2))).image Subtype.val

theorem mem_main_low_payment_rows (P : Plane) (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (z : O) :
    z∈mainLowPaymentRows (P := P) rows select p ↔
      ∃hz : z∈rows,select ⟨z,hz⟩=p ∧ bufferValue e p < ((1+P.q)/2) := by
  simp only [mainLowPaymentRows,Finset.mem_image,Finset.mem_filter,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨x,hx,he⟩
    subst z
    exact ⟨x.property,hx⟩
  · rintro ⟨hz,hselect,hlow⟩
    exact ⟨⟨z,hz⟩,⟨hselect,hlow⟩,rfl⟩

theorem main_low_payment_rows_sum (P : Plane) (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if select z=p ∧ bufferValue e p < ((1+P.q)/2) then f z.val else 0)=
      ∑z∈mainLowPaymentRows (P := P) rows select p,f z := by
  rw [mainLowPaymentRows,Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · intro x _ y _ h
    exact Subtype.ext h

/-- All strict low rows occur in exactly one literal kernel bin. The
finite buffered index set is fixed before the moving rows or labels. -/
theorem main_low_payment_complete_low_sum (P : Plane) (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if bufferValue e (select z) < ((1+P.q)/2) then f z.val else 0)=
      ∑p : BufferIndex e,∑z∈mainLowPaymentRows (P := P) rows select p,f z := by
  calc
    _=∑z : rows,∑p : BufferIndex e,
        if select z=p ∧ bufferValue e p < ((1+P.q)/2) then f z.val else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [ite_and]
      simp
    _=∑p : BufferIndex e,∑z : rows,
        if select z=p ∧ bufferValue e p < ((1+P.q)/2) then f z.val else 0 := Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro p _
      exact main_low_payment_rows_sum (P := P) rows select p f


/-- A single bounded shifted-height envelope is sufficient for every
occupied buffered bin. The bin index is chosen from genuine zero geometry. -/
theorem main_low_payment_height_bin (P : Plane) {e : ℝ} (p : BufferIndex e)
    (hp : 1 ≤ p.1.val) (v height T : ℝ) (hT : 0 ≤ T)
    (hheight : |v|+height+T/2 ≤ 5*T) :
    |v|+height+T/2 ≤ (3*p.1.val+2:ℕ)*T := by
  apply hheight.trans
  apply mul_le_mul_of_nonneg_right _ hT
  exact_mod_cast (show 5 ≤ 3*p.1.val+2 by omega)

/-- Both literal first-Mellin orientations fit the bounded kernel range.
The cutoff is common to all rows and does not restrict either shift globally. -/
theorem main_low_payment_shifted_height_envelope (P : Plane)
    (second : Bool) (v height t u T : ℝ) (hT : 0 ≤ T)
    (hsmall : 2*(1+|v|+height+2*Real.pi*(|t|+|u|)) ≤ T) :
    |v+2*Real.pi*(u-(if second then -t else t))|+height+T/2 ≤ 5*T := by
  have hs : |u-(if second then -t else t)| ≤ |u|+|t| := by
    cases second
    · simpa using abs_sub_le u 0 t
    · simpa using abs_sub_le u 0 (-t)
  have hmul : |2*Real.pi*(u-(if second then -t else t))| ≤ 
      2*Real.pi*(|u|+|t|) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hv := (abs_add_le v (2*Real.pi*(u-(if second then -t else t)))).trans
    (add_le_add (le_refl |v|) hmul)
  nlinarith


/-- A strict small-tau inequality supplies the high-parameter gate for
EVERY member of the fixed finite zero-bin dictionary at one common threshold.
The threshold precedes source rows, characters, allocations and heights. -/
theorem eventual_main_low_payment_high_gate (P : Plane) (e τ d η : ℝ)
    (hτ : 0 < τ) (hgap : 2*τ < d*η) :
    ∀ᶠ Z : ℝ in Filter.atTop,1 < Z ∧ 2 < Z^τ ∧
      ∀p : BufferIndex e,(3+(3*p.1.val+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η := by
  let B : ℕ := 3*bufferCount e+2
  let K : ℝ := 3+(B:ℝ)
  have hg : 0 < d*η-2*τ := sub_pos.mpr hgap
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (Filter.eventually_gt_atTop (2:ℝ)),
    (tendsto_rpow_atTop hg).eventually (Filter.eventually_ge_atTop (K^2))]
    with Z hZ hT hpower
  refine ⟨hZ,hT,?_⟩
  intro p
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hscale : 1 ≤ Z^τ := by linarith
  have hi : 3*p.1.val+2 ≤ B := by
    dsimp only [B]
    have hp := p.1.isLt
    omega
  have hic : ((3*p.1.val+2:ℕ):ℝ) ≤ (B:ℝ) := by exact_mod_cast hi
  have hbound : 3+(3*p.1.val+2:ℕ)*Z^τ ≤ K*Z^τ := by
    have hm := mul_le_mul_of_nonneg_right hic (Real.rpow_nonneg hz.le τ)
    dsimp only [K]
    nlinarith
  have hsquare : (3+(3*p.1.val+2:ℕ)*Z^τ)^2 ≤ (K*Z^τ)^2 :=
    pow_le_pow_left₀ (by positivity) hbound 2
  calc
    (3+(3*p.1.val+2:ℕ)*Z^τ)^2 ≤ (K*Z^τ)^2 := hsquare
    _=K^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [mul_comm,Real.rpow_mul hz.le]
      exact (Real.rpow_two _).symm
    _ ≤ Z^(d*η-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hz.le _)
    _=Z^(d*η) := by rw [←Real.rpow_add hz]; congr 1; ring
    _=(Z^d)^η := by rw [Real.rpow_mul hz.le]


end
end OAI.SevenEighths.MainPhysical
end
