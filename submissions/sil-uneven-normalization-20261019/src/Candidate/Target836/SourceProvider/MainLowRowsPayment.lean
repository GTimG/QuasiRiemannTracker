import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowRows
import Candidate.Target836.SourceProvider.LowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryMainCostPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainBufferedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryMainFirstProjectorShell

/- Original module: Candidate.Target836.SourceProvider.MainLowRows. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
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

theorem actual_main_low_bin_admission
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (e T : ℝ) (p : BufferIndex e)
    (hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hz e T p)
    (hlow : bufferValue e p < ((1+Named.q)/2))
    (hweight : 1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re) :
    ActualLow M H hH st η₀ hQM hQη (((1+Named.q)/2)) e (3*(p.1.val+1:ℕ)*T) z := by
  have hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 := by
    intro heq
    rw [heq] at hweight
    norm_num at hweight
  apply whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz _ _ _ hs
  change geometryRowMaximum M H hH st η₀ hQM hQη z hz (3*(p.1.val+1:ℕ)*T) < (1+Named.q)/2+2*e
  linarith [hbin.2.2.2.2.2.2.2.1]

/-- Choose actual buffered bins on every complete signed ordinary row at
this fixed ray pair. Constants and allocations are not chosen per frequency. -/
theorem actual_main_low_buffered_rows
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=> True)
    ∃select : rows→BufferIndex e,∀z : rows,
      st.radial.keep z.val ∧
      1 ≤ (st.radial.profile (normValue z.val/st.radial.scale)).re ∧
      (bufferValue e (select z) < ((1+Named.q)/2) →
        ActualLow M H hH st η₀ hQM hQη (((1+Named.q)/2)) e
          (3*((select z).1.val+1:ℕ)*T) z.val) := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=> True) z.val z.property
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (ha z).1 e T he hT hβlo hβhi
  let select : rows→BufferIndex e := fun z=> Classical.choose (hp z)
  refine ⟨select,?_⟩
  intro z
  refine ⟨(ha z).1,(ha z).2.2,?_⟩
  intro hl
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z.val (ha z).1 e T
    (select z) (Classical.choose_spec (hp z)) hl
  simpa only [normValue_eq_embedding] using (ha z).2.2

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.actual_main_low_bin_admission
#print axioms Target874836.SourceProvider.Physical.actual_main_low_buffered_rows
end

/- Original module: Candidate.Target836.SourceProvider.MainLowRowsPayment. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Target874836.SourceProvider.Physical
noncomputable section
open OAI OAI.SevenEighths
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

def mainLowPaymentRows (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) : Finset O :=
  (rows.attach.filter (fun z=> select z=p ∧ bufferValue e p < ((1+Named.q)/2))).image Subtype.val

theorem mem_main_low_payment_rows (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (z : O) :
    z∈mainLowPaymentRows rows select p ↔
      ∃hz : z∈rows,select ⟨z,hz⟩=p ∧ bufferValue e p < ((1+Named.q)/2) := by
  simp only [mainLowPaymentRows,Finset.mem_image,Finset.mem_filter,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨x,hx,he⟩
    subst z
    exact ⟨x.property,hx⟩
  · rintro ⟨hz,hselect,hlow⟩
    exact ⟨⟨z,hz⟩,⟨hselect,hlow⟩,rfl⟩

theorem main_low_payment_rows_sum (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (p : BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if select z=p ∧ bufferValue e p < ((1+Named.q)/2) then f z.val else 0)=
      ∑z∈mainLowPaymentRows rows select p,f z := by
  rw [mainLowPaymentRows,Finset.sum_image]
  · rw [Finset.sum_filter]
    rfl
  · intro x _ y _ h
    exact Subtype.ext h

/-- All strict low rows occur in exactly one literal kernel bin. The
finite buffered index set is fixed before the moving rows or labels. -/
theorem main_low_payment_complete_low_sum (rows : Finset O) {e : ℝ}
    (select : rows→BufferIndex e) (f : O→ℝ) :
    (∑z : rows,if bufferValue e (select z) < ((1+Named.q)/2) then f z.val else 0)=
      ∑p : BufferIndex e,∑z∈mainLowPaymentRows rows select p,f z := by
  calc
    _=∑z : rows,∑p : BufferIndex e,
        if select z=p ∧ bufferValue e p < ((1+Named.q)/2) then f z.val else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [ite_and]
      simp
    _=∑p : BufferIndex e,∑z : rows,
        if select z=p ∧ bufferValue e p < ((1+Named.q)/2) then f z.val else 0 := Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro p _
      exact main_low_payment_rows_sum rows select p f

/-- The genuine buffered partition supplies precisely the low kernel's
keep and low gates, and dominates literal unit weight, for each fixed bin.
The reflected ray and signed row are retained throughout. -/
theorem actual_main_low_payment_bins
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (d : SecondInputDatum α) (χ₀ χ ψ : RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1 < Z) (second : Bool)
    (hP : d.R*(if second then d.D else d.C)≠0)
    (hPN : ((d.R*(if second then d.D else d.C)).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0 < e) (hT : 2 < T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let st:=retainedState Z Bmask hZ (if second then d.τ ψ⁻¹ else d.τ χ) Q
      (d.R*(if second then d.D else d.C)) hP hPN d.radius d.C d.D d.inactive
    let rows:=mainLowSourceRows second (ordinarySecondDatum d χ₀ Q m) (fun _=> True)
    ∃select : rows→BufferIndex e,∀p z,z∈mainLowPaymentRows rows select p→
      st.radial.keep z ∧
      ActualLow M H hH st η₀ hQM hQη (((1+Named.q)/2)) e (3*(p.1.val+1:ℕ)*T) z ∧
      1 ≤ (st.radial.profile (normValue z/st.radial.scale)).re ∧
      1 ≤ p.1.val ∧ p.1.val ≤ bufferCount e := by
  intro st rows
  have ha (z : rows) := actual_main_low_source_admission d χ₀ χ ψ Q hQ m hm hml hm2
    Z Bmask hZ second hP hPN (fun _=> True) z.val z.property
  have hp (z : rows) := actual_geometry_zero_partition M H hH st η₀ hQM hQη
    z.val (ha z).1 e T he hT hβlo hβhi
  let select : rows→BufferIndex e := fun z=> Classical.choose (hp z)
  refine ⟨select,?_⟩
  intro p z hz
  obtain ⟨hzrows,hsel,hlow⟩ := (mem_main_low_payment_rows rows select p z).mp hz
  have hg:=ha ⟨z,hzrows⟩
  have hbin : GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T p := by
    have hb:=Classical.choose_spec (hp ⟨z,hzrows⟩)
    change GeometryZeroBin M H hH st η₀ hQM hQη z hg.1 e T (select ⟨z,hzrows⟩) at hb
    rw [hsel] at hb
    exact hb
  refine ⟨hg.1,?_,hg.2.2,hbin.1,hbin.2.1⟩
  apply actual_main_low_bin_admission M H hH st η₀ hQM hQη z hg.1 e T p hbin hlow
  simpa only [normValue_eq_embedding] using hg.2.2

/-- A single bounded shifted-height envelope is sufficient for every
occupied buffered bin. The bin index is chosen from genuine zero geometry. -/
theorem main_low_payment_height_bin {e : ℝ} (p : BufferIndex e)
    (hp : 1 ≤ p.1.val) (v height T : ℝ) (hT : 0 ≤ T)
    (hheight : |v|+height+T/2 ≤ 5*T) :
    |v|+height+T/2 ≤ (3*p.1.val+2:ℕ)*T := by
  apply hheight.trans
  apply mul_le_mul_of_nonneg_right _ hT
  exact_mod_cast (show 5 ≤ 3*p.1.val+2 by omega)

/-- Both literal first-Mellin orientations fit the bounded kernel range.
The cutoff is common to all rows and does not restrict either shift globally. -/
theorem main_low_payment_shifted_height_envelope
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

/-- The genuine positive selector index puts both shifted rays into the
same buffered height bin used by the original low kernel. -/
theorem main_low_payment_shifted_height_bin {e : ℝ} (p : BufferIndex e)
    (hp : 1 ≤ p.1.val) (second : Bool) (v height t u T : ℝ) (hT : 0 ≤ T)
    (hsmall : 2*(1+|v|+height+2*Real.pi*(|t|+|u|)) ≤ T) :
    |v+2*Real.pi*(u-(if second then -t else t))|+height+T/2 ≤ 
      (3*p.1.val+2:ℕ)*T :=
  main_low_payment_height_bin p hp _ height T hT
    (main_low_payment_shifted_height_envelope second v height t u T hT hsmall)

/-- A strict small-tau inequality supplies the high-parameter gate for
EVERY member of the fixed finite zero-bin dictionary at one common threshold.
The threshold precedes source rows, characters, allocations and heights. -/
theorem eventual_main_low_payment_high_gate (e τ d η : ℝ)
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

/-- The fixed physical lower factor stays outside the complete selected
family. There is no arithmetic-label cardinality or extra source volume. -/
theorem main_low_payment_physical_factor {Label : Type*} [Fintype Label]
    (N : ℕ) (a ap : ℝ) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (zs : Label→Finset O) (f : Label→Ideal O→O→ℝ) :
    (∑l,∑D∈(d l).block.divisors.filter Squarefree,
      (coefficient l*((d l).K/lowerFactor N a ap)*normalizer (d l).C (d l).D (d l).inactive)*
        (∑z∈zs l,f l D z))=
    (1/lowerFactor N a ap)*
      (∑l,∑D∈(d l).block.divisors.filter Squarefree,
        (coefficient l*(d l).K*normalizer (d l).C (d l).D (d l).inactive)*
          (∑z∈zs l,f l D z)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  ring

end
end Target874836.SourceProvider.Physical
#print axioms Target874836.SourceProvider.Physical.main_low_payment_rows_sum
#print axioms Target874836.SourceProvider.Physical.main_low_payment_complete_low_sum
#print axioms Target874836.SourceProvider.Physical.actual_main_low_payment_bins
#print axioms Target874836.SourceProvider.Physical.main_low_payment_physical_factor
#print axioms Target874836.SourceProvider.Physical.main_low_payment_height_bin
#print axioms Target874836.SourceProvider.Physical.main_low_payment_shifted_height_envelope
#print axioms Target874836.SourceProvider.Physical.main_low_payment_shifted_height_bin
#print axioms Target874836.SourceProvider.Physical.eventual_main_low_payment_high_gate
end
