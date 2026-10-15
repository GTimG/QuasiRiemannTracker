/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B135
import Submissions.gao_cycle61_plane_20261013.Bundles.B151
import Submissions.gao_cycle61_plane_20261013.Bundles.B154
import Submissions.gao_cycle61_plane_20261013.Bundles.B172

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainBufferedPartition; sha256 110d3fa19ace202dd5fc661bd2d1eb9b6ba3b2ef232c6594bf3a53cf20c28c71 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                        

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion LocalMoment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Cycle61FinalNatural CenteredMomentEnergyState Cycle61Moment.LowBranch
open ConcretePrimeRowBridge ConcreteTraceCRT CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- One buffered bin contains each original row exactly when its single
selector chooses that bin. Projector costs remain inside the row cost. -/
def mainBufferedCostBin {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→ BufferIndex e) (cost : rows→ℝ) (p : BufferIndex e) : ℝ :=
  ∑r : rows,if select r=p then cost r else 0

/-- Exact finite disintegration, followed by the strict-low/inclusive-high
cut. This does not charge the number of source labels or rows. -/
theorem main_buffered_cost_partition {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→ BufferIndex e) (cost : rows→ℝ) :
    (∑r : rows,cost r)=
      (∑p∈Finset.univ.filter (fun p=>bufferValue e p<167/200),
        mainBufferedCostBin rows e select cost p)+
      (∑p∈Finset.univ.filter (fun p=>167/200≤ bufferValue e p),
        mainBufferedCostBin rows e select cost p) := by
  have hf := geometry_zero_fiber_reassembly rows e select cost
  simp only [Finset.sum_filter,Finset.attach_eq_univ] at hf
  exact hf.trans (geometry_zero_low_high_reassembly e _)

/-- The projector union and its shells are formed from the whole original
row family, before either zero-bin grouping or low/high filtering. -/
def mainBufferedShellBin {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→ BufferIndex e) (Ds : rows→ Finset (Ideal O))
    (cost : rows→ Ideal O→ℝ) (n : ℤ) (p : BufferIndex e) : ℝ :=
  ∑r : rows,if select r=p then
    ∑D∈shell (sharedProjectors Ds) n,if D∈Ds r then cost r D else 0
  else 0

/-- Exact common-shell disintegration retains the original per-row ideal
membership filter. Both branches use the same global projector union. -/
theorem main_buffered_projector_partition {ι : Type*} (rows : Finset ι) (e : ℝ)
    (select : rows→ BufferIndex e) (Ds : rows→ Finset (Ideal O))
    (hs : ∀r D,D∈Ds r→ Squarefree D) (cost : rows→ Ideal O→ℝ) :
    (∑r : rows,∑D∈Ds r,cost r D)=
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>bufferValue e p<167/200),
          mainBufferedShellBin rows e select Ds cost n p)+
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>167/200≤ bufferValue e p),
          mainBufferedShellBin rows e select Ds cost n p) := by
  rw [shared_projector_shell_sum Ds hs cost,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact main_buffered_cost_partition rows e select
    (fun r=>∑D∈shell (sharedProjectors Ds) n,if D∈Ds r then cost r D else 0)

section Physical
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainBufferedSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- One actual selector for the complete ordinary physical row family,
before any residual projector or low/high cost is considered. `Label` keeps
the original nonzero-block restriction and its previously selected allocations. -/
theorem actual_main_buffered_row_selector
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (d : Label→ SecondInputDatum α) (χ₀ : Label→ RayCharacter) (Q : Ideal O)
    (hQ : Q≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1< Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤ Z^Bmask)
    (η₀ : Character) (hQM : Q≤ M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0< e) (hT : 2< T)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    let ordinary:=fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m
    let rows:=secondLiveRows (fun l=>(ordinary l).block)
    let signed:=fun r : rows=>mainLowSignedRow second r.val.2.2.2.val
    let st:=fun r : rows=>retainedState Z Bmask hZ
      (if second then (d r.val.1).τ r.val.2.2.1⁻¹ else (d r.val.1).τ r.val.2.1) Q
      ((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C))
      (hP r.val.1) (hPN r.val.1)
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    ∃keep : ∀r : rows,(st r).radial.keep (signed r),
    ∃select : rows→ BufferIndex e,∀r : rows,
      1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re ∧
      GeometryZeroBin M H hH (st r) η₀ hQM hQη (signed r) (keep r) e T (select r) ∧
      (bufferValue e (select r)<167/200 →
        ActualLow M H hH (st r) η₀ hQM hQη (167/200) e
          (3*((select r).1.val+1:ℕ)*T) (signed r)) := by
  intro ordinary rows signed st
  have ha (r : rows) := actual_main_ordinary_row_admission (d r.val.1)
    (χ₀ r.val.1) r.val.2.1 r.val.2.2.1 Q hQ m hm hml hm2
    Z Bmask hZ second (hP r.val.1) (hPN r.val.1)
    r.val.2.2.2.val r.val.2.2.2.property
  let keep : ∀r : rows,(st r).radial.keep (signed r) := fun r=>(ha r).1
  have hp (r : rows) := actual_geometry_zero_partition M H hH (st r) η₀ hQM hQη
    (signed r) (keep r) e T he hT hβlo hβhi
  let select : rows→ BufferIndex e := fun r=>Classical.choose (hp r)
  refine ⟨keep,select,?_⟩
  intro r
  have hbin := Classical.choose_spec (hp r)
  refine ⟨(ha r).2,hbin,?_⟩
  intro hl
  apply actual_main_low_bin_admission M H hH (st r) η₀ hQM hQη (signed r)
    (keep r) e T (select r) hbin hl
  have hweight : 1≤((st r).radial.profile (normValue (signed r)/(st r).radial.scale)).re := (ha r).2
  simpa only [normValue_eq_embedding] using hweight

/-- Literal full main physical cost is exactly low plus high buffered costs.
`Label` can be the original-nonzero block subtype: it is never enlarged or
replaced, and its original first coefficient remains inside every term. -/
theorem actual_main_buffered_physical_partition
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→ SecondInputDatum α) (coefficient : Label→ℝ) (t u e : ℝ)
    (select : (secondLiveRows (fun l=>(d l).block))→ BufferIndex e) :
    let rows:=secondLiveRows (fun l=>(d l).block)
    let cost:=fun r : rows=>∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      (∑p∈Finset.univ.filter (fun p=>bufferValue e p<167/200),
        mainBufferedCostBin rows e select cost p)+
      (∑p∈Finset.univ.filter (fun p=>167/200≤ bufferValue e p),
        mainBufferedCostBin rows e select cost p) := by
  intro rows cost
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  exact main_buffered_cost_partition rows e select cost

/-- The same literal identity with globally unioned residual-projector
shells. A selector never depends on the residual ideal being paid. -/
theorem actual_main_buffered_physical_shell_partition
    (N : ℕ) (a ap : ℝ) (second : Bool)
    (d : Label→ SecondInputDatum α) (coefficient : Label→ℝ) (t u e : ℝ)
    (select : (secondLiveRows (fun l=>(d l).block))→ BufferIndex e) :
    let rows:=secondLiveRows (fun l=>(d l).block)
    let Ds:=fun r : rows=>secondResidualIdeals (fun l=>(d l).block) r.val
    let cost:=fun (r : rows) D=>mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>bufferValue e p<167/200),
          mainBufferedShellBin rows e select Ds cost n p)+
      (∑n∈selectedShells (sharedProjectors Ds),
        ∑p∈Finset.univ.filter (fun p=>167/200≤ bufferValue e p),
          mainBufferedShellBin rows e select Ds cost n p) := by
  intro rows Ds cost
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort rows]
  apply main_buffered_projector_partition rows e select Ds _ cost
  intro r D hD
  change D∈secondResidualIdeals (fun l=>(d l).block) r.val at hD
  rw [actual_second_residual_ideals_label] at hD
  exact (Finset.mem_filter.mp hD).2
end Physical
end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_buffered_cost_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_buffered_projector_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_buffered_physical_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_buffered_physical_shell_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_buffered_row_selector

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainBufferedPartition -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighActualShell; sha256 171c22335fc5f393db200cd16d39de65cd36d8b33ddd2e71c952597d2493c798 -/
section
                                                       
                                                         

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentSectorLocalization
open ActualEisensteinCubic
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O

open CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit

/-- Literal retained second rows supply the frequency coordinate, including
reflection. Fixed unit costs are absorbed before sources and labels move. -/
theorem eventual_geometry_literal_high_frequency
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (b εfreq : ℝ)(N : ℕ)(hb : 0< b)(hε : 0<εfreq) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧
    ∀{α DataLabel : Type}[Fintype α][DecidableEq α][Fintype DataLabel],
    ∀(reflected second : Bool)(s : Input α)(R seed : Ideal O)(D ξ : ℝ)(hK : 0< Z^D)
      (bin : ℤ×(Fin 5→ℤ))
      (column : FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
      (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
      (row : secondLiveRows (fun l=>(datum l).block))
      (hfirst : first row.val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin column)
      (ampExponent reserveShift εvolume : ℝ),
    ξ≤εfreq →
    (datum row.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected (Z^D) (volume s) Z ξ (3*ampExponent) reserveShift b N
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin column)) Z ξ →
    let left:=!reflected
    let unit:=fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
    let hf:=geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK
      bin column datum first row hfirst
    let key₀:=secondEncodedNonzeroRow (fun l=>(datum l).block) first row left u₀ unit hf
    let key:=if second then reflectedNonzeroJointLabel key₀ else key₀
    let d₂:=datum row.val.1
    let x:=childHighCoordinates (actualHighCoordinates reflected left second
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin column) d₂.C d₂.D d₂.inactive
      Z D (Real.logb Z (volume s)) ampExponent ξ reserveShift εfreq) εvolume
    rawFrequencyNorm (nonzeroJointSourceRow key)≤ Z^(x 2) := by
  filter_upwards [eventual_actual_child_high_frequency u₀ b εfreq N hb hε] with Z hz
  refine ⟨hz.1,?_⟩
  intro α DataLabel _ _ _ reflected second s R seed D ξ hK bin column datum first row hfirst
    ampExponent reserveShift εvolume hξ hradius left unit hf key₀ key d₂ x
  have hC : Supported (first row.val.1).1.1 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).hC
  have hD : Supported (first row.val.1).1.2 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).hD
  have heq : primeSupport (first row.val.1).1.1=primeSupport (first row.val.1).1.2 := hfirst.symm ▸
    (geometryFirstSource s R seed (Z^D) Z ξ hK bin column.1).sameSupport
  have hret:=actual_second_live_retained_weight (fun l=>(datum l).block) row.val row.property
  change retainedWeight d₂.radius (normValue
    ((commonFrequencyGenerator d₂.C d₂.D*nonunitFrequencyGenerator d₂.C d₂.D d₂.inactive)*
      row.val.2.2.2.val))≠0 at hret
  rw [hradius] at hret
  have hh:=hz.2 reflected left second (firstDictionaryUnit left η₀ u₀ F₀ R₀) key₀ hC hD heq
    (volume s) D ampExponent reserveShift ξ εvolume (volume_pos s) hξ (by
      simpa only [key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
        originalSecondBlock,hfirst] using hret)
  have hfreq : rawFrequencyNorm (nonzeroJointSourceRow key₀)≤ Z^(x 2) := by
    simpa only [x,key₀,secondEncodedNonzeroRow,secondEncodedRow,SecondInputDatum.block,
      originalSecondBlock,hfirst,rawFrequencyNorm,nonzeroJointSourceRow,normValue] using hh.2
  cases second
  · exact hfreq
  · exact (reflected_joint_norm key₀).trans_le hfreq

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint high shell payment for the literal physical child coefficient.
The zero-shell parameter β and amplifier exponent are distinct inputs. -/
theorem actual_geometry_literal_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(lo εmass εfreq εvolume : ℝ)(hlo : 0< lo)(hεmass : 0≤εmass)
    (hεfreq : 0<εfreq)(hεvolume : 0<εvolume)
    (Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(_hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(W : 𝓢(ℝ,ℂ))(D ξ : ℝ)(hK : 0< Z^D)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed (Z^D) Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (_hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (_hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed (Z^D) Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width : ℝ) (i : ℕ),
      167/200 ≤ β → β ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T → 0< width →
      Function.Injective key →
      ∀labels : Finset κ,
      let A:=Real.logb Z (volume s.toData)
      let x:=fun l=>childHighCoordinates (actualHighCoordinates reflected left second
        (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive
        Z D A ampExponent ξ reserveShift εfreq) εvolume
      let target:=(1-unmarkedDensity (2*β-1))*(frequencyLoss Z 32 ξ+reserveShift)+
        unmarkedDensity (2*β-1)*εfreq+εvolume
      (∀l∈labels,x l 2+width≤ Q) →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B → lo≤ s.lower →
      3401/100000≤ bAmpl → bAmpl≤1/25 → 0≤ D → |D|≤ B → |A|≤ B → |ampExponent|≤ B →
      |frequencyLoss Z 32 ξ+reserveShift|≤ B → εfreq≤ B → ξ≤εfreq →
      A≤ D*Cycle61.Arithmetic.totalA bAmpl → ampExponent≤ D*Cycle61.Arithmetic.amp bAmpl →
      (∀l∈labels,((datum (row l).val.1).C.absNorm:ℝ)≤ Z^B ∧
        ((datum (row l).val.1).D.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,(datum (row l).val.1).radius=frequencyRadius
        (firstMainFourierScale reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent)
          reserveShift b N (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))) Z ξ) →
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (_hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (_hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (_hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, β ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      let C₁:=fun l=>geometryColumnIdeal reflected s R seed (Z^D) Z ξ hK bin (column l)
      let χ₁:=fun l=>geometryColumnCharacter reflected s R seed (Z^D) Z ξ hK bin (column l)
      ∀(B₁ : ∀l,actualAllocations s.pools (C₁ l))(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) R s.ν s.W s.P≠0) →
      let firstChild:=fun l=>child s (C₁ l) R (B₁ l) (χ₁ l) (t₁ l)
      let coeff:=fun l=>Z^(-ampExponent)*
        (firstMainRadius reflected (Z^D) (volume s.toData) Z ξ (3*ampExponent) reserveShift
          (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l))/volume (firstChild l))*
        (normalizer (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).inactive/
          Z^(Real.logb Z ((if second then (datum (row l).val.1).D
            else (datum (row l).val.1).C).absNorm:ℝ)))
      let E:=fun l=>if second then (datum (row l).val.1).D else (datum (row l).val.1).C
      let R₂:=fun l=>(datum (row l).val.1).R
      ∀(pick : ∀l,actualAllocations (firstChild l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      pad≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R₂ l)
        (firstChild l).ν (firstChild l).W (firstChild l).P≠0) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<β+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (firstChild l) (st l).character (t l)) (E l) (R₂ l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      pad+2*P.εplain*P.d+2*P.εslot*P.d*(N:ℝ)≤ rawError →
      (∑l∈labels,geometryFirstHighMass reflected s R seed W D Z ξ εmass hK bin (column l)*
        coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*
      ((Finset.Icc (⌊-(37*B+|εvolume|)/width⌋:ℤ) ⌊(37*B+|εvolume|)/width⌋).card^4:ℕ)*
        (C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
          Z^(target-D*(781136071/45083880000000)+4*width+loss+rawError+allowance+B*εmass)) := by
  obtain ⟨bound,hbound,J,hpaid⟩ := actual_geometry_paid_binned_high_shell
    (α:=α) (bp:=bp) M H hH η₀ u₀ F₀ R₀ hu₀ B Q loss ε hB hQ hQB hloss hε hap
    N lo εmass hlo hεmass Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hpaid P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint,eventual_actual_child_high_coefficient N lo εvolume hlo hεvolume,
    eventual_geometry_literal_high_frequency η₀ u₀ F₀ R₀ hu₀ b εfreq N
      (zero_lt_one.trans_le hb) hεfreq] with Z he hcoef hfrequency
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key β ampExponent reserveShift bAmpl rawError allowance Kcontrol T width i hβ hβ'
    hKcontrol hT hwidthbin hinj labels A x target hq hseed hz₁ hz₂ hsource hlower
    hbAmpl hbAmpl' hD hDbox hAbox hampbox hω hεbox hξ hA hamp hsecond hradius
    st hQM hQη z hz hchar hpuncture hrow hzero hsupport hi hcard hM hb₁ hb₂ hupperB hwin
    C₁ χ₁ B₁ t₁ hf₁ firstChild coeff E R₂ pick t w σ v θ p Ds cap
    hcap hmatches hscales hpadallow hf₂ hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq
    hW hDs hdyad src hcontrol hrawError
  have hZ : 1< Z := by linarith [he.1]
  have hδ : Cycle61.Arithmetic.q0≤2*β-1 ∧ 2*β-1≤3/4 := by
    norm_num [Cycle61.Arithmetic.q0]; constructor <;> linarith
  have hgeo (l : κ)(hl : l∈labels) := actual_geometry_compensated_high_gates s R seed (Z^D) Z ξ hK
    bin (column l) (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
    D A ampExponent reserveShift εfreq εvolume B bAmpl (2*β-1) hZ hB hseed hz₁ hz₂ hsource
    (hsecond l hl) hDbox hAbox hampbox hω (by rw [abs_of_pos hεfreq]; exact hεbox)
    ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp
  have hx (l : κ)(hl : l∈labels) : ∀j,-(32*B+|εvolume|)≤ x l j ∧ x l j≤32*B+|εvolume| := by
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val
    exact (actual_geometry_high_coordinate_gates s R seed (Z^D) Z ξ hK bin (column l)
      (datum (row l).val.1) reflected left second (datum (row l).val.1).inactive
      D A ampExponent reserveShift εfreq εvolume B bAmpl (2*β-1) hZ hB
      ⟨(hn 0).2,(hn 1).2⟩ (hsecond l hl) hDbox hAbox hampbox hω
      (by rw [abs_of_pos hεfreq]; exact hεbox) ⟨hbAmpl,hbAmpl'⟩ hδ hD hA hamp).2.1
  have hcoeff (l : κ)(hl : l∈labels) : coeff l≤ Z^(x l 0) := by
    have hC:Supported (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).hC
    have hD':Supported (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).hD
    have hsup:primeSupport (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1=
      primeSupport (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2 :=
      (geometryFirstSource s R seed (Z^D) Z ξ hK bin (column l).1).sameSupport
    exact hcoef.2 s hcard hlower reflected left second
      (geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)) hC hD' hsup R (B₁ l) (χ₁ l) (t₁ l)
      (hf₁ l hl) (datum (row l).val.1).C (datum (row l).val.1).D (datum (row l).val.1).hC
      (datum (row l).val.1).inactive D ampExponent ξ reserveShift εfreq
  have hpoint (l : κ)(hl : l∈labels) : highExponentValue (2*β-1) (x l)≤
      geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)+
        target-D*(781136071/45083880000000) := by
    have hh:=(hgeo l hl).2.2
    rw [compensated_high_exponent] at hh
    change highExponentValue (2*β-1) (x l)-
      geometryHighSide reflected A (geometryExponents s R seed (Z^D) Z ξ (column l).1.val)≤
        target-D*(781136071/45083880000000) at hh
    linarith
  have hnorm (l : κ)(hl : l∈labels) :
      ((key l).val.1.1.1.absNorm:ℝ)≤ Z^B ∧ ((key l).val.1.1.2.absNorm:ℝ)≤ Z^B ∧
      ((key l).val.2.1.1.absNorm:ℝ)≤ Z^B ∧ ((key l).val.2.1.2.absNorm:ℝ)≤ Z^B := by
    have hn:=actual_geometry_norm_caps s R seed (Z^D) Z ξ B hseed hz₁ hz₂ hsource (column l).1.val
    have h₁ : ((geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.1.absNorm:ℝ)≤ Z^B ∧
      ((geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l)).1.2.absNorm:ℝ)≤ Z^B := ⟨(hn 0).2,(hn 1).2⟩
    cases second <;> simpa only [key,rawKey,secondEncodedNonzeroRow,secondEncodedRow,
      reflectedNonzeroJointLabel,reflectedJointLabel,SecondInputDatum.block,originalSecondBlock,
      Bool.false_eq_true,ite_false,ite_true,hfirst] using ⟨h₁.1,h₁.2,(hsecond l hl).1,(hsecond l hl).2⟩
  have hmissing (l : κ)(hl : l∈labels) : ((firstSourceMissing left (key l).val.1).absNorm:ℝ)≤ Z^(x l 1) := by
    have hk : (key l).val.1=geometryFirstLabel s R seed (Z^D) Z ξ hK bin (column l) := by
      cases second <;> exact hfirst l
    rw [hk]
    have hh:=(hgeo l hl).1
    simpa only [x,compensatedHighCoordinates,childHighCoordinates,show (1:Fin 4)≠0 by decide,
      ite_false,add_zero] using hh.le

  have hzero' (l : κ)(hl : l∈labels) : rawFrequencyNorm (nonzeroJointSourceRow (key l))≤ Z^(x l 2) ∧
      β≤ HeckeDetectorZeros.zeroMaximum (wholeSourceFamily M H hH η₀
        (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
          (st l).puncture)) (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) _) (3*(i+1:ℕ)*Z^P.τ) := by
    exact ⟨hfrequency.2 reflected second s R seed D ξ hK bin (column l) datum first (row l)
      (hfirst l) ampExponent reserveShift εvolume hξ (hradius l hl),hzero l hl⟩
  have hmask (l : κ)(_hl : l∈labels) : (st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
      idealGenerator (R₂ l*E l) := by
    simp only [NaturalState.mask,hpuncture l]
    rfl
  have hledger (l : κ)(hl : l∈labels) :
      (2*β-1)*(A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤(2*β-1)*x l 3+rawError := by
    have hcards : (Fintype.card α:ℝ)≤ N := Nat.cast_le.mpr hcard
    have hp : 0≤2*P.εslot*P.d := mul_nonneg
      (mul_nonneg (by norm_num : (0:ℝ)≤2) P.hεs.le) P.hd.le
    have hh:=mul_le_mul_of_nonneg_left hcards hp
    have hraw : pad+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ rawError := by linarith
    have hx3 : x l 3=A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ) := by
      change (A-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ))+0=_
      exact add_zero _
    rw [hx3]
    linarith
  have hh:=he.2 reflected second s hη R seed W D ξ hK bin column datum first row hparent hfirst hR ψ
    β rawError allowance Kcontrol T width (32*B+|εvolume|) target (D*(781136071/45083880000000)) i
    hβ hβ' hKcontrol hT hwidthbin hinj labels x coeff hx hq hcoeff hpoint
    hseed hz₁ hz₂ hsource hAbox hlower st hQM hQη z hz hchar hpuncture hrow hzero' hsupport hnorm
    hmissing hi hcard hM hb₁ hb₂ hupperB hwin C₁ (fun _=>R) B₁ χ₁ t₁ hf₁ E R₂ pick t w σ v θ p Ds cap A
    hcap hmatches hscales (by exact le_refl _) hpadallow hf₂ hmask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hledger
  simpa only [show 32*B+|εvolume|+5*B=37*B+|εvolume| by ring] using hh

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_literal_high_frequency
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_literal_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighActualShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighFamily; sha256 906471522062fd2703e0cceb1a9795a0cba5b970bb78ce19e82dc3c219945278 -/
section
                                                           

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentCommonPairedSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O

/-- A finite family is reduced to one maximizing representative per joint
key. The complete cost is selected, so its physical scalar stays inside the
joint sum. This statement supplies no analytic bound on that sum. -/
theorem high_family_max_selection {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→ Key)(cost : Row→ℝ)(W : ℝ)(hW : 0≤ W)
    (hc : ∀r,0≤ cost r)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤ W) :
    ∃pick : (k : Finset.univ.image key)→ Row,
      (∀k,key (pick k)=k.val) ∧ Function.Injective (fun k=>key (pick k)) ∧
      (∑r,cost r)≤ W*(∑k : Finset.univ.image key,cost (pick k)) := by
  let keys:=Finset.univ.image key
  let fiber:=fun k : Key=>Finset.univ.filter (fun r=>key r=k)
  have hn (k : keys) : (fiber k.val).Nonempty := by
    obtain ⟨r,hr,he⟩:=Finset.mem_image.mp k.property
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩
  choose pick hp hm using (fun k : keys=>Finset.exists_max_image (fiber k.val) cost (hn k))
  have hk : ∀k,key (pick k)=k.val:=fun k=>(Finset.mem_filter.mp (hp k)).2
  refine ⟨pick,hk,?_,?_⟩
  · intro k l he
    apply Subtype.ext
    exact (hk k).symm.trans (he.trans (hk l))
  · apply joint_fiber_selection key cost W _ hW hc (fun k _=>hfiber k)
    intro other hother
    apply Finset.sum_le_sum
    intro k _
    exact hm k (other k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hother k⟩)

/-- The physical second normalized column, with its source character and
reflection inherited from the literal retained row. -/
def highNormalizedRowCost {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) : ℝ :=
  let v:=d r.val.1
  let E:=if second then v.D else v.C
  let hE : Supported E:=by dsimp only [E]; split <;> first | exact v.hD | exact v.hC
  let ψ:=if second then r.val.2.2.1⁻¹ else r.val.2.1
  let z:=if second then -r.val.2.2.2.val else r.val.2.2.2.val
  ∑L∈Ds,‖normalizedColumn (withHeight v.input (v.τ ψ) t) E hE v.R v.seed L z‖^2

lemma high_normalized_row_cost_nonneg {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (second : Bool)(d : Label→ SecondInputDatum α)
    (r : secondLiveRows (fun l=>(d l).block))(t : ℝ)(Ds : Finset (Ideal O)) :
    0≤ highNormalizedRowCost second d r t Ds := by
  dsimp only [highNormalizedRowCost]
  exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)

/-- Genuine live-block fibers pay for the actual normalized columns with
the physical first scalar still inside the selected joint sum. Constants
precede the original source and every moving label. -/
theorem actual_geometry_high_normalized_family_selection (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → (Z^Dfirst)≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(εmass : ℝ)
        (height : rows→ℝ)(Ds : rows→ Finset (Ideal O)),
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * highNormalizedRowCost second datum r.val (height r) (Ds r)
      ∃pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) ∧ Function.Injective (fun j=>key (pick j)) ∧
        Function.Injective (fun j=>if second then reflectedNonzeroJointLabel (key (pick j)) else key (pick j)) ∧
        (∑r : rows,cost r)≤(D*Z^(2*ε))*(∑j : Finset.univ.image key,cost (pick j)) := by
  obtain ⟨D,hD,hrows⟩:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows] with Z hz
  intro hZ α Label _ _ _ reflected s R seed Dfirst a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf rows second W εmass height Ds key cost
  have hbnd:=hz hZ reflected s R seed (Z^Dfirst) a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows
  obtain ⟨pick,hpick,hinjpick,hsum⟩:=high_family_max_selection key cost (D*Z^(2*ε))
    (by positivity) (fun r=>mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hK bin _)
      (high_normalized_row_cost_nonneg second datum r.val (height r) (Ds r))) hbnd
  refine ⟨pick,hpick,hinjpick,?_,hsum⟩
  cases second
  · exact hinjpick
  · intro j k h
    apply hinjpick
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)

/-- Canonical retained states for a selected family, widened only in their
support ceiling. Dictionary, puncture, mask, width and retained-profile
gates follow pointwise from actual source admission. -/
theorem actual_geometry_high_family_states {ι α Label κ : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ a reserve b Mcap Bmask bΦ : ℝ)(N : ℕ)
    (hK : 0< K)(hZ : 1< Z)(hb : 0< b)(hbΦ : 2≤ bΦ)(bin : ℤ×(Fin 5→ℤ))
    (column : κ→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (datum : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (row : κ→ secondLiveRows (fun l=>(datum l).block))
    (hparent : ∀k,(datum (row k).val.1).input.η=
      geometryColumnCharacter reflected s R seed K Z ξ hK bin (column k))
    (hradius : ∀k,(datum (row k).val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin (column k))) Z ξ)
    (hfirst : ∀k,first (row k).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column k))
    (hR : ∀k,(datum (row k).val.1).R≠0)(ψ : κ→ RayCharacter)(Q M : Ideal O)
    (hQM : Q≤ M)(hQη : Q≤η₀.modulus)
    (hPN : ∀k,(((datum (row k).val.1).R*
      (if second then (datum (row k).val.1).D else (datum (row k).val.1).C)).absNorm:ℝ)≤ Z^Bmask)
    (m : κ→ O)(hm : ∀k,m k≠0)(hml : ∀k,ConcretePrimeRowBridge.goodLambda∣m k)
    (hm2 : ∀k,(2:O)∣m k)
    (hkeep : ∀k,CenteredMomentRestrictedEnergy.nonexceptional (datum (row k).val.1).input.η
      (ψ k) Q (m k) (datum (row k).val.1).block.frequency
      (if second then -(row k).val.2.2.2.val else (row k).val.2.2.2.val))
    (hwidth : ∀k,
      let src:=geometryFirstSource s R seed K Z ξ hK bin (column k).1
      let c:=Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
      let e:=Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-
        Real.logb Z (normValue (commonFrequencyGenerator (datum (row k).val.1).C (datum (row k).val.1).D))+
        Real.logb Z ((∏p∈(datum (row k).val.1).inactive,p.val).absNorm:ℝ))+
      (Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)))≤ Mcap) :
    let unit:=fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf:=fun k=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK
      bin (column k) datum first (row k) (hfirst k)
    let key₀:=fun k=>secondEncodedNonzeroRow (fun l=>(datum l).block) first (row k) (!reflected) u₀ unit (hf k)
    let key:=fun k=>if second then reflectedNonzeroJointLabel (key₀ k) else key₀ k
    let z:=fun k=>if second then -(row k).val.2.2.2.val else (row k).val.2.2.2.val
    let puncture:=fun k=>(datum (row k).val.1).R*
      (if second then (datum (row k).val.1).D else (datum (row k).val.1).C)
    let hP : ∀k,puncture k≠0:=fun k=>mul_ne_zero (hR k) (by
      split <;> first | exact (datum (row k).val.1).hD.1 | exact (datum (row k).val.1).hC.1)
    let base:=fun k=>retainedState Z Bmask hZ ((datum (row k).val.1).τ (ψ k)) Q
      (puncture k) (hP k) (hPN k) (datum (row k).val.1).radius
      (datum (row k).val.1).C (datum (row k).val.1).D (datum (row k).val.1).inactive
    let st:=fun k=>widenHighState (base k) bΦ hbΦ
    ∀k,(st k).fixedModulus≤ M ∧ (st k).fixedModulus≤η₀.modulus ∧
      (st k).character=(datum (row k).val.1).τ (ψ k) ∧ (st k).puncture=puncture k ∧
      (st k).mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator (puncture k) ∧
      (st k).width≤ Mcap ∧ (datum (row k).val.1).input.η.modulus*puncture k≠0 ∧
      ∃hz : (st k).radial.keep (z k),
        (st k).radial.profile (‖eisEmbedding (z k)‖^2/(st k).radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow (st k).character (z k) ((st k).row_ne_zero (z k) hz)).character
          (st k).puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin (column k),ψ k))
          (nonzeroJointSourceRow (key k)).val (nonzeroJointSourceRow (key k)).property).character
          ((datum (row k).val.1).input.η.modulus*puncture k)) I := by
  intro unit hf key₀ key z puncture hP base st k
  have had:=actual_geometry_high_state_admission reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed
    K Z ξ a reserve b Mcap N hK hZ hb bin (column k) datum first (row k)
    (hparent k) (hradius k) (hfirst k) (hR k) (ψ k) Bmask Q M hQM hQη (hPN k)
    (m k) (hm k) (hml k) (hm2 k) (hkeep k) (hwidth k)
  simpa only [st,widenHighState,NaturalState.mask,NaturalState.width] using had


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_family_max_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_normalized_family_selection

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_family_states

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighWeightedSelection; sha256 40aef23f4a696c6886ea5d97e91c46d9e33b1f855e05a26c7eb425b2ab2c8ae7 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                      
                                                             

set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment Cycle61HighResidual
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic
open CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle61FinalNatural
open CenteredMomentCommonPairedSource
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSecondEnergySplit
open ConcreteTraceCRT CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentAllocatedRayDictionary CenteredMomentFiniteProfileExceptional CenteredMomentCommonHeightEnvelope
local notation "O" => HeckeFamily.O

/-- Restricting a finite row family does not increase any original key
fiber. The embedding may retain original block-nonzero evidence separately. -/
theorem high_restricted_key_fiber {Row Original Key : Type*}
    [Fintype Row] [Fintype Original] [DecidableEq Key]
    (embed : Row→ Original) (hinj : Function.Injective embed)
    (key : Original→ Key) (W : ℝ)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤ W) :
    ∀k,((Finset.univ.filter (fun r=>key (embed r)=k)).card:ℝ)≤ W := by
  intro k
  let selected := Finset.univ.filter (fun r : Row=>key (embed r)=k)
  have hsub : selected.image embed⊆Finset.univ.filter (fun r=>key r=k) := by
    intro r hr
    obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hq).2⟩
  calc
    _=((selected.image embed).card:ℝ) := by
      rw [Finset.card_image_of_injective _ hinj]
    _≤((Finset.univ.filter (fun r=>key r=k)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _≤ W := hfiber k

/-- Maximal full-cost selection on any injectively restricted ordinary or
original-nonzero family. No nonzero restricted block is required. -/
theorem high_restricted_full_cost_selection {Row Original Key : Type*}
    [Fintype Row] [Fintype Original] [DecidableEq Key]
    (embed : Row→ Original) (hinj : Function.Injective embed)
    (key : Original→ Key) (cost : Row→ℝ) (W : ℝ) (hW : 0≤ W)
    (hc : ∀r,0≤ cost r)
    (hfiber : ∀k,((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤ W) :
    ∃pick : (k : Finset.univ.image (key∘embed))→ Row,
      (∀k,key (embed (pick k))=k.val) ∧
      Function.Injective (fun k=>key (embed (pick k))) ∧
      (∑r,cost r)≤ W*(∑k : Finset.univ.image (key∘embed),cost (pick k)) := by
  exact high_family_max_selection (key∘embed) cost W hW hc
    (high_restricted_key_fiber embed hinj key W hfiber)

/-- A genuine full source-row datum admits the ordinary rows without
altering labels, rays or Fourier coordinates. The full-row identity is
structural and holds definitionally for actualSecondBlockDatum. -/
def ordinaryHighOriginalRow {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (d : Label→ SecondInputDatum α)
    (χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)) :
    secondLiveRows (fun l=>(d l).block) := by
  let z : (d r.val.1).rows := ⟨r.val.2.2.2.val,by
    rw [hrows]
    exact (Finset.mem_filter.mp r.val.2.2.2.property).1⟩
  refine ⟨⟨r.val.1,r.val.2.1,r.val.2.2.1,z⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  exact (Finset.mem_filter.mp r.property).2

@[simp] theorem ordinary_high_original_row_coordinates
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)) :
    let r₀:=ordinaryHighOriginalRow d χ Q m hrows r
    (r₀.val.1,r₀.val.2.1,r₀.val.2.2.1,r₀.val.2.2.2.val)=
      (r.val.1,r.val.2.1,r.val.2.2.1,r.val.2.2.2.val) := rfl

theorem ordinary_high_original_row_injective
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) :
    Function.Injective (ordinaryHighOriginalRow d χ Q m hrows) := by
  intro r s h
  apply Subtype.ext
  have hl : r.val.1=s.val.1:=congrArg (fun q=>q.val.1) h
  rcases r with ⟨⟨l,χr,ψr,zr⟩,hr⟩
  rcases s with ⟨⟨k,χs,ψs,zs⟩,hs⟩
  dsimp only at hl
  subst k
  have hc : χr=χs:=congrArg (fun q=>q.val.2.1) h
  have hp : ψr=ψs:=congrArg (fun q=>q.val.2.2.1) h
  have hz : zr=zs:=Subtype.ext (congrArg (fun q=>q.val.2.2.2.val) h)
  subst χs ψs zs
  rfl

/-- Encoding uses the identical original arithmetic labels and Fourier
coordinate after the ordinary inclusion. -/
@[simp] theorem ordinary_high_original_row_encoded
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block)) :
    secondEncodedRow (fun l=>(d l).block) first (ordinaryHighOriginalRow d χ Q m hrows r)=
      secondEncodedRow (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block) first r := rfl

/-- The complete normalized row cost is unchanged by the inclusion. -/
@[simp] theorem ordinary_high_original_row_cost
    {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
    (d : Label→ SecondInputDatum α)(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius)
    (r : secondLiveRows (fun l=>(ordinarySecondDatum (d l) (χ l) (Q l) (m l)).block))
    (second : Bool)(t : ℝ)(Ds : Finset (Ideal O)) :
    highNormalizedRowCost second d (ordinaryHighOriginalRow d χ Q m hrows r) t Ds=
      highNormalizedRowCost second (fun l=>ordinarySecondDatum (d l) (χ l) (Q l) (m l))
        r t Ds := rfl

/-- The full source-row identity for an actual physical second block. -/
theorem actual_high_block_full_rows {α : Type*}[Fintype α][DecidableEq α]
    (slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec Z ξ : ℝ)(hK : 0< K)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    let d:=actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
    d.rows=sourceRows d.C d.D d.inactive d.radius := rfl

/-- Genuine live-block fibers pay for the actual normalized columns with
the physical first scalar and arbitrary nonnegative outer factor inside the
selected joint sum. Constants
precede the original source and every moving label. -/
theorem actual_geometry_high_weighted_normalized_family_selection (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(b bs ε Amax Mmax ξ : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hε : 0<ε)
    (hA : 0≤ Amax)(hM : 0≤ Mmax)(hξ : 0≤ξ)(hξε : ξ≤ε) :
    ∃D : ℝ,0< D ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0< Z^Dfirst),
      Squarefree seed → Fintype.card α≤ N → Endpoints b bs bs s → volume s≤ Z^Amax → (Z^Dfirst)≤ Z^Mmax →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤ a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→ actualAllocations s.pools (C l),
      (∀l,frozenCoefficient (alloc l).val (C l) R s.ν s.W s.P≠0) →
      let slots := fun l=>liveIndices (alloc l).val
      let source := fun l=>child s (C l) R (alloc l) (χ l) t
      let first := fun l=>geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let projector := fun l=>(column l).val.2.1.val
      let Kmain := firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
      let Tsec := firstMainFourierScale reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve b N
      let hprojector := fun l=>actual_first_live_squarefree
        (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus) (column l).val (column l).property
      let hz₁ : ∀l,(source l).W₁ 0=0 := fun _=>hs₁
      let hz₂ : ∀l,(source l).W₂ 0=0 := fun _=>hs₂
      let hKm : ∀l,0< Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      let label := fun q : Index=>first q.1
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
      let hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
        fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
          hu₀ (hunit _) (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column r.val.1.1).val.1).hC
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(εmass : ℝ)
        (height : rows→ℝ)(Ds : rows→ Finset (Ideal O))
        (outer : rows→ℝ)(_houter : ∀r,0≤ outer r),
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      ∃pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) ∧ Function.Injective (fun j=>key (pick j)) ∧
        Function.Injective (fun j=>if second then reflectedNonzeroJointLabel (key (pick j)) else key (pick j)) ∧
        (∑r : rows,cost r)≤(D*Z^(2*ε))*(∑j : Finset.univ.image key,cost (pick j)) := by
  obtain ⟨D,hD,hrows⟩:=actual_geometry_high_row_fiber_bound η₀ u₀ F₀ R₀ hu₀
    N b bs ε Amax Mmax ξ hb hbs hε hA hM hξ hξε
  refine ⟨D,hD,?_⟩
  filter_upwards [hrows] with Z hz
  intro hZ α Label _ _ _ reflected s R seed Dfirst a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector Kmain Tsec
    hprojector hz₁ hz₂ hKm Index datum block label left unit hunit hf rows second W εmass height Ds outer houter key cost
  have hbnd:=hz hZ reflected s R seed (Z^Dfirst) a reserve t hK hseed hcard he hV hKM
    hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows
  obtain ⟨pick,hpick,hinjpick,hsum⟩:=high_family_max_selection key cost (D*Z^(2*ε))
    (by positivity) (fun r=>mul_nonneg
      (mul_nonneg
        (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hK bin _)
        (houter r))
      (high_normalized_row_cost_nonneg second datum r.val (height r) (Ds r))) hbnd
  refine ⟨pick,hpick,hinjpick,?_,hsum⟩
  cases second
  · exact hinjpick
  · intro j k h
    apply hinjpick
    apply Subtype.ext
    exact reflected_joint_involutive.injective (congrArg Subtype.val h)


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_high_weighted_normalized_family_selection

#print axioms OAI.SevenEighths.Cycle61InitialMass.high_restricted_key_fiber
#print axioms OAI.SevenEighths.Cycle61InitialMass.high_restricted_full_cost_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_high_original_row_injective

#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_high_original_row_encoded
#print axioms OAI.SevenEighths.Cycle61InitialMass.ordinary_high_original_row_cost
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_block_full_rows

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighWeightedSelection -/
