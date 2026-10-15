/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B117
import Submissions.cycle61_c0125139.Bundles.B119
import Submissions.cycle61_c0125139.Bundles.B135
import Submissions.cycle61_c0125139.Bundles.B154
import Submissions.cycle61_c0125139.Bundles.B159
import Submissions.cycle61_c0125139.Bundles.B169
import Submissions.cycle61_c0125139.Bundles.B170

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePhysicalSelection; sha256 6e9529f15aac3ae2a85682d34a79b8107f7e608cb42ffbc0bcf3b80ef1df8342 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                 
                                                                  

set_option autoImplicit false
set_option maxHeartbeats 180000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
local instance affinePhysicalSelectionSumDecidable {ι : Type*} [DecidableEq ι] :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Only the card field uses the ambient cap in the saved affine source record. -/
theorem geometry_affine_source_gates_actual_card {ι : Type*} [Fintype ι]
    (s : Input ι)(p : Profiles (1/4) (9/4))(N : ℕ)(Cs Z : ℝ)
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z) :
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z where
  card := le_rfl
  controls := caps.controls
  lower := caps.lower
  lo := caps.lo
  hi := caps.hi
  endpoints := caps.endpoints
  scales := caps.scales
  profile₁ := caps.profile₁
  profile₂ := caps.profile₂
  zero₁ := caps.zero₁
  zero₂ := caps.zero₂
  support₁ := caps.support₁
  support₂ := caps.support₂
  volume := caps.volume
  volumeLog := caps.volumeLog
  sourcePositive := caps.sourcePositive
  sourceCap := caps.sourceCap
  poolCap := caps.poolCap
  plain₁ := caps.plain₁
  plain₂ := caps.plain₂
  plain₃ := caps.plain₃
  plain₄ := caps.plain₄

/-- The supported allocation is selected before the complete second cost.
The original full-block filter and actual-cardinality Fourier cutoff remain literal. -/
def GeometryAffinePhysicalSelectionSpec {ι : Type} [Fintype ι] [DecidableEq ι]
    (Cs ε ξ K Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(reflected : Bool)(s : Input ι)(p : Profiles (1/4) (9/4)),
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
  ∀(amp reserve height : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
  ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hK key) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key j.val
  let mass:=fun j : rows=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z ξ ε hK key j.val
  (∀{Label : Type}[Fintype Label](column : Label → rows),
    Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hK key (column j).val,
      (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→ actualAllocations s.pools (C (column j)),
    (∀j,frozenCoefficient (alloc j).val (C (column j)) 1 s.ν s.W s.P≠0) →
    (∑j : Label,mass (column j)*geometryMainFirstCost reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
      ⟨column j,alloc j⟩)≤ E) →
  let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) height
    (Fintype.card ι) hZ key hz₁ hz₂
  let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m j.val
  let w:=fun j : selected=>geometryMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key 1 (Real.logb Z (volume s.toData))
    (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
  secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    (K*Z^ε)*E

/-- All constants and thresholds precede the live subset and source.
The caps record supplies every physical source gate of the selection theorem. -/
theorem uniform_actual_affine_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (Cs ε ξ : ℝ)(hCs : 1≤ Cs)(hε : 0<ε)(hξ : 0≤ξ) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,∀T : Finset α,
      GeometryAffinePhysicalSelectionSpec (ι:=T) Cs ε ξ K Z := by
  have data (T : Finset α) := actual_geometry_main_physical_selection (α:=T)
    (Fintype.card T) Cs (9/4) ε 2 2 3 ξ 1 (1/4)
    hCs hε (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num) (by norm_num)
  choose K hK hpaid using data
  let total:=1+∑T : Finset α,K T
  have hn : ∀T : Finset α,0≤ K T := fun T=>(hK T).le
  have ht : 0< total := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hn T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : K T≤ total := by
    have hh:=Finset.single_le_sum (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=>hn T)
      (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total,ht,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpaid] with Z hz
  intro T
  unfold GeometryAffinePhysicalSelectionSpec
  intro hZ reflected s p caps amp reserve height key Ψ χ Q m W second t₀ u E hz₁ hz₂
    hKfirst rows C mass hselected selected datum w
  have hKi : (Z^(1:ℝ))⁻¹≤ Z^(2:ℝ) := by
    rw [Real.rpow_one]
    exact (inv_le_one_of_one_le₀ hZ.le).trans (Real.one_le_rpow hZ.le (by norm_num))
  have hlo : (1:ℝ)≤ s.lower := le_of_eq caps.lower.symm
  have hbound := hz T hZ reflected s 1 1 1 amp reserve height caps.card caps.controls
    squarefree_one hz₁ hz₂ caps.sourcePositive caps.sourceCap caps.volume hKi hlo
    caps.support₁ caps.support₂ key Ψ χ Q m W second t₀ u E hselected
  have hE : 0≤ E := by
    have hh:=hselected (fun j : Fin 0=>Fin.elim0 j)
      (fun j k _=>Fin.elim0 j) (fun j=>Fin.elim0 j) (fun j=>Fin.elim0 j)
    simpa using hh
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hle T) (Real.rpow_nonneg (zero_lt_one.trans hZ).le ε)) hE

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_affine_source_gates_actual_card
#print axioms OAI.SevenEighths.Cycle61InitialMass.uniform_actual_affine_physical_selection

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffinePhysicalSelection -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryFinalLowLoss; sha256 50cdc63e128c86731947620c3bd4857842672194849621246c669e164eb1eafe -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- The shared final dictionary rate pays the literal low consumer and its
remaining finite fees. The mesh and old-moment rate precede the dictionary. -/
theorem geometry_final_low_loss_budget
    (μ d Bmass Bnorm U B Lproj omega mesh fees : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤ d) (hm : 0≤ Bmass) (hn : 0≤ Bnorm)
    (hU : 0≤ U) (hB : 0≤ B) (hL : 0≤ Lproj)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8)
    (hfees : fees≤8*geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N) :
    let δ:=geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    μ/8+μ/128+μ/8+2*δ*d*N+
      (2*Cycle61.Arithmetic.q0/9)*(omega+μ/8)+Cycle61.Arithmetic.q0*mesh+
      μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+fees≤2*μ := by
  intro δ
  have rates:=geometry_final_dictionary_budgets μ d Bmass Bnorm U B Lproj N
    hμ hd hm hn hU hB hL
  have hb:=rates.2.2.2.2.1
  change 2*δ*d*N+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤μ at hb
  change fees≤8*δ at hfees
  norm_num only [Cycle61.Arithmetic.q0]
  linarith

/-- Width one and the actual common rate: the five low-consumer unit fees
leave three more unit fees for physical selection, ratio bins and prime
averaging. The amplifier exponent cancels exactly once. -/
theorem geometry_final_main_low_consumer_ledger
    (μ d Bmass Bnorm U B Lproj omega mesh amp : ℝ) (N : ℕ)
    (hμ : 0<μ) (hd : 0≤ d) (hm : 0≤ Bmass) (hn : 0≤ Bnorm)
    (hU : 0≤ U) (hB : 0≤ B) (hL : 0≤ Lproj)
    (hω : omega≤33*μ/128) (hmesh : mesh≤μ/8) :
    let δ:=geometryFinalDictionaryRate μ d Bmass Bnorm U B Lproj N
    let error:=μ/8+μ/128-(7/30000000:ℝ)+μ/8+2*δ*d*N+
      (2*Cycle61.Arithmetic.q0/9)*(omega+μ/8)+Cycle61.Arithmetic.q0*mesh+μ/8
    let target:=Bmass*δ+amp+error+δ+Bnorm*δ+δ+δ+
      (δ+3*(((N:ℝ)+2)*U)*δ)+δ
    target+δ+δ+δ-amp≤-(7/30000000:ℝ)+2*μ := by
  intro δ error target
  have hb:=geometry_final_low_loss_budget μ d Bmass Bnorm U B Lproj omega mesh
    (8*δ) N hμ hd hm hn hU hB hL hω hmesh le_rfl
  dsimp only [target,error]
  change μ/8+μ/128+μ/8+2*δ*d*N+
    (2*Cycle61.Arithmetic.q0/9)*(omega+μ/8)+Cycle61.Arithmetic.q0*mesh+
    μ/8+Bmass*δ+Bnorm*δ+3*((N:ℝ)+2)*U*δ+8*δ≤2*μ at hb
  linarith only [hb]

/-- After the literal low exponent has been paid, the fixed strict saving
is uniform in the slot cardinality. -/
theorem geometry_final_main_low_exponent_saving (εaffine : ℝ) (hε : 0<εaffine) :
    -(7/30000000:ℝ)+2*geometryLossUnit 1 εaffine≤-(7/60000000:ℝ) :=
  geometry_low_width_one_exponent_saving εaffine (2*geometryLossUnit 1 εaffine) hε le_rfl

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_low_loss_budget
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_main_low_consumer_ledger
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_final_main_low_exponent_saving

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryFinalLowLoss -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainAbsoluteBox; sha256 3efc012252dc573609328f92676acde6e439b1ce7246418cc9f1642c4ac38bce -/
section
                                                             
                                                      
                                                     

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CompletedGauss CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

theorem actual_geometry_main_radius_interval {α : Type}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1< Z)(hK : 0< Z^M)(hB : 0≤ B)
    (hM : |M|≤ B)(hA : |Real.logb Z (volume s)|≤ B)(ha : |a|≤ B)
    (hω : |frequencyLoss Z 32 ξ+reserve|≤ B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    Z^(-(16*B))≤ firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j) ∧
    firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)≤ Z^(16*B) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
  let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
  let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
  let A := Real.logb Z (volume s)
  have hv (i : Fin 5) : 0≤ v i ∧ v i≤ B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ hh.1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2⟩
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (CenteredMomentAmplificationChildInput.volume_pos s)).symm
  have he : Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {primeSubsetGenerator (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [first_projector_span]
  have hR : Real.logb Z (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm=v 3 := rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := rfl
  rw [hV,actual_main_radius_power reflected l src.hC src.hD src.sameSupport Z M A a ξ reserve hZ]
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  all_goals
    have hm0 (i j : Fin 5) : 0≤ max (v i-v j) 0 := le_max_right _ _
    have hmB (i j : Fin 5) : max (v i-v j) 0≤ B :=
      max_le (by linarith [(hv i).2,(hv j).1]) hB
    constructor
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).1,(abs_le.mp hM).2,(abs_le.mp ha).1,
        (abs_le.mp hω).1,(hv 0).2,(hv 1).2,(hv 3).1,(hv 4).1,hm0 0 1,hm0 1 0]
    · apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith [(abs_le.mp hA).2,(abs_le.mp hM).1,(abs_le.mp ha).2,
        (abs_le.mp hω).2,(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2,hmB 0 1,hmB 1 0]

def geometryMainAbsoluteBox (Z : ℝ)(N : ℕ)(B loss b : ℝ) : Finset (Fin 4→ℤ) :=
  secondAbsoluteBox Z (16*B) (16*B) (B+loss) (B+loss) (b^(2*N))

private theorem actual_second_absolute_box_mem {α : Type*}[Fintype α][DecidableEq α]
    (Z A D₀ B L Cr : ℝ)(hZ : 1≤ Z)(hA : 0≤ A)(hD₀ : 0≤ D₀)
    (hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr)
    (slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(hK : 0< K)
    (hKlo : Z^(-D₀)≤ K)(hKhi : K≤ Z^A)
    (hcut : frequencyRadius Tsec Z ξ≤ Cr*Z^L)(hsource : sourceRadius s≤ Z^B)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
    actualSecondDyad s R seed K Tsec Z ξ q∈secondAbsoluteBox Z A D₀ B L Cr := by
  let d := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  have hg := actual_retained_block_gates slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q
  apply Fintype.mem_piFinset.mpr
  intro i
  exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
    d.C d.D d.hC d.hD d.sameSupport d.inactive K (frequencyRadius Tsec Z ξ) (sourceRadius s)
    hK hKlo hKhi hcut hsource
    (hg.2.2.1.trans hsource) (hg.2.2.2.trans hsource) q.2.2 i

theorem eventual_actual_geometry_main_absolute_box (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hb : 1≤ b)(hbs : 1≤ bs)
    (hξ : 0≤ξ)(hξloss : ξ≤ loss)(hε : 0<ε) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ((geometryMainAbsoluteBox Z N B loss b).card:ℝ)≤ Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M a reserve t : ℝ)(hK : 0< Z^M),
      Fintype.card α≤ N → Endpoints b bs bs s → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s)|≤ B → |M|≤ B → |a|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B → 0≤ a → 0≤ reserve →
      ∀(key : ℤ×(Fin 5→ℤ))
        (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)),
      j∈firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK key) (fun _=>logAnnulus) →
      ∀alloc : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j),
      frozenCoefficient alloc.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j)
        R s.ν s.W s.P≠0 →
      let childSource := child s (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) R alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j) t
      let Kmain := firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      let Tsec := firstMainFourierScale reflected (Z^M) (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)
      ∀q : ActualSecondBlockIndex childSource
        (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) j.2.1.val Kmain Tsec Z ξ,
      actualSecondDyad childSource (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j)
        j.2.1.val Kmain Tsec Z ξ q∈geometryMainAbsoluteBox Z N B loss b := by
  have hCr : 0< b^(2*N) := pow_pos (zero_lt_one.trans_le hb) _
  obtain ⟨Cb,hCb,hcard⟩ := second_absolute_envelope_subpower
    (16*B) (16*B) (B+loss) (B+loss) (b^(2*N)) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hCr hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hcard,eventual_geometry_child_source_cap N b bs loss hb hbs hloss]
    with Z hc hs
  refine ⟨hs.1,?_,?_⟩
  · simpa only [geometryMainAbsoluteBox,second_absolute_box_card] using hc
  intro α _ _ reflected s R seed M a reserve t hK hn hend hseed hz₁ hz₂ hsource hA hM ha hω
    ha0 hreserve key j hj alloc halloc childSource Kmain Tsec q
  have hZ : 0< Z := zero_lt_one.trans hs.1
  have hV : volume s≤ Z^B := (Real.logb_le_iff_le_rpow hs.1 (volume_pos s)).mp (abs_le.mp hA).2
  have hchild := hs.2 s B hn hend hV
    (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) R alloc
    (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK key j) t halloc
  have hradius := actual_geometry_main_radius_interval reflected s R seed M Z ξ a reserve B
    hs.1 hK hB hM hA ha hω hseed hz₁ hz₂ hsource key j
  have hcut := actual_geometry_main_cutoff_cap reflected s R seed (Z^M) Z ξ (3*a) reserve b M
    N hK hs.1 (zero_lt_one.trans_le hb) hξ (by positivity) hreserve le_rfl key j
  have hcut' : frequencyRadius Tsec Z ξ≤ b^(2*N)*Z^(B+loss) := by
    apply hcut.trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hb) _)
    exact Real.rpow_le_rpow_of_exponent_le hs.1.le (by linarith [(abs_le.mp hM).2])
  exact actual_second_absolute_box_mem Z (16*B) (16*B) (B+loss) (B+loss) (b^(2*N)) hs.1.le
    (by positivity) (by positivity) (by positivity) (by positivity) hCr
    (liveIndices alloc.val) childSource (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK key j) j.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK key)
      (fun _=>logAnnulus) j hj) hz₁ hz₂ Kmain Tsec ξ
    (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ _)
    hradius.1 hradius.2 hcut' hchild q

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_radius_interval
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_main_absolute_box

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainAbsoluteBox -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryCoarseSidePayment; sha256 56bb9a04bc5ec2e573f06ba54a92bbf0a7def5d9a1c8377d2f0950dc0eedc303 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Restore the outer physical side factor in a coarse bound. The extra
scale power is used only on the coarse branch of height extension. -/
theorem geometry_coarse_side_unit (reflected : Bool) (C Z B : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hC : 0< C) (hZ : 1≤ Z) (hB : 0≤ B)
    (hlo : 1≤2*geometryDCompensator key)
    (hhi : geometryDCompensator key≤ Z^B) :
    1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B := by
  have hz : 1≤ Z^B:=Real.one_le_rpow hZ hB
  have hh : 0< geometryDCompensator key:=geometryDCompensator_pos key
  have hc : 1≤1+C⁻¹^2:=by nlinarith [sq_nonneg C⁻¹]
  cases reflected
  · simp only [geometryHighFactor,Bool.false_eq_true,ite_false]
    have he : (1+C⁻¹^2)*(2*C^2*geometryDCompensator key)=
        2*(C^2+1)*geometryDCompensator key := by field_simp
    rw [he]
    have hone : 1≤2*(C^2+1)*geometryDCompensator key := by
      nlinarith [mul_nonneg (sq_nonneg C) hh.le]
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sub_nonneg.mpr hz)]
  · simp only [geometryHighFactor,ite_true]
    have he : 1≤(geometryDCompensator key)⁻¹*Z^B := by
      rw [←div_eq_inv_mul]
      exact (le_div_iff₀ hh).mpr (by simpa using hhi)
    have hm : 1≤(1+C⁻¹^2)*((geometryDCompensator key)⁻¹*Z^B) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]
    simpa only [mul_assoc] using hm

/-- Actual nonempty first geometry supplies both compensator bounds. No
extra restriction on moving Mellin heights is needed. -/
theorem actual_geometry_coarse_side_unit {ι : Type*} [Fintype ι]
    (reflected : Bool) (C : ℝ) (hC : 0< C)
    (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 1≤ Z) (hB : 0≤ B) (hs : Squarefree seed)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (key : ℤ×(Fin 5→ℤ)) (q : CommonGeometryFiber s R seed K Z ξ key) :
    1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B := by
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val 1
  have hd:=actual_geometry_D_compensation s R seed K Z ξ B hs hz₁ hz₂ hsource key q
  exact geometry_coarse_side_unit reflected C Z B key hC hZ hB
    (hn.1.trans hd.2.le) (hd.1.trans hn.2)

/-- Reinsert the side factor before extending heights, increasing the
coarse exponent only. Small-height exponents keep their strict saving. -/
theorem geometry_coarse_side_bound (reflected : Bool) (C Z B coarse E K control : ℝ)
    (key : ℤ×(Fin 5→ℤ)) (hZ : 0< Z) (hK : 0≤ K) (hc : 0≤ control)
    (hunit : 1≤(1+C⁻¹^2)*geometryHighFactor reflected C key*Z^B)
    (hbound : E≤ K*control*Z^coarse) :
    E≤(K*(1+C⁻¹^2))*control*geometryHighFactor reflected C key*Z^(coarse+B) := by
  have hm:=mul_le_mul_of_nonneg_left hunit
    (mul_nonneg (mul_nonneg hK hc) (Real.rpow_nonneg hZ.le coarse))
  rw [mul_one] at hm
  apply hbound.trans
  convert hm using 1
  rw [Real.rpow_add hZ]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_coarse_side_unit
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_coarse_side_unit
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_coarse_side_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryCoarseSidePayment -/
