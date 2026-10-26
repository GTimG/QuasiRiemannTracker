/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorAbsoluteBox
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorOrdinaryContraction
import Candidate.Cycle63.Physical.InitialMass.SecondRatioBox
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondBlockAggregate
open CenteredMomentFirstCanonicalFamily Cycle63Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
open CenteredMomentAllocatedChildCapacity CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

/-- Every allocation decreases raw volume when all original slot scales
are at least one. No frozen-coefficient support is required. -/
theorem geometry_common_volume_le_of_scales {ι : Type*}[Fintype ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (hP : ∀i,1≤s.P i) : volume (child s C R B τ t)≤volume s := by
  rw [common_volume]
  exact div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le
    (common_reduction_ge_one s C B hP)

/-- The unpruned twice-child envelope covers unsupported first
allocations too. The active extracted allocation is lifted before use. -/
theorem geometry_twice_source_cap_of_scales {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤b)(hbs : 1≤bs)
    (s : Input ι)(hn : Fintype.card ι≤N)(hend : Endpoints b bs bs s)(hP : ∀i,1≤s.P i)
    (C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character)(v : ℝ) :
    sourceRadius (twiceChild s C R B τ t Q k Bp υ v)≤(b^N*bs*bs)*volume s := by
  have hv₁:=geometry_common_volume_le_of_scales s C R B τ t hP
  have hp₁:=child_slot_scale_ge_one s hP C R B τ t
  have hv₂:=geometry_common_volume_le_of_scales (child s C R B τ t)
    (Q^k) (R*C) Bp υ v hp₁
  have he₁:=endpoints_child b bs bs s hend C R B τ t
  have he₂:=endpoints_child b bs bs (child s C R B τ t) he₁ (Q^k) (R*C) Bp υ v
  have hn₂: Fintype.card (liveIndices Bp.val)≤N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hn)
  have hr:=(radius_bound N b bs bs hb hbs hbs
    (twiceChild s C R B τ t Q k Bp υ v) hn₂ he₂).2
  exact hr.trans (mul_le_mul_of_nonneg_left (hv₂.trans hv₁) (by positivity))

/-- The threshold absorbs only a fixed profile envelope, before all
sources, allocations, characters and the two independent heights. -/
theorem eventual_geometry_error_child_source_cap_of_scales (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (s : Input α)(A : ℝ),Fintype.card α≤N → Endpoints b bs bs s →
      (∀i,1≤s.P i) → volume s≤Z^A →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
        (Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s C R B τ t).pools (Q^k))
        (υ : Character)(v : ℝ),
      sourceRadius (twiceChild s C R B τ t Q k Bp υ v)≤Z^(A+loss) := by
  filter_upwards [(tendsto_rpow_atTop hloss).eventually
    (eventually_ge_atTop (b^N*bs*bs)),eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  intro α _ _ s A hn hend hP hV C R B τ t Q k Bp υ v
  calc
    _≤(b^N*bs*bs)*volume s:=geometry_twice_source_cap_of_scales N b bs hb hbs
      s hn hend hP C R B τ t Q k Bp υ v
    _≤Z^loss*Z^A:=mul_le_mul hg hV (CenteredMomentAmplificationChildInput.volume_pos s).le
      (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=Z^(A+loss):=by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

set_option maxHeartbeats 1600000 in
/-- One fixed box covers all literal extracted sources, allocations,
heights and second blocks. The Fourier scale uses card α, not its cap N. -/
theorem eventual_actual_geometry_error_absolute_box_of_scales (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hb : 1≤b)(hbs : 1≤bs)
    (hξ : ξ≤loss)(hε : 0<ε) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ((geometryErrorAbsoluteBox Z N B loss b).card:ℝ)≤Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M amp reserve t : ℝ)(hZ : 1<Z),
      Fintype.card α≤N → Endpoints b bs bs s → (∀i,1≤s.P i) → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      |Real.logb Z (volume s)|≤B → |M|≤B → |amp|≤B →
      |frequencyLoss Z 32 ξ+reserve|≤B →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      ∀(p : O),p≠0 → ∀(i : Fin 3),
      ∀(Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) (υ : Character)(v : ℝ),
      let extracted:=geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
      let rad:=geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i
      let fourier:=geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i
      let Rsecond:=(R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
      Z^(-(16*B))≤rad ∧ rad≤Z^(16*B) ∧ sourceRadius extracted≤Z^(B+loss) ∧
        frequencyRadius fourier Z ξ≤b^(2*N)*Z^(18*B+loss) ∧
        ∀z : ActualSecondBlockIndex extracted Rsecond q.1.val.2.1.val rad fourier Z ξ,
          actualSecondDyad extracted Rsecond q.1.val.2.1.val rad fourier Z ξ z∈
            geometryErrorAbsoluteBox Z N B loss b := by
  have hCr : 0<b^(2*N):=pow_pos (zero_lt_one.trans_le hb) _
  obtain ⟨Cb,hCb,hcard⟩:=second_absolute_envelope_subpower
    (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) ε
    (by positivity) (by positivity) (by positivity) (by positivity) hCr hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hcard,eventual_geometry_error_child_source_cap_of_scales N b bs loss hb hbs hloss]
    with Z hc hs
  refine ⟨hs.1,?_,?_⟩
  · simpa only [geometryErrorAbsoluteBox,second_absolute_box_card] using hc
  intro α _ _ reflected s R seed M amp reserve t hZ hn hend hP hseed hz₁ hz₂
    hsource hA hM ha hω bin q p hp i Bp υ v extracted rad fourier Rsecond
  have hz0 := zero_lt_one.trans hZ
  have hK := Real.rpow_pos_of_pos hz0 M
  have hV : volume s≤Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hr := actual_geometry_error_radius_interval reflected s R seed M Z ξ amp reserve B
    hZ hK hB hM hA ha hω hseed hz₁ hz₂ hsource bin q.1.val p hp (errorIndex i+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  have hr' : Z^(-(16*B))≤rad ∧ rad≤Z^(16*B) := by
    simpa only [rad,geometryErrorSourceRadius,actual_geometry_error_tail_radius] using hr
  have hcut := actual_geometry_error_cutoff_cap N B loss b hB hloss.le hb
    reflected s R seed Z M amp ξ reserve t hZ hn hξ hV bin q p hp i hr'.1
  have hextracted : sourceRadius extracted≤Z^(B+loss) := by
    dsimp only [geometryLowFirstChild] at Bp
    dsimp only [extracted,geometryErrorChild,geometryLowFirstChild]
    exact hs.2 s B hn hend hP hV
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val) R q.2
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin q.1.val) t
      (Ideal.span {p}) (errorIndex i+1)
      (errorActiveAllocation
        (child s (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin q.1.val) R q.2
          (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin q.1.val) t)
        ((Ideal.span {p})^(errorIndex i+1)) Bp) υ v
  refine ⟨hr'.1,hr'.2,hextracted,hcut,?_⟩
  intro z
  have hseed1 := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus) q.1.val q.1.property
  have hradpos := actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ bin q p i
  have hw₁ : extracted.W₁ 0=0 := by
    dsimp only [extracted,geometryErrorChild]
    exact hz₁
  have hw₂ : extracted.W₂ 0=0 := by
    dsimp only [extracted,geometryErrorChild]
    exact hz₂
  let d:=actualSecondBlockDatum _ extracted Rsecond q.1.val.2.1.val hseed1 hw₁ hw₂ rad fourier Z ξ hradpos z
  have hg:=actual_retained_block_gates _ extracted Rsecond q.1.val.2.1.val hseed1 hw₁ hw₂ rad fourier Z ξ hradpos z
  apply Fintype.mem_piFinset.mpr
  intro c
  exact actual_second_dyads_absolute Z (16*B) (16*B) (B+loss) (18*B+loss) (b^(2*N)) hZ.le
    (by positivity) (by positivity) (by positivity) (by positivity) hCr
    d.C d.D d.hC d.hD d.sameSupport d.inactive rad (frequencyRadius fourier Z ξ) (sourceRadius extracted)
    hradpos hr'.1 hr'.2 hcut hextracted (hg.2.2.1.trans hextracted) (hg.2.2.2.trans hextracted) z.2.2 c

attribute [local instance] geometryErrorOrdinaryContractionDecidable
open CenteredMomentPrimeElements RayFourExpansion

private theorem geometry_error_second_datum_dyad {α : Type*} [Fintype α] [DecidableEq α] (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
    (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
    (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v) :
    (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.dyad=
      fun c : Fin 4=>(n.2.2 c:ℤ) := by
  rfl

private theorem geometry_error_dyad_mem_of_block_eq {stored raw : SecondBlockSource}
    {dyad : Fin 4→ℤ} {box : Finset (Fin 4→ℤ)}
    (he : stored=raw) (hd : raw.dyad=dyad) (hm : dyad∈box) : stored.dyad∈box := by
  rw [he,hd]
  exact hm

@[instance_reducible]
private def geometry_joint_error_selected_fintype {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
 : Fintype (GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) :=
  inferInstance

private def geometry_joint_error_raw_dyad {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
 : Fin 4→ℤ :=
  actualSecondDyad
      (geometryErrorChild reflected s R seed Z M ξ t hZ key j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
        (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t)
      ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key j.1.1.1.val)*
        (Ideal.span {j.1.2.1.val})^(errorIndex j.1.2.2.1+1)) j.1.1.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      Z ξ j.2.val

private theorem geometry_joint_error_dyad_box {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (j : GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (box : Finset (Fin 4→ℤ))
    (hmem : actualSecondDyad
      (geometryErrorChild reflected s R seed Z M ξ t hZ key j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
        (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t)
      ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key j.1.1.1.val)*
        (Ideal.span {j.1.2.1.val})^(errorIndex j.1.2.2.1+1)) j.1.1.1.val.2.1.val
      (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ key j.1.1 j.1.2.1.val j.1.2.2.1)
      Z ξ j.2.val∈box) :
    (@SecondInputDatum.block α inferInstance (secondDatumReindexDecidable (ι:=α))
      (geometryJointErrorDatum (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂ j)).dyad∈box := by
  have he:=geometry_joint_error_datum_block (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂ j
  have hr:=geometry_error_second_datum_dyad (α:=α) reflected s R seed Z M amp ξ reserve b t
    (Fintype.card α) hZ key j.1.1 j.1.2.1.val j.1.2.2.1 j.1.2.2.2.2
    (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t hz₁ hz₂ j.2.val
  -- These raw blocks are identical. Supply the abstract transport arguments
  -- directly to avoid expanding dependent sources during Meta inference.
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let he ← Lean.Meta.getFVarFromUserName `he
      let hr ← Lean.Meta.getFVarFromUserName `hr
      let hm ← Lean.Meta.getFVarFromUserName `hmem
      let box ← Lean.Meta.getFVarFromUserName `box
      let t1 ← Lean.instantiateMVars (← he.fvarId!.getDecl).type
      let t2 ← Lean.instantiateMVars (← hr.fvarId!.getDecl).type
      let a1 := t1.getAppArgs
      let a2 := t2.getAppArgs
      unless a1.size==3 && a2.size==3 do
        throwError "expected block and dyad equalities"
      unless a1[2]! == a2[1]!.getAppArgs[0]! do
        throwError "raw block transport requires identical block expressions"
      let proof := Lean.mkAppN (Lean.mkConst ``geometry_error_dyad_mem_of_block_eq)
        #[a1[1]!,a1[2]!,a2[2]!,box,he,hr,hm]
      (← Lean.Elab.Tactic.getMainGoal).assign proof
      Lean.Elab.Tactic.replaceMainGoal []

/-- A finite datum family uses its shared box for both original and ordinary ratio sums. -/
def GeometryErrorBoxRatioSpec {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
    (datum : Label→SecondInputDatum α)(box : Finset (Fin 4→ℤ))(Cb ε Z : ℝ) : Prop :=
    (∀j : Label,(datum j).block.dyad∈box) ∧
    ((secondRatioBins (fun j : Label=>(datum j).block)).card:ℝ)≤Cb*Z^ε ∧
    (∀E : ℝ,0≤E → ∀A : ℕ,
      (∑r∈secondRatioBins (fun j : Label=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^ε) ∧
    ∀(χ : Label→RayCharacter)(Q : Label→Ideal O)(m : Label→O)(E : ℝ),0≤E → ∀A : ℕ,
      (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
        E/(1+dyadicScale r)^A)≤Cb*E*Z^ε

private theorem geometry_error_box_ratio_payment {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
    (datum : Label→SecondInputDatum α)(box : Finset (Fin 4→ℤ))(Cb ε Z : ℝ)
    (mem : ∀j,(datum j).block.dyad∈box)(hbox : (box.card:ℝ)≤Cb*Z^ε) :
    GeometryErrorBoxRatioSpec datum box Cb ε Z := by
  have hcard : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤Cb*Z^ε := by
    have hcount : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤box.card := by
      exact_mod_cast second_ratio_bins_card_le_box (fun j=>(datum j).block) box mem
    exact hcount.trans hbox
  have decay (E : ℝ)(hE : 0≤E)(A : ℕ) :
      (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤Cb*E*Z^ε := by
    have hpaid:=second_ratio_decay_le_box (fun j=>(datum j).block) box mem E hE A
    have hbound:=mul_le_mul_of_nonneg_right hbox hE
    exact hpaid.trans (hbound.trans_eq (by ring))
  refine ⟨mem,hcard,decay,?_⟩
  intro χ Q m E hE A
  simpa only [ordinary_second_ratio_bins] using decay E hE A

private theorem geometry_affine_error_box_spec {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→elementPool P→Fin 3→RayCharacter→Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
 (box : Finset (Fin 4→ℤ)) (Cb ε : ℝ)
    (hcard : (box.card:ℝ)≤Cb*Z^ε)
    (raw : ∀j : GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂,
      geometry_joint_error_raw_dyad (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂ j∈box) :
    @GeometryErrorBoxRatioSpec α
      (GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
      inferInstance (Classical.decEq α)
      (geometry_joint_error_selected_fintype (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
      (geometryJointErrorDatum (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) box Cb ε Z :=
  @geometry_error_box_ratio_payment α (GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) inferInstance (Classical.decEq α)
    (geometry_joint_error_selected_fintype (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂)
    (geometryJointErrorDatum (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) box Cb ε Z
    (fun j : GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂ => geometry_joint_error_dyad_box (α:=α) reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂ j box (raw j)) hcard

/-- The literal retained error menu, including zero first weights, has one
shared ratio envelope. No energy or numerator estimate is a premise. -/
def GeometryAffineErrorRatioPaymentSpec (N : ℕ)(loss ξ ε Cb Z : ℝ) : Prop :=
  ∀{α : Type}[Fintype α](reflected : Bool)(s : Input α)(R seed : Ideal O)
    (profile : Profiles (1/4) (9/4))(Cs amp reserve t : ℝ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))
    (caps : GeometryAffineExceptionalSourceGates s profile N Cs Z),
    Squarefree seed → |amp|≤3 → |frequencyLoss Z 32 ξ+reserve|≤3 →
    ∀(P : Finset (Ideal O)),(∀p : elementPool P,p.val≠0) →
    ∀(υ : GeometryLowFirstIndex (α:=α) reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) key→elementPool P→Fin 3→RayCharacter→Character),
    @GeometryErrorBoxRatioSpec α
      (GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key P υ caps.zero₁ caps.zero₂)
      inferInstance (Classical.decEq α)
      (geometry_joint_error_selected_fintype (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key
        P υ caps.zero₁ caps.zero₂)
      (geometryJointErrorDatum (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key
        P υ caps.zero₁ caps.zero₂) (geometryErrorAbsoluteBox Z N 3 loss (9/4)) Cb ε Z

attribute [local irreducible] geometryErrorSecondDatum geometryErrorNonzeroBlocks
  geometryErrorChild geometryLowFirstChild geometryJointErrorDatum GeometryErrorBoxRatioSpec

set_option maxHeartbeats 250000 in
/-- Constants precede the actual affine source and every retained menu.
The Fourier scale still uses card α; N bounds only the fixed envelope. -/
theorem eventual_actual_geometry_affine_error_ratio_payment (N : ℕ)(loss ξ ε : ℝ)
    (hloss : 0<loss)(hξ : ξ≤loss)(hε : 0<ε) :
    ∃Cb : ℝ,0<Cb ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      GeometryAffineErrorRatioPaymentSpec N loss ξ ε Cb Z := by
  obtain ⟨Cb,hCb,hbox⟩:=eventual_actual_geometry_error_absolute_box_of_scales
    N 3 loss (9/4) (9/4) ξ ε (by norm_num) hloss (by norm_num) (by norm_num) hξ hε
  refine ⟨Cb,hCb,?_⟩
  filter_upwards [hbox] with Z hz
  refine ⟨hz.1,?_⟩
  intro α _ reflected s R seed profile Cs amp reserve t hZ key caps hseed hamp hω P hp υ
  have raw (j : GeometryJointErrorSelectedIndex (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key P υ caps.zero₁ caps.zero₂) : geometry_joint_error_raw_dyad (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key P υ caps.zero₁ caps.zero₂ j∈
      geometryErrorAbsoluteBox Z N 3 loss (9/4) := by
    have hraw:=hz.2.2 reflected s R seed (1:ℝ) amp reserve t hZ caps.card caps.endpoints
      caps.scales hseed caps.zero₁ caps.zero₂ caps.sourceCap caps.volumeLog
      (by norm_num) hamp hω key j.1.1 j.1.2.1.val (hp j.1.2.1) j.1.2.2.1 j.1.2.2.2.2
      (υ j.1.1 j.1.2.1 j.1.2.2.1 j.1.2.2.2.1) t
    exact hraw.2.2.2.2 j.2.val
  have paid:=geometry_affine_error_box_spec (α:=α) reflected s R seed Z 1 amp ξ reserve (9/4) t hZ key P υ caps.zero₁ caps.zero₂
    (geometryErrorAbsoluteBox Z N 3 loss (9/4)) Cb ε hz.2.1 raw
  exact paid

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_common_volume_le_of_scales
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_twice_source_cap_of_scales
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_error_child_source_cap_of_scales
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_error_absolute_box_of_scales

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_affine_error_ratio_payment
