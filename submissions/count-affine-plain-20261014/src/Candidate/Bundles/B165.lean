/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B146
import Candidate.Bundles.B149
import Candidate.Bundles.B154
import Candidate.Bundles.B155
import Candidate.Bundles.B156
import Candidate.Bundles.B159
import Candidate.Bundles.B161
import Candidate.Bundles.B162
import Candidate.Bundles.B163
import Candidate.Bundles.B164
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorRatioPayment; sha256 ecfff6549a384162da7ba9943bf4ce93bfe9a0ab1cabfd56a3344870564d9df7 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                            
                                                                    
                                                  
                                                                  
                                                                 

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
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
open CenteredMomentFirstCanonicalFamily Cycle61Moment
open CompletedGauss CenteredMomentLogDyadic CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentChildRows
open CenteredMomentAmplificationActiveFactor CenteredMomentFirstAnnularInput
open CenteredMomentAllocatedChildCapacity CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

/-- Every allocation decreases raw volume when all original slot scales
are at least one. No frozen-coefficient support is required. -/
theorem geometry_common_volume_le_of_scales {ι : Type*}[Fintype ι]
    (s : Input ι)(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
    (hP : ∀i,1≤ s.P i) : volume (child s C R B τ t)≤ volume s := by
  rw [common_volume]
  exact div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le
    (common_reduction_ge_one s C B hP)

/-- The unpruned twice-child envelope covers unsupported first
allocations too. The active extracted allocation is lifted before use. -/
theorem geometry_twice_source_cap_of_scales {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤ b)(hbs : 1≤ bs)
    (s : Input ι)(hn : Fintype.card ι≤ N)(hend : Endpoints b bs bs s)(hP : ∀i,1≤ s.P i)
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
  have hn₂: Fintype.card (liveIndices Bp.val)≤ N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hn)
  have hr:=(radius_bound N b bs bs hb hbs hbs
    (twiceChild s C R B τ t Q k Bp υ v) hn₂ he₂).2
  exact hr.trans (mul_le_mul_of_nonneg_left (hv₂.trans hv₁) (by positivity))

/-- The threshold absorbs only a fixed profile envelope, before all
sources, allocations, characters and the two independent heights. -/
theorem eventual_geometry_error_child_source_cap_of_scales (N : ℕ)(b bs loss : ℝ)
    (hb : 1≤ b)(hbs : 1≤ bs)(hloss : 0< loss) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{α : Type}[Fintype α][DecidableEq α]
      (s : Input α)(A : ℝ),Fintype.card α≤ N → Endpoints b bs bs s →
      (∀i,1≤ s.P i) → volume s≤ Z^A →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ)
        (Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s C R B τ t).pools (Q^k))
        (υ : Character)(v : ℝ),
      sourceRadius (twiceChild s C R B τ t Q k Bp υ v)≤ Z^(A+loss) := by
  filter_upwards [(tendsto_rpow_atTop hloss).eventually
    (eventually_ge_atTop (b^N*bs*bs)),eventually_gt_atTop (1:ℝ)] with Z hg hZ
  refine ⟨hZ,?_⟩
  intro α _ _ s A hn hend hP hV C R B τ t Q k Bp υ v
  calc
    _≤(b^N*bs*bs)*volume s:=geometry_twice_source_cap_of_scales N b bs hb hbs
      s hn hend hP C R B τ t Q k Bp υ v
    _≤ Z^loss*Z^A:=mul_le_mul hg hV (CenteredMomentAmplificationChildInput.volume_pos s).le
      (Real.rpow_nonneg (zero_le_one.trans hZ.le) _)
    _=Z^(A+loss):=by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

set_option maxHeartbeats 1600000 in
/-- One fixed box covers all literal extracted sources, allocations,
heights and second blocks. The Fourier scale uses card α, not its cap N. -/
theorem eventual_actual_geometry_error_absolute_box_of_scales (N : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hb : 1≤ b)(hbs : 1≤ bs)
    (hξ : ξ≤ loss)(hε : 0<ε) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ((geometryErrorAbsoluteBox Z N B loss b).card:ℝ)≤ Cb*Z^ε ∧
      ∀{α : Type}[Fintype α][DecidableEq α](reflected : Bool)(s : Input α)(R seed : Ideal O)
        (M amp reserve t : ℝ)(hZ : 1< Z),
      Fintype.card α≤ N → Endpoints b bs bs s → (∀i,1≤ s.P i) → Squarefree seed →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤ Z^B →
      |Real.logb Z (volume s)|≤ B → |M|≤ B → |amp|≤ B →
      |frequencyLoss Z 32 ξ+reserve|≤ B →
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
      Z^(-(16*B))≤ rad ∧ rad≤ Z^(16*B) ∧ sourceRadius extracted≤ Z^(B+loss) ∧
        frequencyRadius fourier Z ξ≤ b^(2*N)*Z^(18*B+loss) ∧
        ∀z : ActualSecondBlockIndex extracted Rsecond q.1.val.2.1.val rad fourier Z ξ,
          actualSecondDyad extracted Rsecond q.1.val.2.1.val rad fourier Z ξ z∈
            geometryErrorAbsoluteBox Z N B loss b := by
  have hCr : 0< b^(2*N):=pow_pos (zero_lt_one.trans_le hb) _
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
  have hV : volume s≤ Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hr := actual_geometry_error_radius_interval reflected s R seed M Z ξ amp reserve B
    hZ hK hB hM hA ha hω hseed hz₁ hz₂ hsource bin q.1.val p hp (errorIndex i+1)
    (Nat.succ_le_succ (Nat.zero_le _))
  have hr' : Z^(-(16*B))≤ rad ∧ rad≤ Z^(16*B) := by
    simpa only [rad,geometryErrorSourceRadius,actual_geometry_error_tail_radius] using hr
  have hcut := actual_geometry_error_cutoff_cap N B loss b hB hloss.le hb
    reflected s R seed Z M amp ξ reserve t hZ hn hξ hV bin q p hp i hr'.1
  have hextracted : sourceRadius extracted≤ Z^(B+loss) := by
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
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
 : Fintype (GeometryJointErrorSelectedIndex reflected s R seed Z M amp ξ reserve b t hZ key P υ hz₁ hz₂) :=
  inferInstance

private def geometry_joint_error_raw_dyad {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
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
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
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
    (datum : Label→ SecondInputDatum α)(box : Finset (Fin 4→ℤ))(Cb ε Z : ℝ) : Prop :=
    (∀j : Label,(datum j).block.dyad∈box) ∧
    ((secondRatioBins (fun j : Label=>(datum j).block)).card:ℝ)≤ Cb*Z^ε ∧
    (∀E : ℝ,0≤ E → ∀A : ℕ,
      (∑r∈secondRatioBins (fun j : Label=>(datum j).block),E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε) ∧
    ∀(χ : Label→ RayCharacter)(Q : Label→ Ideal O)(m : Label→ O)(E : ℝ),0≤ E → ∀A : ℕ,
      (∑r∈secondRatioBins (fun j=>(ordinarySecondDatum (datum j) (χ j) (Q j) (m j)).block),
        E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε

private theorem geometry_error_box_ratio_payment {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
    (datum : Label→ SecondInputDatum α)(box : Finset (Fin 4→ℤ))(Cb ε Z : ℝ)
    (mem : ∀j,(datum j).block.dyad∈box)(hbox : (box.card:ℝ)≤ Cb*Z^ε) :
    GeometryErrorBoxRatioSpec datum box Cb ε Z := by
  have hcard : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤ Cb*Z^ε := by
    have hcount : ((secondRatioBins (fun j=>(datum j).block)).card:ℝ)≤ box.card := by
      exact_mod_cast second_ratio_bins_card_le_box (fun j=>(datum j).block) box mem
    exact hcount.trans hbox
  have decay (E : ℝ)(hE : 0≤ E)(A : ℕ) :
      (∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A)≤ Cb*E*Z^ε := by
    have hpaid:=second_ratio_decay_le_box (fun j=>(datum j).block) box mem E hE A
    have hbound:=mul_le_mul_of_nonneg_right hbox hE
    exact hpaid.trans (hbound.trans_eq (by ring))
  refine ⟨mem,hcard,decay,?_⟩
  intro χ Q m E hE A
  simpa only [ordinary_second_ratio_bins] using decay E hE A

private theorem geometry_affine_error_box_spec {α : Type*} [Fintype α]
    (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z M amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
    (P : Finset (Ideal O))
    (υ : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key→ elementPool P→ Fin 3→ RayCharacter→ Character)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
 (box : Finset (Fin 4→ℤ)) (Cb ε : ℝ)
    (hcard : (box.card:ℝ)≤ Cb*Z^ε)
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
    (profile : Profiles (1/4) (9/4))(Cs amp reserve t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))
    (caps : GeometryAffineExceptionalSourceGates s profile N Cs Z),
    Squarefree seed → |amp|≤3 → |frequencyLoss Z 32 ξ+reserve|≤3 →
    ∀(P : Finset (Ideal O)),(∀p : elementPool P,p.val≠0) →
    ∀(υ : GeometryLowFirstIndex (α:=α) reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) 1) key→ elementPool P→ Fin 3→ RayCharacter→ Character),
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
    (hloss : 0< loss)(hξ : ξ≤ loss)(hε : 0<ε) :
    ∃Cb : ℝ,0< Cb ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_common_volume_le_of_scales
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_twice_source_cap_of_scales
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_geometry_error_child_source_cap_of_scales
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_absolute_box_of_scales

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_affine_error_ratio_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineErrorRatioPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorFullPayment; sha256 ebc5e643c19e600bd566e0a7f562f88efbaee75ab90aa73c3f63708bc3c5cec1 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                     
                                                     
                                                        
                                                              
                                                             
                                                            

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
universe u v
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentFirstSectors CenteredMomentFirstDiscardedEnergy
open CenteredMomentWholeDivisorShell CenteredMomentMobiusRegroup
open Filter Set HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentCommonPairedSource
open CenteredMomentCommonHeightEnvelope CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondHeightFamily CenteredMomentCommonProfile
open CenteredMomentHeckeColumnWindow CenteredMomentSecondRetainedRows
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondBlockAggregate CenteredMomentSecondLiveBlock
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentEligibleEnergy CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAmplificationErrorEnergy CenteredMomentRestrictedEnergy
open CenteredMomentAllocatedRayDictionary CenteredMomentSlotRatios
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Cycle61FinalNatural Cycle61Moment Cycle61FinalError Cycle61FinalErrorCapacity
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonAllocationSum
open CenteredMomentPrimeElements CenteredMomentRankinRadical
open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceMass CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentFirstAnnularInput CenteredMomentSecondRadicalBudget CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance errorFullPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


variable {α : Type*} [Fintype α] [DecidableEq α]
section Selected
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (n : GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
variable (second : Bool)

/-- The supported arithmetic label is obtained from the original physical
block, before choosing a common second allocation. -/
noncomputable def geometryErrorSupportedSecondLabel : FirstSourceLabel :=
  let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
  ⟨(d.C,d.D),⟨d.inactive,by
    exact second_block_nonzero_inactive d.block ballProfile hne⟩⟩

variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

noncomputable def geometryErrorColumnScalar
    (P : Finset (Ideal O))(weight lf error εcommon : ℝ) : ℝ :=
  let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
  let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
    (if second then d.D else d.C) d.R
    (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
  let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  ((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/volume chain.extracted)*
    Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
    (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal+error-Mrow*branchReserve chain.k)

/-- The literal post-column coefficient retains the prime denominator,
removal gain and selected source volume in the arithmetic label payment. -/
theorem actual_geometry_error_column_scalar_identity
    (P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
    let d := geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n
    let chain := geometryErrorChain reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v hp hcop
      (if second then d.D else d.C) d.R
      (geometryErrorSelectedAllocation reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second)
    let g := geometryErrorSelectedGeometry reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne second hp hcop ψ hυ hf₁
    let firstLabel := geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let secondLabel := geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n hne
    let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
    ((56/(P.card:ℝ))*weight*(K/lf)*normalizer d.C d.D d.inactive*16*((chain.k+1):ℝ)/volume chain.extracted)*
      Z^(errorRemoval chain.p Z chain.k-errorMoving chain.p Z chain.k)*
      (chain.E₂.absNorm:ℝ)^(εcommon-1)*Z^(g.nominal+error-Mrow*branchReserve chain.k)=
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
        extractedErrorLabelScalar reflected second firstLabel secondLabel Z Mrow amp
          (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) p (errorIndex i+1) := by
  intro d chain g firstLabel secondLabel K
  have hr : K=firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
      (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := rfl
  have hn : g.nominal=errorNominal Mrow Z amp (frequencyLoss Z 32 ξ+reserve)
      (errorRemoval p Z (errorIndex i+1)) (errorMoving p Z (errorIndex i+1))
      (if reflected then firstLabel.1.2 else firstLabel.1.1)
      (if reflected then firstLabel.1.1 else firstLabel.1.2)
      secondLabel.1.1 secondLabel.1.2 secondLabel.2.val := by
    cases reflected <;> rfl
  rw [hr,hn]
  have hcount : (chain.k:ℝ)+1=(errorIndex i+2:ℝ) := by
    change (↑(errorIndex i+1):ℝ)+1=(errorIndex i+2:ℝ)
    push_cast
    ring
  rw [hcount]
  exact actual_error_normalized_scalar_identity reflected second firstLabel secondLabel Z Mrow amp
    (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume chain.extracted) lf weight
    P p i (zero_lt_one.trans hZ)

end Selected

section ScalarFamily
variable {Label : Type*}[Fintype Label]
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

variable (index : Label→ GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v)
variable (hne : ∀n : Label,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n)).block.value ballProfile≠0)

/-- All second labels share the extracted source and prime denominator;
the common allocation remains fixed before both ray and residual sums. -/
theorem actual_geometry_error_column_scalar_sum
    (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ) :
    (∑n : Label,geometryErrorColumnScalar reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
      hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ P weight lf error εcommon)=
    ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)*
      ∑n : Label,extractedErrorLabelScalar reflected second
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)
        (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ (index n) (hne n))
        Z Mrow amp (frequencyLoss Z 32 ξ) reserve error εcommon
        (volume s) (volume (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)) p (errorIndex i+1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact actual_geometry_error_column_scalar_identity reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ (index n) (hne n) second hp hcop ψ hυ hf₁ P weight lf error εcommon

end ScalarFamily

section ScalarDisintegration
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (p : O) (i : Fin 3)
variable (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
          ((Ideal.span {p})^(errorIndex i+1))) (υ : Character) (v : ℝ)
variable (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
variable (hp : p≠0)
    (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
      IsCoprime (Ideal.span {p}) I)
    (ψ : RayCharacter)
    (hυ : υ.modulus.absNorm≤ radicalBound
      (childCharacter (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
      fixedBadMask p (errorMovingExponent (errorIndex i)))
    (hf₁ : frozenCoefficient q.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)

set_option linter.defProp false in
/-- Genuine second-label enlargement pays one full four-dyad box, after
the literal normalized coefficient has been restored. -/
def actual_geometry_error_scalar_disintegration
    (rows : Finset (GeometryErrorSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v))
    (hne : ∀n∈rows,(geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀n∈rows,actualSecondDyad
      (geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v)
      ((R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1))
      q.1.val.2.1.val (geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i)
      (geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i)
      Z ξ n∈box)
    (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ)
    (hweight : 0≤ weight)(hlf : 0< lf) :=
  let source := geometryErrorChild reflected s R seed Z Mrow ξ t hZ bin q p i Bp υ v
  let R₂ := (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
  let K := geometryErrorSourceRadius reflected s R seed Z Mrow amp ξ reserve hZ bin q p i
  let Tsec := geometryErrorFourierScale reflected s R seed Z Mrow amp ξ reserve b N hZ bin q p i
  let firstLabel := geometryFirstLabel s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
  let hU : ∀n∈rows,n.2.1∈inactiveSubsets n.1.val.val.1 n.1.val.val.2 :=
    fun n hn=>second_block_nonzero_inactive
      (geometryErrorSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n).block
      ballProfile (hne n hn)
  let cost := fun l=>extractedErrorLabelScalar reflected second firstLabel l Z Mrow amp
    (frequencyLoss Z 32 ξ) reserve error εcommon (volume s) (volume source) p (errorIndex i+1)
  let hseed := actual_first_live_squarefree
    (geometryFirstSource s R seed (Z^Mrow) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (fun _=>logAnnulus) q.1.val q.1.property
  let hz₁ : source.W₁ 0=0 := hw₁
  let hz₂ : source.W₂ 0=0 := hw₂
  let hcost : ∀l∈actualSecondLabels source R₂ q.1.val.2.1.val,∀n∈box,0≤ cost l := by
    intro l hl _ _
    have hg := actual_second_labels_gates source R₂ q.1.val.2.1.val hseed hz₁ hz₂ l hl
    have hn := (normalizer_pos l.1.1 l.1.2 hg.1 l.2.val).le
    have hV := (volume_pos source).le
    have hrad : 0≤ firstErrorTailRadius reflected firstLabel Z Mrow (volume s) amp
        (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := by
      unfold firstErrorTailRadius errorCommonRadius
      exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _
    dsimp only [cost]
    unfold extractedErrorLabelScalar
    positivity
  let hpaid := actual_second_positive_disintegration source R₂ q.1.val.2.1.val K Tsec Z ξ
    rows hU box hbox (fun l _=>cost l) hcost
  let hpaid' :
      (∑n : rows,cost (geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property)))≤
      (box.card:ℝ)*∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,cost l := by
    have hlabel (n : rows) :
        actualSecondSupportedLabel source R₂ q.1.val.2.1.val K Tsec Z ξ n.val (hU n.val n.property)=
        geometryErrorSupportedSecondLabel reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v hw₁ hw₂ n.val (hne n.val n.property) := rfl
    simpa only [hlabel,Finset.sum_const,nsmul_eq_mul] using hpaid
  let hsum := actual_geometry_error_column_scalar_sum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin q p i Bp υ v
    hw₁ hw₂ hp hcop ψ hυ hf₁ (fun n : rows=>n.val) (fun n=>hne n.val n.property) second P weight lf error εcommon
  let hfactor : 0≤((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf) := by positivity
  hsum.le.trans (mul_le_mul_of_nonneg_left hpaid' hfactor)

end ScalarDisintegration


private theorem error_box_factor_payment (factor card cap total : ℝ)
    (hf : 0≤ factor)(ht : 0≤ total)(hc : card≤ cap) :
    factor*(card*total)≤ cap*(factor*total) := by
  have h:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc ht) hf
  exact h.trans_eq (mul_left_comm _ _ _)

def geometryErrorScalarSubpowerConstant
    (Ncap : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hb : 1≤ b)(hbs : 1≤ bs)
    (hξ : ξ≤ loss)(hε : 0<ε) : ℝ :=
  Classical.choose (eventual_actual_geometry_error_absolute_box Ncap B loss b bs ξ ε
    hB hloss hb hbs hξ hε)

set_option linter.defProp false in
/-- Fixed source caps pay the complete second-label disintegration before
the first column, extraction menu or either height is chosen. -/
def eventual_actual_geometry_error_scalar_subpower
    (Ncap : ℕ)(B loss b bs ξ ε : ℝ)
    (hB : 0≤ B)(hloss : 0< loss)(hb : 1≤ b)(hbs : 1≤ bs)
    (hξ : ξ≤ loss)(hε : 0<ε) :=
  let data:=eventual_actual_geometry_error_absolute_box Ncap B loss b bs ξ ε
    hB hloss hb hbs hξ hε
  let hdata:=Classical.choose_spec data
  And.intro hdata.1 (hdata.2.mono fun Z hz=>And.intro hz.1 (
    fun {α : Type} [Fintype α] [DecidableEq α] (reflected : Bool)(s : Input α)(R seed : Ideal O)
      (M amp reserve t : ℝ)(hZ : 1< Z)
      (hN : Fintype.card α≤ Ncap)(hend : Endpoints b bs bs s)(hseed : Squarefree seed)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
      (hsource : sourceRadius s≤ Z^B)(hA : |Real.logb Z (volume s)|≤ B)
      (hM : |M|≤ B)(ha : |amp|≤ B)(hω : |frequencyLoss Z 32 ξ+reserve|≤ B)
      (bin : ℤ×(Fin 5→ℤ))
      (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
      (hf₁ : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) R s.ν s.W s.P≠0)
      (p : O)(hp : p≠0)(i : Fin 3)
      (hcop : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).slots j→
        IsCoprime (Ideal.span {p}) I)=>
    let firstChild:=geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q
    fun (Bp : actualAllocations (activeInput firstChild).pools ((Ideal.span {p})^(errorIndex i+1)))
      (υ : Character)(v : ℝ)(ψ : RayCharacter)
      (hυ : υ.modulus.absNorm≤ radicalBound
        (childCharacter (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val) ψ)
        fixedBadMask p (errorMovingExponent (errorIndex i)))
      (rows : Finset (GeometryErrorSecondIndex reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v))
      (hne : ∀n∈rows,(geometryErrorSecondDatum reflected s R seed Z M amp ξ reserve b t
        (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ n).block.value ballProfile≠0)
      (second : Bool)(P : Finset (Ideal O))(weight lf error εcommon : ℝ)
      (hweight : 0≤ weight)(hlf : 0< lf)=>
    let source:=geometryErrorChild reflected s R seed Z M ξ t hZ bin q p i Bp υ v
    let R₂:=(R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val)*(Ideal.span {p})^(errorIndex i+1)
    let first:=geometryFirstLabel s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin q.1.val
    let hc:=hz.2.2 reflected s R seed M amp reserve t hZ hN hend hseed hw₁ hw₂
      hsource hA hM ha hω bin q hf₁ p hp i hcop Bp υ v
    let hbox : ∀n∈rows,actualSecondDyad source R₂ q.1.val.2.1.val
        (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ bin q p i)
        (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card α) hZ bin q p i)
        Z ξ n∈geometryErrorAbsoluteBox Z Ncap B loss b := fun n _=>hc.2.2.2.2 n
    let hpaid:=actual_geometry_error_scalar_disintegration reflected s R seed Z M amp ξ reserve b t
      (Fintype.card α) hZ bin q p i Bp υ v hw₁ hw₂ hp hcop ψ hυ hf₁ rows hne
      (geometryErrorAbsoluteBox Z Ncap B loss b) hbox second P weight lf error εcommon hweight hlf
    let hseed₁:=actual_first_live_squarefree
      (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
      (fun _=>logAnnulus) q.1.val q.1.property
    let hsum : 0≤∑l∈actualSecondLabels source R₂ q.1.val.2.1.val,
        extractedErrorLabelScalar reflected second first l Z M amp (frequencyLoss Z 32 ξ)
          reserve error εcommon (volume s) (volume source) p (errorIndex i+1) := by
      apply Finset.sum_nonneg
      intro l hl
      have hg:=actual_second_labels_gates source R₂ q.1.val.2.1.val hseed₁ hw₁ hw₂ l hl
      have hn:=(normalizer_pos l.1.1 l.1.2 hg.1 l.2.val).le
      have hV:=(volume_pos source).le
      have hrad : 0≤ firstErrorTailRadius reflected first Z M (volume s) amp
          (frequencyLoss Z 32 ξ) reserve p (errorIndex i+1) := by
        unfold firstErrorTailRadius errorCommonRadius
        exact Real.rpow_nonneg (zero_lt_one.trans hZ).le _
      unfold extractedErrorLabelScalar
      exact mul_nonneg
        (mul_nonneg (div_nonneg hrad hV)
          (mul_nonneg hn (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    let hf : 0≤((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf) :=
      div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) hweight)
            (by norm_num))
          (add_nonneg (Nat.cast_nonneg _) (by norm_num))) hlf.le
    hpaid.trans (error_box_factor_payment
      ((56/(P.card:ℝ))*weight*16*(errorIndex i+2:ℝ)/lf)
      ((geometryErrorAbsoluteBox Z Ncap B loss b).card:ℝ) _ _ hf hsum hz.2.1)
  ))


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorSupportedSecondLabel
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_column_scalar_identity
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorColumnScalar
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_column_scalar_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_scalar_disintegration
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_error_scalar_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometryErrorScalarSubpowerConstant

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorFullPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowAggregate; sha256 dfa163380e4ca458e8c68043b13842d31c49ba3b4bb8c642587ac9b21cf54f3c -/
section
                                                          
                                                        
                                                             
                                                         

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle61FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate CenteredMomentSourceMass CenteredMomentRankinRadical
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle61Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open CenteredMomentWholeDivisorShell
open Cycle61FinalLow
open Cycle61Moment.LowBranch Cycle61FinalNatural Cycle61FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle61FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainLowAggregateSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The genuine uniform low-column theorem accepts the selected first
mass divided by its child volume. All second scalar factors stay inside
the complete frequency sum, before any row-independent allocation choice. -/
theorem actual_selected_low_physical_family_columns
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0< Cg ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀(hZ : 1< Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0≤ w j) → (∀j,w j≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤ Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤ hi) →
      0≤ height → (∀j,|freq j|≤ height) → 51/100≤ aLow → aLow≤167/200 →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤ Mrow → 0≤ omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤ Mcap →
      ((17/500)*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤(1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle61.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤ Cycle61.Arithmetic.B*Mrow →
    ∀(reflected : Bool)(R seed : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t _Mprice _Aprice : ℝ)
      (_sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ),
    ∀{Label : Type*}[Fintype Label][DecidableEq Label],
    ∀firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin,
    ∀q : Label→ Chain s,
    (∀l,(q l).C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).R₁=R) → (∀l,HEq (q l).B₁ (firstIndex l).2) →
    (∀l,(q l).η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).t₁=t) →
    let cell := Cycle61.Arithmetic.cellUpper (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle61.Arithmetic.amp cell
    ∀g : (l : Label)→ LiveMainGeometry s (q l) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀l,(g l).reflected=reflected) →
    (∀l,(g l).C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).C) →
    (∀l,(g l).D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).D) →
    ∀(χ : Label→ RayFourExpansion.RayCharacter)(hP : ∀l,(q l).R₂*(q l).E₂≠0)
      (hPN : ∀l,(((q l).R₂*(q l).E₂).absNorm:ℝ)≤ Z^Bmask),
    let st := fun l=>retainedState Z Bmask hZ ((g l).datum.τ (χ l)) (internalQ Q η₀)
      ((q l).R₂*(q l).E₂) (hP l) (hPN l) (g l).datum.radius (g l).datum.C (g l).datum.D (g l).datum.inactive
    let src := fun l=>withHeight (q l).first ((g l).datum.τ (χ l)) v
    let nominal := fun l=>secondNominal Mrow Z amp omega (q l).C₁ (g l).D₁
      (g l).datum.C (g l).datum.D (g l).datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(divisorSeed : Label→ Ideal O)(hE₂ : ∀l,Supported (q l).E₂),(∀l,divisorSeed l∣(q l).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤ T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      (commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.allowance Z≤ pad) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      ∀D∈Ds,∀alloc∈(commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.active D,∀second : Bool,
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 0≤ Z^L ∧
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 1≤ Z^L) →
    let low := fun l=>ActualLow M H hH (st l) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Label→ Finset O)(weight : Label→ O→ℝ),(∀l,∀z∈zs l,0≤ weight l z) →
      (∀l,∀z∈zs l,(st l).radial.keep z ∧ low l z) →
      (∀l,∀z∈zs l,weight l z≤((st l).radial.profile (‖eisEmbedding z‖^2/(st l).radial.scale)).re) →
    ∀coefficient : Label→ℝ,(∀l,0≤ coefficient l) →
    let c := fun l=>coefficient l*
      ((g l).datum.K/lowerFactor Nweight slotlo plainlo)*
      normalizer (g l).datum.C (g l).datum.D (g l).datum.inactive
    (∑l,c l*(∑D∈Ds,∑z∈zs l,weight l z*
      ‖normalizedColumn (src l) (q l).E₂ (hE₂ l) (q l).R₂ (divisorSeed l) D z‖^2))≤
      Cg*∑l,c l*((src l).toData.profileFactor*(∏j,(src l).M j)^2*
        QuadraticInitialBound.diagonalControl (st l).radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*((q l).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal l+δwidth+amp-Mrow*(1/3750000)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh)*Z^pad) := by
  obtain ⟨degree,Sp,hcolumn⟩ := actual_live_main_low_profile_column (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hzslot haff
    reflected R seed bin t Mprice Aprice sourceWeight Label _ _ firstIndex q hCq hRq hBq hηq htq
    cell amp g hgref hgC hgD χ hP hPN st src nominal δwidth padding divisorSeed hE₂ hseed
    Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight coefficient hcoefficient c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hzslot haff (q l) (g l) (χ l) (hP l) (hPN l)
    (divisorSeed l) (hE₂ l) (hseed l) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow l) (hcaps l)
    (zs l) (weight l) (hnonneg l) (hkeep l) (hweight l)
  have hc : 0≤ c l := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg
      (hcoefficient l)
      (div_nonneg (g l).datum.K_pos.le (lowerFactor_pos Nweight slotlo plainlo hslot hplain).le))
      (normalizer_pos (g l).datum.C (g l).datum.D (g l).datum.hC (g l).datum.inactive).le
  apply (mul_le_mul_of_nonneg_left hh hc).trans_eq
  ring

universe u v
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option linter.defProp false in
/-- Literal original main constructors for the selected physical low
energy. The final nonnegative coefficient is chosen by the first cost
selection, without requiring an energy bound as an input. -/
def actual_geometry_selected_low_physical_columns {α : Type u} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0< A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤ B) (ha : 0< a) (ha' : a≤1/4) (hb : 1≤ b)
    (hBmask : 0≤ Bmask) (hMcap : 0< Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤ Rwidth) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0< d) (hdsupply : Mcap+Bmask+margin≤ d) (hdm : d≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤ bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0< Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0< slotlo) (hplain : 0< plainlo) :=
  let hbase := actual_selected_low_physical_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell Nweight slotlo plainlo hslot hplain
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc := hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose hc
    let hg := Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1< Z) (s : Input α) (θ : α→ RayQuotient.Characters M H)
        (w σ freq : α→ℝ) (heightV height mesh aLow : ℝ) (i : ℕ)
        hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
        hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap'
        hzslot haff (reflected : Bool) (R seed : Ideal O) (bin : ℤ×(Fin 5→ℤ))
        (t Mprice Aprice : ℝ)
        (sourceWeight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        {Label : Type v} [Fintype Label] [DecidableEq Label]
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let cell := Cycle61.Arithmetic.cellUpper
          (Cycle61.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle61.Arithmetic.amp cell
        fun (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
        (n : (l : Label)→ GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l))=>
        let datum := fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l)
        let firstChild := fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        fun (second : Label→ Bool)
          (B₂ : (l : Label)→ actualAllocations (firstChild l).pools
            (if second l then (datum l).D else (datum l).C))
          (r : (l : Label)→ secondLiveRows (fun _:Unit=>(datum l).block))
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hf₂ : ∀l,frozenCoefficient (B₂ l).val
            (if second l then (datum l).D else (datum l).C) (datum l).R
            (firstChild l).ν (firstChild l).W (firstChild l).P≠0)=>
        let q : Label→ Chain s := fun l=>geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l)
        let g : (l : Label)→ LiveMainGeometry s (q l) Z Mrow amp
          (frequencyLoss Z 32 ξ+reserve) ξ bs (Fintype.card α) := fun l=>geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        let hfields := fun l=>actual_geometry_low_admission_fields reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        hz.2 hZ s θ w σ freq heightV height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
          hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow (frequencyLoss Z 32 ξ+reserve) ξ
          hMmin hω hξ hMcap' hzslot haff reflected R seed bin t Mprice Aprice sourceWeight firstIndex q
          (fun l=>(hfields l).1) (fun l=>(hfields l).2.1) (fun l=>(hfields l).2.2.1)
          (fun l=>(hfields l).2.2.2.1) (fun l=>(hfields l).2.2.2.2.1) g
          (fun l=>(hfields l).2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.2.1)))))))

/-- The occupied first labels and projectors, with no extension of an
allocation to a zero or unsupported ideal. -/
def selectedLowFirstLabels {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) : Finset FirstSourceLabel :=
  Finset.univ.image first

def selectedLowFirstProjectors {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (l : FirstSourceLabel) : Finset (Ideal O) :=
  (Finset.univ.filter (fun j=>first j=l)).image seed

abbrev SelectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O) :=
  (l : selectedLowFirstLabels first) × selectedLowFirstProjectors first seed l.val

def selectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O) (j : Label) :
    SelectedLowFirstPair first seed :=
  ⟨⟨first j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩,
    ⟨seed j,Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩⟩⟩

theorem selected_low_first_pair_bijective {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Function.Bijective (selectedLowFirstPair first seed) := by
  constructor
  · intro j k h
    apply hinj
    exact Prod.ext (congrArg (fun x=>(x.1.val)) h) (congrArg (fun x=>x.2.val) h)
  · intro x
    obtain ⟨j,hj,hseed⟩ := Finset.mem_image.mp x.2.property
    have hfirst : first j=x.1.val := (Finset.mem_filter.mp hj).2
    refine ⟨j,?_⟩
    apply Sigma.ext
    · exact Subtype.ext hfirst
    · apply (Subtype.heq_iff_coe_eq (fun D=>by
        dsimp only [selectedLowFirstPair]
        rw [hfirst])).mpr
      exact hseed

def selectedLowFirstPairEquiv {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Label ≃ SelectedLowFirstPair first seed :=
  Equiv.ofBijective _ (selected_low_first_pair_bijective first seed hinj)

/-- Reindex the entire selected child cost, after the second-label sum has
been formed. The inverse pair index keeps the actual first allocation. -/
theorem selected_low_first_cost_reindex {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→ Finset FirstSourceLabel) (cost : Label→ FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost j v)=
      ∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first seed l.val,
          ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩),
            cost ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩) v := by
  calc
    _=∑p : SelectedLowFirstPair first seed,
        ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm p),
          cost ((selectedLowFirstPairEquiv first seed hinj).symm p) v :=
      Fintype.sum_equiv (selectedLowFirstPairEquiv first seed hinj) _ _ (fun j=>by simp)
    _=_ := Fintype.sum_sigma _

theorem selected_low_pair_inverse_fields {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (p : SelectedLowFirstPair first seed) :
    first ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.1.val ∧
      seed ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.2.val := by
  have h := (selectedLowFirstPairEquiv first seed hinj).apply_symm_apply p
  exact ⟨congrArg (fun x=>x.1.val) h,congrArg (fun x=>x.2.val) h⟩

def selectedLowSupportedChildren {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→ Finset FirstSourceLabel)
    (l : FirstSourceLabel) (D : Ideal O) : Finset FirstSourceLabel :=
  if h : l∈selectedLowFirstLabels first ∧ D∈selectedLowFirstProjectors first seed l then
    children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨⟨l,h.1⟩,⟨D,h.2⟩⟩)
  else ∅

@[simp] theorem selected_low_supported_children_at {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→ Finset FirstSourceLabel) (p : SelectedLowFirstPair first seed) :
    selectedLowSupportedChildren first seed hinj children p.1.val p.2.val=
      children ((selectedLowFirstPairEquiv first seed hinj).symm p) := by
  unfold selectedLowSupportedChildren
  rw [dite_eq_left (show p.1.val∈selectedLowFirstLabels first ∧
    p.2.val∈selectedLowFirstProjectors first seed p.1.val from ⟨p.1.property,p.2.property⟩)]

/-- The supported payment domain is exactly the image of selected first
pairs, with the dependent second children retained in every occupied fiber. -/
theorem selected_low_supported_sum {Label : Type*} [Fintype Label]
    (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→ Finset FirstSourceLabel)
    (cost : FirstSourceLabel→ FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost (first j) v)=
      ∑l∈selectedLowFirstLabels first,∑D∈selectedLowFirstProjectors first seed l,
        ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v := by
  rw [selected_low_first_cost_reindex first seed hinj children (fun j v=>cost (first j) v)]
  calc
    _=∑l : selectedLowFirstLabels first,∑D : selectedLowFirstProjectors first seed l.val,
        ∑v∈selectedLowSupportedChildren first seed hinj children l.val D.val,cost l.val v := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro D _
      rw [selected_low_supported_children_at first seed hinj children ⟨l,D⟩,
        (selected_low_pair_inverse_fields first seed hinj ⟨l,D⟩).1]
    _=_ := by
      rw [Finset.sum_coe_sort (selectedLowFirstLabels first)
        (fun l=>∑D : selectedLowFirstProjectors first seed l,
          ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_coe_sort (selectedLowFirstProjectors first seed l)
        (fun D=>∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)

/-- Pay the selected first-pair fibers once. Supported second labels are
summed with their reciprocal norm; the first labels and projector ideals
are reindexed injectively, without an additional first-family count. -/
theorem actual_selected_low_supported_budget (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀{Label : Type*}[Fintype Label]
    (reflected second : Bool)(Z T A p exponent error : ℝ),
    2≤ Z → 1≤ T → p≤ B → ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    ∀(first : Label→ FirstSourceLabel)(seed : Label→ Ideal O),
    Function.Injective (fun j=>(first j,seed j)) →
    (∀j,Supported (first j).1.1 ∧ Supported (first j).1.2) →
    (∀j,primeSupport (first j).1.1=primeSupport (first j).1.2) →
    (∀j,seed₀∣(first j).1.1 ∧ seed₀∣(first j).1.2) →
    (∀j,((first j).1.1.absNorm:ℝ)≤ Z^B ∧ ((first j).1.2.absNorm:ℝ)≤ Z^B) →
    (∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤ Z^p) →
    (∀j,lowGeometryExponent reflected Z A (first j)≤ exponent) →
    (∀j,Squarefree (seed j)) →
    (∀j,T≤((seed j).absNorm:ℝ) ∧ ((seed j).absNorm:ℝ)<2*T) →
    ∀children : Label→ Finset FirstSourceLabel,
    (∀j,∀v∈children j,Supported v.1.1 ∧ Supported v.1.2) →
    (∀j,∀v∈children j,primeSupport v.1.1=primeSupport v.1.2) →
    (∀j,∀v∈children j,seed j∣v.1.1 ∧ seed j∣v.1.2) →
    (∀j,∀v∈children j,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) →
    (∑j,∑v∈children j,Z^(lowGeometryExponent reflected Z A (first j)+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
      K₀*Z^(p+exponent+error+ε)/(seed₀.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hbudget⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K₀,hK₀,?_⟩
  intro Label _ reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0 first seed hinj
    hsup heq hseed hnorm hrad hgeom hsq hdyad children hsup₂ heq₂ hseed₂ hnorm₂
  rw [selected_low_supported_sum first seed hinj children
    (fun l v=>Z^(lowGeometryExponent reflected Z A l+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))]
  apply hbudget reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0
    (selectedLowFirstLabels first)
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hsup j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact heq j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hseed j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hnorm j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hrad j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hgeom j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hsq j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hdyad j
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hsup₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact heq₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    have hf := (selected_low_pair_inverse_fields first seed hinj ⟨⟨l,hl⟩,⟨D,hD⟩⟩).2
    simpa only [hf] using hseed₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hnorm₂ _ v hv

/-- Literal selected first columns supply the occupied support equivalence
used by the finite supported low payment. -/
def actual_geometry_selected_first_pair_equiv {Label : Type*} [Fintype Label]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin (column j),
      (column j).2.1.val))) :=
  selectedLowFirstPairEquiv
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (column j))
    (fun j=>(column j).2.1.val) hinj

omit [DecidableEq α] in
/-- The occupied-pair inverse requires an allocation only at its original
selected ideal, so the first coefficient remains genuinely nonzero. -/
theorem actual_geometry_selected_pair_allocation {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin (column j),
      (column j).2.1.val)))
    (alloc : (j : Label)→ actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)))
    (hne : ∀j,frozenCoefficient (alloc j).val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)) R s.ν s.W s.P≠0) :
    ∀p : SelectedLowFirstPair
      (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (column j))
      (fun j=>(column j).2.1.val),
      let j := (actual_geometry_selected_first_pair_equiv s R seed K Z ξ hK bin column hinj).symm p
      frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)) R s.ν s.W s.P≠0 := by
  intro p j
  exact hne j

/-- Actual selected second blocks pay their child volume and canonical
scalar before the supported reciprocal-norm sum. The common four-dyad
box is paid once, independently of the number of first labels. -/
theorem eventual_actual_selected_low_second_payment
    (N : ℕ) (lo εv : ℝ) (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→ FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→ actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→ Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(ξ M a reserve error εcommon Bnorm : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤ Z^Bnorm) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ M a reserve error εcommon Bnorm hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox pay
  have hZ : 0< Z := zero_lt_one.trans hz.1
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hpay (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :
      0≤ pay l v := by
    dsimp only [pay]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _) (div_nonneg
        (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ (first l)).le
        (volume_pos (src l)).le))
      (mul_nonneg (normalizer_pos _ _ (hgate l v hv).1 _).le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ.le _)
  have hdis := actual_second_joint_positive_disintegration
    (fun l=>liveIndices (alloc l).val) src R seed K Tsec Z ξ rows hU box hbox
    (fun l v _=>pay l v) (fun l v hv _ _=>hpay l v hv)
  apply hdis.trans
  have hpoint : ∀l,∀v∈actualSecondLabels (src l) (R l) (seed l),pay l v≤
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
        error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    intro l v hv
    have hg := hgate l v hv
    have hnorm : ((if second then v.1.2 else v.1.1).absNorm:ℝ)≤ Z^Bnorm := by
      cases second
      · exact hg.2.2.2.2.2.1.trans (hsource l)
      · exact hg.2.2.2.2.2.2.trans (hsource l)
    exact hz.2 s hn hs reflected second (first l) (hfirst l).1 (hfirst l).2 (heq l)
      Rfirst (alloc l) (χ l) (t l) (halloc l) v.1.1 v.1.2 hg.1 hg.2.1 v.2.val
      M a ξ reserve error εcommon Bnorm hecommon hnorm
  calc
    _≤∑_n∈box,∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum (hpoint l)
    _=_ := by simp

/-- The selected original second scalar sum is fully paid on its finite
supported first-label/projector fibers. -/
theorem eventual_actual_selected_low_second_paid
    (N : ℕ) (lo εv B ε : ℝ) (hlo : 0< lo) (hev : 0<εv) (hB : 0≤ B) (hε : 0<ε) :
    ∃K₀ : ℝ,0< K₀ ∧
    ∀ᶠZ : ℝ in atTop,2≤ Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→ FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→ actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→ Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(ξ M a reserve error εcommon : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤ Z^B) →
    ∀(T p exponent : ℝ),1≤ T → p≤ B →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤ Z^B ∧ ((first l).1.2.absNorm:ℝ)≤ Z^B) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤ Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤ exponent) →
    (∀l,T≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*T) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ)) := by
  let hbase := actual_selected_low_supported_budget.{0} B ε hB hε
  let K₀ := Classical.choose hbase
  let hlabels := Classical.choose_spec hbase
  refine ⟨K₀,hlabels.1,?_⟩
  filter_upwards [eventual_actual_selected_low_second_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ M a reserve error εcommon hseed hw₁ hw₂ hecommon hsource
    T p exponent hT hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hdyad
    rows hU box hbox pay
  have hpaid := hz.2 s hn hs reflected second first hfirst heq Rfirst alloc χ t halloc
    R seed K Tsec ξ M a reserve error εcommon B hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hbound := hlabels.2 (Label:=Label) reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed₀ hs₀ hs₀0 first seed hinj hfirst heq
    hfirstseed hfirstnorm hrad hgeom hseed hdyad
    (fun l=>actualSecondLabels (src l) (R l) (seed l))
    (fun l v hv=>⟨(hgate l v hv).1,(hgate l v hv).2.1⟩)
    (fun l v hv=>(hgate l v hv).2.2.1)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.1,(hgate l v hv).2.2.2.2.1⟩)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.2.2.1.trans (hsource l),
      (hgate l v hv).2.2.2.2.2.2.trans (hsource l)⟩)
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=
      p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbound
  apply hpaid.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg box.card)
  simpa only [src,K₀,add_assoc] using hbound

/-- The actual second-projector union pays the low theorem's shell-scale
factor once, uniformly before all moving block labels and allocations. -/
theorem actual_second_low_weighted_shells (N : ℕ)(U εshell ε : ℝ)
    (hU : 0≤ U)(heshell : 0≤εshell)(he : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
    ∀{Label : Type*}[Fintype Label](d : Label→ SecondInputDatum α),
    (∀l,Fintype.card (d l).slots≤ N) →
    (∀l i I,I∈(d l).input.pools i→(I.absNorm:ℝ)≤ Z^U) →
    (∑n∈selectedShells (sharedProjectors (fun l=>(d l).block.divisors)),
      (2*dyadicScale n)^(3*εshell))≤
        C*Z^(ε+3*(((N:ℝ)+2)*U)*εshell) := by
  obtain ⟨C₀,hC₀,hbound⟩ := actual_second_projector_shell_subpower (α:=α) N U ε hU he
  refine ⟨C₀*(2:ℝ)^(3*εshell),mul_pos hC₀ (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ d hN hpool
  let L := ((N:ℝ)+2)*U
  let shells := selectedShells (sharedProjectors (fun l=>(d l).block.divisors))
  have hZ : 0< Z := zero_lt_one.trans hz.1
  have hpower : 0≤3*εshell := mul_nonneg (by norm_num) heshell
  have hscale (n : ℤ)(hn : n∈shells) : dyadicScale n≤ Z^L :=
    (shared_projector_shell_scale (fun l=>(d l).block.divisors) Z L
      (fun l D hD=>(second_datum_projector_cap (d l) N Z U (hN l) hz.1.le hU
        (hpool l) D hD).2) n hn).2
  have hp (n : ℤ)(hn : n∈shells) :
      (2*dyadicScale n)^(3*εshell)≤(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := by
    calc
      _≤(2*Z^L)^(3*εshell) := Real.rpow_le_rpow (mul_nonneg (by norm_num) (dyadicScale_pos n).le)
        (mul_le_mul_of_nonneg_left (hscale n hn) (by norm_num)) hpower
      _=_ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ.le _),
          ←Real.rpow_mul hZ.le]
        congr 1
        ring
  calc
    _≤∑_n∈shells,(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := Finset.sum_le_sum hp
    _=(shells.card:ℝ)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) := by simp
    _≤(C₀*Z^ε)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) :=
      mul_le_mul_of_nonneg_right (hz.2 d hN hpool) (by positivity)
    _=_ := by dsimp only [L]; rw [Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_low_physical_family_columns
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_low_physical_columns

#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_low_first_pair_bijective
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_low_first_cost_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_pair_allocation

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_selected_low_second_payment

#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_low_supported_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_selected_low_supported_budget

#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_selected_low_second_paid

#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_low_pair_inverse_fields
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_low_supported_children_at

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_low_weighted_shells

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainLowAggregate -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorSelectedPayment; sha256 63826df9a44c38f9ef00df520d05c61664f8912a7faae589800007ec3fb0c7ca -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                            
                                                            

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair
open Cycle61Moment CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CompletedGauss
local notation "O" => HeckeFamily.O
local instance errorSelectedPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem error_allocation_cast_val {κ : Type*} [Fintype κ]
    (pools : κ→ Finset (Ideal O))(C D : Ideal O)(h : C=D)
    (B : actualAllocations pools C) : (h ▸ B).val=B.val := by
  cases h
  rfl

section Selected
variable {ι Label : Type} [Fintype ι] [Fintype Label]
variable (s : Input ι) (reflected : Bool)
variable (first : Label→ FirstSourceLabel) (projector : Label→ Ideal O)
variable (hinj : Function.Injective (fun j=>(first j,projector j)))
variable (alloc : (j : Label)→ actualAllocations s.pools
  (if reflected then (first j).1.2 else (first j).1.1))

/-- The occupied-pair inverse keeps the original selected allocation. -/
@[irreducible] def selectedErrorAllocation (pair : SelectedLowFirstPair first projector) :
    actualAllocations s.pools (if reflected then pair.1.val.1.2 else pair.1.val.1.1) :=
  let j:=(selectedLowFirstPairEquiv first projector hinj).symm pair
  let h : (if reflected then (first j).1.2 else (first j).1.1)=
      (if reflected then pair.1.val.1.2 else pair.1.val.1.1) := by
    rw [(selected_low_pair_inverse_fields first projector hinj pair).1]
  h ▸ alloc j

theorem selected_error_allocation_val (pair : SelectedLowFirstPair first projector) :
    (selectedErrorAllocation s reflected first projector hinj alloc pair).val=
      (alloc ((selectedLowFirstPairEquiv first projector hinj).symm pair)).val := by
  unfold selectedErrorAllocation
  exact error_allocation_cast_val _ _ _ _ _

theorem selected_error_allocation_nonzero (R : Ideal O)
    (hf : ∀j,frozenCoefficient (alloc j).val
      (if reflected then (first j).1.2 else (first j).1.1) R s.ν s.W s.P≠0)
    (pair : SelectedLowFirstPair first projector) :
    frozenCoefficient (selectedErrorAllocation s reflected first projector hinj alloc pair).val
      (if reflected then pair.1.val.1.2 else pair.1.val.1.1) R s.ν s.W s.P≠0 := by
  rw [selected_error_allocation_val]
  have h:=(selected_low_pair_inverse_fields first projector hinj pair).1
  simpa only [h] using hf ((selectedLowFirstPairEquiv first projector hinj).symm pair)

theorem selected_error_allocation_at (j : Label) :
    selectedErrorAllocation s reflected first projector hinj alloc
      (selectedLowFirstPair first projector j)=alloc j := by
  apply Subtype.ext
  rw [selected_error_allocation_val]
  change (alloc ((selectedLowFirstPairEquiv first projector hinj).symm
    ((selectedLowFirstPairEquiv first projector hinj) j))).val=(alloc j).val
  rw [Equiv.symm_apply_apply]

end Selected

/-- Reindex complete costs after all second labels and active allocations
have been summed; the prime denominator is retained. -/
theorem selected_error_prime_ray_cost_reindex {Label PrimeIndex : Type*}
    [Fintype Label] [Fintype PrimeIndex]
    (first : Label→ FirstSourceLabel)(projector : Label→ Ideal O)
    (hinj : Function.Injective (fun j=>(first j,projector j)))
    (outside : ℝ)(branch : Fin 3→ℝ)
    (cost : PrimeIndex→ Fin 3→ RayCharacter→ SelectedLowFirstPair first projector→ℝ) :
    outside*(∑q : PrimeIndex,∑i : Fin 3,branch i*
      ∑j : Label,∑ψ : RayCharacter,
        cost q i ψ ((selectedLowFirstPairEquiv first projector hinj) j))=
    outside*(∑q : PrimeIndex,∑i : Fin 3,branch i*
      ∑l : selectedLowFirstLabels first,∑ψ : RayCharacter,
        ∑D : selectedLowFirstProjectors first projector l.val,cost q i ψ ⟨l,D⟩) := by
  apply congrArg (fun x : ℝ=>outside*x)
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x : ℝ=>branch i*x)
  calc
    _=∑p : SelectedLowFirstPair first projector,∑ψ : RayCharacter,cost q i ψ p :=
      Fintype.sum_equiv (selectedLowFirstPairEquiv first projector hinj) _ _ (fun _=>rfl)
    _=∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first projector l.val,∑ψ : RayCharacter,cost q i ψ ⟨l,D⟩ :=
      Fintype.sum_sigma _
    _=_ := Finset.sum_congr rfl (fun l _=>Finset.sum_comm)


private theorem error_selected_label_gate {Label : Type*}[Fintype Label]
    (first : Label→ FirstSourceLabel)(P : FirstSourceLabel→ Prop)(hP : ∀j,P (first j)) :
    ∀l∈selectedLowFirstLabels first,P l := by
  intro l hl
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hl
  exact hP j

private theorem error_selected_projector_gate {Label : Type*}[Fintype Label]
    (first : Label→ FirstSourceLabel)(projector : Label→ Ideal O)
    (P : Ideal O→ Prop)(hP : ∀j,P (projector j)) :
    ∀(l : selectedLowFirstLabels first) D,D∈selectedLowFirstProjectors first projector l.val→ P D := by
  intro l D hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact hP j

private theorem error_actual_second_label_gates {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(cap : ℝ)
    (hs : Squarefree seed)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hcap : sourceRadius s≤ cap) :
    (∀v∈actualSecondLabels s R seed,Supported v.1.1 ∧ Supported v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,primeSupport v.1.1=primeSupport v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,seed∣v.1.1 ∧ seed∣v.1.2) ∧
    (∀v∈actualSecondLabels s R seed,(v.1.1.absNorm:ℝ)≤ cap ∧ (v.1.2.absNorm:ℝ)≤ cap) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.1,h.2.1⟩
  · intro v hv
    exact (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).2.2.1
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.2.2.2.1,h.2.2.2.2.1⟩
  · intro v hv
    have h:=actual_second_labels_gates s R seed hs hw₁ hw₂ v hv
    exact ⟨h.2.2.2.2.2.1.trans hcap,h.2.2.2.2.2.2.trans hcap⟩

set_option linter.defProp false in
/-- Original occupied first keys feed the saved prime payment with their
own allocations. The extracted labels come from the literal child source. -/
def eventual_actual_selected_error_saved_payment (N : ℕ)(lo εv B ε : ℝ)
    (hlo : 0< lo)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (Mmin εaffine : ℝ)(hMmin : 0< Mmin) :=
  let data:=eventual_actual_error_dependent_saved_payment N lo εv B ε hlo hev hB he Mmin εaffine hMmin
  let receipt:=Classical.choose_spec data
  And.intro receipt.1 (receipt.2.mono fun Z hz=>And.intro hz.1 (
    fun {ι Label : Type}[Fintype ι][Fintype Label](s : Input ι)
      (hcard : Fintype.card ι≤ N)(hlower : lo≤ s.lower)
      (reflected second : Bool)(T p exponent error εcommon M a δ reserve : ℝ)
      (hT : 1≤ T)(hp : p≤ B)(hecommon : 0≤εcommon)(hM : Mmin≤ M)
      (hloss : error+εv+B*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
      (first : Label→ FirstSourceLabel)(projector : Label→ Ideal O)
      (hinj : Function.Injective (fun j=>(first j,projector j)))
      (hsup : ∀j,Supported (first j).1.1 ∧ Supported (first j).1.2)
      (heq : ∀j,primeSupport (first j).1.1=primeSupport (first j).1.2)
      (hseed : ∀j,seed∣(first j).1.1 ∧ seed∣(first j).1.2)
      (hnorm : ∀j,((first j).1.1.absNorm:ℝ)≤ Z^B ∧ ((first j).1.2.absNorm:ℝ)≤ Z^B)
      (hrad : ∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤ Z^p)
      (hgeom : ∀j,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first j)≤ exponent)
      (hprojector : ∀j,Squarefree (projector j))
      (hdyad : ∀j,T≤((projector j).absNorm:ℝ) ∧ ((projector j).absNorm:ℝ)<2*T)
      (Rfirst : Ideal O)
      (alloc : (j : Label)→ actualAllocations s.pools
        (if reflected then (first j).1.2 else (first j).1.1))
      (χ : Label→ Character)(t : ℝ)
      (hf : ∀j,frozenCoefficient (alloc j).val
        (if reflected then (first j).1.2 else (first j).1.1) Rfirst s.ν s.W s.P≠0)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)=>
    let labels:=selectedLowFirstLabels first
    let Ds : labels→ Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→ Ds l→ actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→ Ds l→ Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→ Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst (alloc' l D) (χ' l D) t
    fun (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
      (hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (hslot : ∀l D,∀q : elementPool P,∀j I,I∈(u l D).slots j→ IsCoprime (Ideal.span {q.val}) I)=>
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    fun (υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→ Bps l D q i→ Character)(vheight : ℝ)=>
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (Rfirst*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (Rfirst*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    fun (hsource : ∀l D q i ψ Bp,sourceRadius (source l D q i ψ Bp)≤ Z^B)=>
    let gates : ∀(l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i),
        (∀v∈children l D q i ψ Bp,Supported v.1.1 ∧ Supported v.1.2) ∧
        (∀v∈children l D q i ψ Bp,primeSupport v.1.1=primeSupport v.1.2) ∧
        (∀v∈children l D q i ψ Bp,D.val∣v.1.1 ∧ D.val∣v.1.2) ∧
        (∀v∈children l D q i ψ Bp,(v.1.1.absNorm:ℝ)≤ Z^B ∧ (v.1.2.absNorm:ℝ)≤ Z^B) :=
      fun l D q i ψ Bp=>error_actual_second_label_gates
        (source l D q i ψ Bp) (R₂ l q i) D.val (Z^B)
        (error_selected_projector_gate first projector _ hprojector l D.val D.property)
        hw₁ hw₂ (hsource l D q i ψ Bp)
    let pay:=hz.2 s hcard hlower reflected second T p exponent error εcommon M a δ reserve
      hT hp hecommon hM hloss seed hs hs0 labels
      (error_selected_label_gate first _ hsup)
      (error_selected_label_gate first _ heq)
      (error_selected_label_gate first _ hseed)
      (error_selected_label_gate first _ hnorm)
      (error_selected_label_gate first _ hrad)
      (error_selected_label_gate first _ hgeom)
      Ds (error_selected_projector_gate first projector _ hprojector)
      (error_selected_projector_gate first projector _ hdyad)
      Rfirst alloc' χ' t
      (fun l D=>selected_error_allocation_nonzero s reflected first projector hinj alloc Rfirst hf ⟨l,D⟩)
      P hP hprime hbad hslot υ vheight
    let hpaid:=pay children
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.2.1)
      (fun l D q i ψ Bp=>(gates l D q i ψ Bp).2.2.2)
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)
        (pair : SelectedLowFirstPair first projector)=>
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    (selected_error_prime_ray_cost_reindex first projector hinj
      (56/(P.card:ℝ)) (fun i=>16*(errorIndex i+2:ℝ)) cost).le.trans hpaid
  ))


end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.selectedErrorAllocation
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_error_allocation_val
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_error_allocation_nonzero
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_error_allocation_at
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_error_prime_ray_cost_reindex
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_selected_error_saved_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorSelectedPayment -/
