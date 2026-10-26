import Candidate.Cycle63.Physical.InitialMass.GeometryMainCoarseNormalized
import Candidate.Cycle63.Physical.InitialMass.GeometryHighWeightedSelection
import Candidate.Cycle63.Physical.InitialMass.GeometryCoarseSupport
import Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment ActualEisensteinCubic CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentLogDyadic CenteredMomentNaturalRowSource CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentSecondEnergySplit CenteredMomentWholeDivisorShell
open CenteredMomentSourceRow CenteredMomentCommonPairedSource CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonHeightEnvelope CenteredMomentSecondInputCapacitySource
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstSourceReduction
local instance geometryMainCoarseFamilySumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem actual_geometry_main_all_height_coarse_family {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→actualAllocations s.pools (C l),
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
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(height : rows→ℝ)(Ds : rows→Finset (Ideal O))
        (control T B₁ B₂ : ℝ),0≤ control → 1≤T → 0≤B₁ → 0≤B₂ →
      (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,Squarefree L ∧ T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let outer := fun r : rows=>(Kmain (first r.val.val.1.1)/volume (source r.val.val.1.1))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤K*control*(2*T)^(3*ε)*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad) := by
  let SB:=B+loss
  let scalarCap:=39*SB+SB*εmass+SB*ε+εvolume
  let Cscalar:=2*((geometrySupportConstant N lo ap ap)^2+1)*(Cs^N)^2/lowerFactor N lo ap
  have hSB : 0≤SB:=by dsimp [SB]; positivity
  have hCscalar : 0<Cscalar := by
    dsimp [Cscalar]
    apply div_pos _ (lowerFactor_pos N lo ap hlo hap)
    exact mul_pos (by nlinarith [sq_nonneg (geometrySupportConstant N lo ap ap)])
      (sq_pos_of_pos (pow_pos (zero_lt_one.trans_le hCs) _))
  have hselection:=actual_geometry_high_weighted_normalized_family_selection
    η₀ u₀ F₀ R₀ hu₀ N b bs loss B B ξ hb hbs hloss hB hB hξ hξε
  obtain ⟨D,hD,hselection⟩:=hselection
  have hcoarse:=actual_child_weighted_coarse_columns N hα
    (8*SB) loss ε pad Cs b bs window plainCap scalarCap (by positivity)
    hloss hε hpad hCs hb hbs hwindow hcap
  obtain ⟨Kc,hKc,hcoarse⟩:=hcoarse
  refine ⟨D*Kc*Cscalar,by positivity,?_⟩
  filter_upwards [hselection,hcoarse,eventual_actual_geometry_main_scalar_cap N lo ap εvolume hlo hap hev,
    eventual_geometry_child_source_cap N b bs loss hb hbs hloss,
    eventual_geometry_joint_support η₀ u₀ F₀ R₀ hu₀ b loss N (zero_lt_one.trans_le hb) hloss]
    with Z hselect hc hscalar hchild hjoint
  intro hZ Label _ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector
    Kmain Tsec hprojector hz₁ hz₂ hKm Index datum block rows second W
    height Ds control T B₁ B₂ hcontrol hT hB₁ hB₂ hW₁ hW₂ hcontrolB hDs outer cost
  let label := fun q : Index=>first q.1
  let left := !reflected
  let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
  have hunit : ∀l,unit l≠0 := fun _=>Units.ne_zero _
  have hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0 :=
    fun r=>actual_joint_first_frequency_ne_zero left u₀ unit (secondEncodedRow block label r)
      hu₀ (hunit _) (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column r.val.1.1).val.1).hC
  let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
  have hzpos : 0<Z:=zero_lt_one.trans hZ
  have hV : volume s≤Z^B :=
    (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (abs_le.mp hA).2
  have hKM : Z^Dfirst≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.le (abs_le.mp hMbox).2
  have houter : ∀r : rows,0≤outer r := by
    intro r
    exact div_nonneg (mul_nonneg (div_nonneg (hKm _).le (volume_pos _).le)
      (normalizer_pos _ _ (datum r.val.val.1).hC _).le) (lowerFactor_pos N lo ap hlo hap).le
  have hsum:=hselect hZ reflected s R seed Dfirst a reserve t hK
    hseed hα he hV hKM hs₁ hs₂ ha hreserve bin column hinj alloc halloc rows second W εmass
    height Ds outer houter
  obtain ⟨pick,hpick,hinjpick,hinjreflect,hsum⟩:=hsum
  let κ:=Finset.univ.image key
  let chooseRow := fun k : κ=>(pick k).val
  let col := fun k : κ=>(column (chooseRow k).val.1.1).val
  let v := fun k : κ=>datum (chooseRow k).val.1
  let encoded := fun k : κ=>if second then reflectedNonzeroJointLabel (key (pick k)) else key (pick k)
  let E := fun k : κ=>if second then (v k).D else (v k).C
  have hE : ∀k,Supported (E k) := by intro k; cases second <;> first | exact (v k).hC | exact (v k).hD
  let ψ := fun k : κ=>if second then (chooseRow k).val.2.2.1⁻¹ else (chooseRow k).val.2.1
  let z := fun k : κ=>if second then -(chooseRow k).val.2.2.2.val else (chooseRow k).val.2.2.2.val
  let scalar := fun k : κ=>(Real.sqrt (geometryFirstHighMass reflected s R seed W
    Dfirst Z ξ εmass hK bin (col k)*outer (pick k)) : ℂ)
  have hscalarnorm (k : κ) : ‖scalar k‖^2=geometryFirstHighMass reflected s R seed W
      Dfirst Z ξ εmass hK bin (col k)*outer (pick k) := by
    show ‖(Real.sqrt _ : ℂ)‖^2=_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt]
    exact mul_nonneg (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass
      hK bin (col k)) (houter (pick k))
  have hsrc : ∀l,sourceRadius (source l)≤Z^SB := fun l=>
    hchild.2 s B hα he hV (C l) R (alloc l) (χ l) t (halloc l)
  have hvgates (k : κ) : (v k).seed∣(v k).C ∧ (v k).seed∣(v k).D ∧
      ((v k).C.absNorm:ℝ)≤Z^SB ∧ ((v k).D.absNorm:ℝ)≤Z^SB := by
    have hg:=actual_retained_block_gates (slots (chooseRow k).val.1.1) (source (chooseRow k).val.1.1)
      (R*C (chooseRow k).val.1.1) (projector (chooseRow k).val.1.1)
      (hprojector _) (hz₁ _) (hz₂ _) (Kmain (first _)) (Tsec (first _)) Z ξ (hKm _)
      (chooseRow k).val.1.2
    exact ⟨hg.1,hg.2.1,hg.2.2.1.trans (hsrc _),hg.2.2.2.trans (hsrc _)⟩
  have hsupp (k : κ) := actual_second_encoded_support block label
    (fun q=>⟨(geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).hC,
      (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).hD,
      (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin (column q.1).val.1).sameSupport⟩) (chooseRow k)
  have hsupport (k : κ) := hjoint hZ reflected s R seed (Z^Dfirst) ξ a reserve B B hK hseed hs₁ hs₂
    hsource hKM hξ hξε ha hreserve bin (col k) datum label (chooseRow k) rfl rfl
  have hrow (k : κ) : LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (encoded k))≤Z^(8*SB) := by
    have hh : LocalMoment.rawFrequencyNorm (nonzeroJointSourceRow (key (pick k)))≤Z^(B+5*B+loss) :=
      (hsupport k).1
    cases second
    · exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith only [hB, hloss, hξε]))
    · rw [show encoded k=reflectedNonzeroJointLabel (key (pick k)) by rfl,reflected_joint_norm]
      exact hh.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith only [hB, hloss, hξε]))
  have hnorm (k : κ) : ((encoded k).val.1.1.1.absNorm:ℝ)≤Z^(8*SB) ∧
      ((encoded k).val.1.1.2.absNorm:ℝ)≤Z^(8*SB) ∧
      ((encoded k).val.2.1.1.absNorm:ℝ)≤Z^(8*SB) ∧ ((encoded k).val.2.1.2.absNorm:ℝ)≤Z^(8*SB) := by
    have hn:=actual_geometry_norm_caps s R seed (Z^Dfirst) Z ξ B hseed hs₁ hs₂ hsource (col k).1.val
    have hb : Z^B≤Z^(8*SB):=Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith only [hB, hloss, hξε])
    have hb' : Z^SB≤Z^(8*SB):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith only [hSB])
    cases second <;> exact ⟨(hn 0).2.trans hb,(hn 1).2.trans hb,
      (hvgates k).2.2.1.trans hb',(hvgates k).2.2.2.trans hb'⟩
  have hscalarcap (k : κ) : ‖scalar k‖^2*(∏i,(source (chooseRow k).val.1.1).M i)^2*
      ((E k).absNorm:ℝ)^(ε-1)≤Cscalar*Z^scalarCap := by
    have hscalarpoint := hscalar.2 s hα hlow reflected left second R seed W Dfirst ξ a reserve SB εmass ε Cs hK
      hSB hem hε.le hCs hM hseed hs₁ hs₂
      (hsource.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith only [hB, hloss, hξε])))
      hsap₁ hsap₂
      (hMbox.trans (by dsimp [SB]; linarith only [hB, hloss, hξε])) (hA.trans (by dsimp [SB]; linarith only [hB, hloss, hξε]))
      (habox.trans (by dsimp [SB]; linarith only [hB, hloss, hξε])) (hω.trans (by dsimp [SB]; linarith only [hB, hloss, hξε]))
      bin (col k) R (alloc (chooseRow k).val.1.1) (χ (chooseRow k).val.1.1) t (halloc _)
      (v k).C (v k).D (v k).hC (v k).hD (v k).sameSupport ⟨(hvgates k).2.2.1,(hvgates k).2.2.2⟩ (v k).inactive
    exact (congrArg (fun x : ℝ=>x*(∏i,(source (chooseRow k).val.1.1).M i)^2*
      ((E k).absNorm:ℝ)^(ε-1)) (hscalarnorm k)).le.trans hscalarpoint
  have hh:=hc.2 left u₀ unit B control T Cscalar hcontrol hT hCscalar.le encoded hinjreflect Finset.univ
    (fun k _=>hrow k)
    (fun k _=>by cases second <;> exact (hsupp k).1)
    (fun k _=>by cases second <;> exact (hsupp k).2)
    (fun k _=>by
      have hg: ((Ideal.span {jointSourceRow left u₀ unit (encoded k).val}*
        firstSourceMissing left (encoded k).val.1).absNorm:ℝ)≤Z^(B+6*B+loss) := by
        cases second
        · exact (hsupport k).2.2
        · change ((Ideal.span {jointSourceRow left u₀ unit (reflectedJointLabel (key (pick k)).val)}*
              firstSourceMissing left (key (pick k)).val.1).absNorm:ℝ)≤Z^(B+6*B+loss)
          rw [reflected_joint_row,Ideal.span_singleton_neg]
          exact (hsupport k).2.2
      exact hg.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [SB]; linarith only [hB, hloss, hξε])))
    (fun k _=>hnorm k) (fun k _=>by cases second <;> exact (hsupport k).2.1)
    s hM he.1 he.2.2.2.1 he.2.2.2.2.2 hwin hscales hP
    (fun k=>C (chooseRow k).val.1.1) (fun _=>R) (fun k=>alloc (chooseRow k).val.1.1)
    (fun k=>χ (chooseRow k).val.1.1) (fun _=>t)
    E (fun k=>(v k).R) (fun k=>(v k).seed) hE (fun k=>(v k).τ (ψ k))
    (fun k=>height (pick k)) z scalar (fun k=>Ds (pick k)) B₁ B₂
    hB₁ hB₂ hW₁ hW₂ hcontrolB
    (fun k _=>by cases second <;> first | exact (hvgates k).1 | exact (hvgates k).2.1)
    (fun k _=>hscalarcap k) (fun k _=>hDs (pick k))
  have hcosteq : (∑k : κ,cost (pick k))=
      ∑k∈(Finset.univ : Finset κ),∑L∈Ds (pick k),‖scalar k*normalizedColumn
        (withHeight (source (chooseRow k).val.1.1) ((v k).τ (ψ k)) (height (pick k)))
          (E k) (hE k) (v k).R (v k).seed L (z k)‖^2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    let c := normalizedColumn
      (withHeight (source (chooseRow k).val.1.1) ((v k).τ (ψ k)) (height (pick k)))
        (E k) (hE k) (v k).R (v k).seed
    have hpoint (L : Ideal O) :
        (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (col k)*
          outer (pick k))*‖c L (z k)‖^2=‖scalar k*c L (z k)‖^2 := by
      calc
        _=‖scalar k‖^2*‖c L (z k)‖^2 :=
          congrArg (fun x : ℝ=>x*‖c L (z k)‖^2) (hscalarnorm k).symm
        _=(‖scalar k‖*‖c L (z k)‖)^2 := (mul_pow _ _ 2).symm
        _=_ := congrArg (fun x : ℝ=>x^2) (norm_mul (scalar k) (c L (z k))).symm
    exact (Finset.mul_sum (Ds (pick k)) (fun L=>‖c L (z k)‖^2)
      (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (col k)*
        outer (pick k))).trans (Finset.sum_congr rfl (fun L _=>hpoint L))

  have hcub : (∑k : κ,cost (pick k))≤Kc*(Cscalar*control)*(2*T)^(3*ε)*
      Z^(B+scalarCap+8*SB+loss+((N:ℝ)+2)*plainCap+pad) := by
    rw [hcosteq]
    exact hh
  apply hsum.trans
  have h := mul_le_mul_of_nonneg_left hcub (by positivity : 0≤D*Z^(2*loss))
  convert h using 1
  rw [show B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad=
      2*loss+(B+scalarCap+8*SB+loss+((N:ℝ)+2)*plainCap+pad) by
        dsimp [SB,scalarCap]; ring,Real.rpow_add hzpos]
  ring

theorem actual_geometry_main_all_projector_coarse_family {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (column : Label→↥(firstLiveColumns (geometryFirstSource s R seed (Z^Dfirst) Z ξ hK bin) (fun _=>logAnnulus))),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (column l).val,
        (column l).val.2.1.val)) →
      let C := fun l=>geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      let χ := fun l=>geometryColumnCharacter reflected s R seed (Z^Dfirst) Z ξ hK bin (column l).val
      ∀alloc : (l : Label)→actualAllocations s.pools (C l),
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
      let hKm : ∀l,0<Kmain (first l) := fun l=>first_main_radius_pos reflected (Z^Dfirst) (volume s)
        Z ξ (3*a) reserve (zero_lt_one.trans hZ) (first l)
      let Index := (l : Label)×ActualSecondBlockIndex (source l) (R*C l) (projector l)
        (Kmain (first l)) (Tsec (first l)) Z ξ
      let datum := fun q : Index=>actualSecondBlockDatum (slots q.1) (source q.1) (R*C q.1) (projector q.1)
        (hprojector q.1) (hz₁ q.1) (hz₂ q.1) (Kmain (first q.1)) (Tsec (first q.1)) Z ξ (hKm q.1) q.2
      let block := fun q : Index=>(datum q).block
      ∀(rows : Finset (secondLiveRows block))(second : Bool)(W : 𝓢(ℝ,ℂ))(height : rows→ℝ)(Ds : rows→Finset (Ideal O))
        (control B₁ B₂ : ℝ),0≤ control → 0≤B₁ → 0≤B₂ →
      (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) → (B₁*B₂)^2≤ control →
      (∀r : rows,∀L∈Ds r,L∈(datum r.val.val.1).block.divisors ∧ Squarefree L) →
      let outer := fun r : rows=>(Kmain (first r.val.val.1.1)/volume (source r.val.val.1.1))*
        normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive/lowerFactor N lo ap
      let cost := fun r : rows=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
        (column r.val.val.1.1).val * outer r * highNormalizedRowCost second datum r.val (height r) (Ds r)
      (∑r : rows,cost r)≤K*control*
        Z^(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε) := by
  let exponent := B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
    8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad
  let L := ((N:ℝ)+2)*U
  have hfamily := actual_geometry_main_all_height_coarse_family
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε
  obtain ⟨K,hK,hfamily⟩ := hfamily
  have hpayment := shared_projector_shell_payment L pad (by positivity) hpad
  obtain ⟨Cp,hCp,hpayment⟩ := hpayment
  refine ⟨Cp*K*(2:ℝ)^(3*ε),by positivity,?_⟩
  filter_upwards [hfamily,hpayment] with Z hfam hp
  intro hZ Label _ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj C χ alloc halloc slots source first projector
    Kmain Tsec hprojector hz₁ hz₂ hKm Index datum block rows second W
    height Ds control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB hDs outer cost
  let projectors := sharedProjectors Ds
  let columnCost := fun (r : rows) (D : Ideal O)=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
      (column r.val.val.1.1).val*outer r*highNormalizedRowCost second datum r.val (height r) {D}
  have houter : ∀r : rows,0≤outer r := by
    intro r
    exact div_nonneg (mul_nonneg (div_nonneg (hKm _).le (volume_pos _).le)
      (normalizer_pos _ _ (datum r.val.val.1).hC _).le) (lowerFactor_pos N lo ap hlo hap).le
  have hnonneg : ∀r D,0≤ columnCost r D := by
    intro r D
    exact mul_nonneg (mul_nonneg
      (geometry_first_high_mass_nonneg reflected s R seed W Dfirst Z ξ εmass hKfirst bin _)
      (houter r)) (high_normalized_row_cost_nonneg second datum r.val (height r) {D})
  have hnorm : ∀r : rows,∀D∈Ds r,(D.absNorm:ℝ)≤Z^L := by
    intro r D hD
    apply (second_datum_projector_cap (datum r.val.val.1) N Z U
      ((live_card_le (alloc r.val.val.1.1).val).trans hα) hZ.le hU
      (actual_child_pool_cap s (C r.val.val.1.1) R (alloc r.val.val.1.1)
        (χ r.val.val.1.1) t (Z^U) hpool) D (hDs r D hD).1).2
  have hscale n (hn : n∈selectedShells projectors) :=
    shared_projector_shell_scale Ds Z L hnorm n hn
  have hZpos : 0<Z := zero_lt_one.trans hZ
  let E := K*control*(2:ℝ)^(3*ε)*Z^(exponent+3*L*ε)
  have hE : 0≤E := by dsimp [E]; positivity
  have hpay (n : ℤ)(hn : n∈selectedShells projectors) :
      (∑r : rows,∑D∈shell projectors n,columnCost r D)≤E := by
    have h := hfam hZ reflected s R seed Dfirst a reserve t hKfirst hseed he hlow hsource hA hMbox habox hω
      hM hwin hscales hP hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin column hinj alloc halloc
      rows second W height (fun _=>shell projectors n) control (dyadicScale n) B₁ B₂ hcontrol
      (hscale n hn).1 hB₁ hB₂ hW₁ hW₂ hcontrolB
      (fun _ D hD=>by
        have hd:=shared_projector_shell_gates Ds n D hD
        exact ⟨hd.1,hd.2.2⟩)
    have hleft : (∑r : rows,∑D∈shell projectors n,columnCost r D)=
        ∑r : rows,geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hKfirst bin
          (column r.val.val.1.1).val*outer r*
          highNormalizedRowCost second datum r.val (height r) (shell projectors n) := by
      simp only [columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
    rw [hleft]
    apply h.trans
    have hdyadic : 0<dyadicScale n := zero_lt_one.trans_le (hscale n hn).1
    have hpow : (2*dyadicScale n)^(3*ε)≤(2:ℝ)^(3*ε)*Z^(3*L*ε) := by
      calc
        _≤(2*Z^L)^(3*ε) := Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left (hscale n hn).2 (by norm_num)) (by positivity)
        _=_ := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZpos.le _),←Real.rpow_mul hZpos.le]
          congr 1
          ring_nf
    have hp := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le hcontrol))
      (Real.rpow_nonneg hZpos.le exponent)
    convert hp using 1
    dsimp [E]
    rw [Real.rpow_add hZpos]
    ring
  have h := hp.2 Ds (fun r D hD=>(hDs r D hD).2) hnorm columnCost E hnonneg hE hpay
  have hleft : (∑r : rows,cost r)=∑r : rows,∑D∈Ds r,columnCost r D := by
    simp only [cost,columnCost,highNormalizedRowCost,Finset.sum_singleton,Finset.mul_sum]
  rw [hleft]
  convert h using 1
  dsimp [E,exponent,L]
  rw [show B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε=
      pad+(B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+pad+3*(((N:ℝ)+2)*U)*ε) by ring,
    Real.rpow_add hZpos]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
