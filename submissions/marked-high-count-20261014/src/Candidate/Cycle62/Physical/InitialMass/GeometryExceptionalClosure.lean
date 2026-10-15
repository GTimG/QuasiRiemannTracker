import Candidate.Cycle62.Physical.InitialMass.GeometryExceptionalAggregate

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentSourceLiveColumn CenteredMomentFirstCanonicalFamily
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSectorLocalization RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationErrorEnergy CenteredMomentSecondExceptionalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor
open Cycle62Moment CenteredMomentRankinRadical
open CenteredMomentFirstAnnularInput CenteredMomentActive
open CenteredMomentCanonicalFirst CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstExceptionalChildPaid
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance closureSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Both actual restriction depths are finite before source labels, ideals,
allocations, heights or the large scale are selected. -/
abbrev GeometryExceptionalSlotMenu (ι : Type*) [Fintype ι] :=
  (Finset ι) ⊕ ((A : Finset ι) × Finset A)

def geometryExceptionalSlot (a : GeometryExceptionalSlotMenu ι) : Type _ :=
  match a with
  | .inl A => A
  | .inr a => a.2

instance (a : GeometryExceptionalSlotMenu ι) : Fintype (geometryExceptionalSlot a) := by
  cases a <;> dsimp only [geometryExceptionalSlot] <;> infer_instance

instance (a : GeometryExceptionalSlotMenu ι) : DecidableEq (geometryExceptionalSlot a) :=
  Classical.decEq _

def geometryExceptionalSlotEndpoint (e : ι→ℝ) (a : GeometryExceptionalSlotMenu ι) :
    geometryExceptionalSlot a→ℝ :=
  match a with
  | .inl _ => fun i=>e i.val
  | .inr _ => fun i=>e i.val.val

/-- One saved whole exceptional estimate serves every literal first child
and every literal twice child. No desired energy inequality is a premise. -/
theorem actual_geometry_saved_exceptional_sources
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ Bcap L Cr : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ) (hB : 0≤Bcap) (hL : 0≤L) (hCr : 0<Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤Ck ∧
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤Ideal.span {(72:O)} →
      ∃Kfix : ℝ,0<Kfix ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
        ∀s : Input ι,s.lo=lo → s.hi=hi →
        ∀(I R : Ideal O)(B : actualAllocations s.pools I)(τ : Character)(t : ℝ),
        geometryExceptionalSourceEstimate wlo whi (child s I R B τ t).lo
          (child s I R B τ t).hi W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z ∧
        ∀(Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s I R B τ t).pools (Q^k))
          (υ : Character)(v : ℝ),
        geometryExceptionalSourceEstimate wlo whi (twiceChild s I R B τ t Q k Bp υ v).lo
          (twiceChild s I R B τ t Q k Bp υ v).hi W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z := by
  obtain ⟨J,Sp,Ck,hCk,hfamily⟩ := actual_finite_slot_exceptional_uniform
    (geometryExceptionalSlot (ι:=ι)) wlo whi hwlo hwhi
    (geometryExceptionalSlotEndpoint lo) (geometryExceptionalSlotEndpoint hi)
    W ε δ θ Bcap L Cr hε hδ hθ hB hL hCr
  refine ⟨J,Sp,Ck,hCk,?_⟩
  intro Qfix hQ hQt hQ72
  obtain ⟨Kfix,hK,hbound⟩ := hfamily Qfix hQ hQt hQ72
  refine ⟨Kfix,hK,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨(hz (.inl ∅)).1,?_⟩
  intro s hlo hhi I R B τ t
  constructor
  · have hh := (hz (.inl (liveIndices B.val))).2
    change geometryExceptionalSourceEstimate wlo whi
      (fun i : liveIndices B.val=>lo i.val) (fun i : liveIndices B.val=>hi i.val)
      W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z at hh
    have hl : (child s I R B τ t).lo=(fun i=>lo i.val) := funext (fun i=>congrFun hlo i.val)
    have hu : (child s I R B τ t).hi=(fun i=>hi i.val) := funext (fun i=>congrFun hhi i.val)
    rw [hl,hu]
    exact hh
  · intro Q k Bp υ v
    have hh := (hz (.inr ⟨liveIndices B.val,liveIndices Bp.val⟩)).2
    change geometryExceptionalSourceEstimate wlo whi
      (fun i : liveIndices Bp.val=>lo i.val.val) (fun i : liveIndices Bp.val=>hi i.val.val)
      W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z at hh
    have hl : (twiceChild s I R B τ t Q k Bp υ v).lo=(fun i=>lo i.val.val) :=
      funext (fun i=>congrFun hlo i.val.val)
    have hu : (twiceChild s I R B τ t Q k Bp υ v).hi=(fun i=>hi i.val.val) :=
      funext (fun i=>congrFun hhi i.val.val)
    rw [hl,hu]
    exact hh

set_option linter.defProp false in
/-- Saved whole-source constants and actual admission close the literal
main allocation payment. Only original source and profile receipts remain
as inputs; the exceptional energy estimate is constructed here. -/
def actual_geometry_main_exceptional_closed
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :=
  let hsave := actual_geometry_saved_exceptional_sources wlo whi hwlo hwhi lo hi W
    ε δ θ 41 8 1 hε hδ hθ (by norm_num) (by norm_num) (by norm_num)
  let J := Classical.choose hsave
  let hj := Classical.choose_spec hsave
  let Sp := Classical.choose hj
  let hsp := Classical.choose_spec hj
  let Ck := Classical.choose hsp
  let hc := Classical.choose_spec hsp
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let hk := hc.2 Qfix hQ hQt hQ72
    let Kfix := Classical.choose hk
    let hK := Classical.choose_spec hk
    (Kfix,PLift.up (And.intro hK.1
      (Filter.Eventually.mono (hK.2.and
        (eventual_actual_geometry_main_exceptional_admission (ι:=ι) η N b bs hb hbs))
        (fun Z hz=>And.intro hz.1.1
          (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤s.P i) (p : Profiles wlo whi)
            (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsource : sourceRadius s≤Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤Z) (M ξ sigma reserve t : ℝ)
            (hKM : Z^M≤Z) (hξ : 0≤ξ) (hξ₁ : ξ≤1)
            (hsigma : 0≤sigma) (hreserve : 0≤reserve)
            (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (χ₀ : RayCharacter) (m : O)
            (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val
          let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hKMpos bin q.1.val
          let hadmit := hz.2.2 reflected s R seed (Z^M) ξ sigma reserve t hKMpos
            hη hcard hend hs hz₁ hz₂ hV hsource hRN hKM hξ hξ₁ hsigma hreserve bin q hne
          let hest := (hz.1.2 s hlo hhi I R q.2 τ t).1
          let hseed := actual_first_live_squarefree
            (geometryFirstSource s R seed (Z^M) Z ξ hKMpos bin)
            (fun _=>logAnnulus) q.1.val q.1.property
          actual_geometry_main_exceptional_paid reflected s R seed W M Z ξ sigma reserve t
            hZ bin q.1.val q.2 wlo whi p ε δ θ 41 8 1 J Sp Ck Qfix Kfix hK.1.le hc.1
            N b hb hend.1 hcard a₁ a₂ ha₁ ha₂ hs₁ hs₂ hest
            (fun i=>hsP i.val) hW₁ hW₂ (mul_ne_zero hR (allocation_ne s I q.2))
            hseed hseed.ne_zero hadmit.2.2.1 χ₀ m hm hml hm2
            (firstMainFourierScale reflected (Z^M) (volume s) Z ξ sigma reserve b N
              (geometryFirstLabel s R seed (Z^M) Z ξ hKMpos bin q.1.val))
            hadmit.1 (by simpa only [one_mul] using hadmit.2.1) hadmit.2.2.2 hne))))))

/-- Exposes the exact predicate of a saved eventual receipt without
changing it or assuming its conclusion. -/
def geometryExceptionalEventualPredicate {P : ℝ→Prop} (_ : ∀ᶠZ : ℝ in atTop,P Z) :
    ℝ→Prop := P

def geometryExceptionalActiveLift (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (Z ξ t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin) (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
      (Z^(1:ℝ)) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))) :
    actualAllocations (geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q).pools
        ((Ideal.span {p})^(errorIndex i+1)) :=
  errorActiveAllocation (geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t q) _ Bp

set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency false in
/-- The saved estimate and arithmetic admission also close the literal
lifted active prime-error payment, with its original projector seed and
local prime cost. The active menu is fixed before any row sum. -/
def actual_geometry_error_exceptional_closed
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs) :=
  let hsave := actual_geometry_saved_exceptional_sources wlo whi hwlo hwhi lo hi W
    ε δ θ 126 25 1 hε hδ hθ (by norm_num) (by norm_num) (by norm_num)
  let J := Classical.choose hsave
  let hj := Classical.choose_spec hsave
  let Sp := Classical.choose hj
  let hsp := Classical.choose_spec hj
  let Ck := Classical.choose hsp
  let hc := Classical.choose_spec hsp
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let hk := hc.2 Qfix hQ hQt hQ72
    let Kfix := Classical.choose hk
    let hK := Classical.choose_spec hk
    let hbound := hK.2.and
      (eventual_actual_geometry_error_exceptional_admission (ι:=ι) η N b bs hb hbs)
    (Kfix,PLift.up (And.intro hK.1 hbound),
      PLift.up (fun (Z : ℝ) (hz : geometryExceptionalEventualPredicate hbound Z)=>
          let hpayed := (fun (hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤s.P i) (p0 : Profiles wlo whi)
            (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsource : sourceRadius s≤Z^(3:ℝ))
            (hlogV : |Real.logb Z (volume s)|≤3) (hRN : (R.absNorm:ℝ)≤Z)
            (amp ξ reserve t : ℝ) (ha : 0≤amp) (ha₁ : amp≤1)
            (hξ : 0≤ξ) (hξ₁ : ξ≤1) (hreserve : 0≤reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (a₁ a₂ : ℝ) (ha₁p : 0<a₁) (ha₂p : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (p : O) (hp : p≠0)
            (hpN : ((Ideal.span {p}).absNorm:ℝ)≤Z^(3:ℝ))
            (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
              hKMpos bin t q).slots j→IsCoprime (Ideal.span {p}) I) (i : Fin 3)
            (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hKMpos bin t q)).pools ((Ideal.span {p})^(errorIndex i+1)))
            (υ : Character) (χ : RayCharacter) (v : ℝ)
            (hυ : υ.modulus.absNorm≤radicalBound (childCharacter
              (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val) χ)
                fixedBadMask p (errorMovingExponent (errorIndex i)))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val
          let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val
          let Q := Ideal.span {p}
          let Bplift := geometryExceptionalActiveLift reflected s R seed Z ξ t hZ bin q p i Bp
          let hadmit := hz.2.2 reflected s R seed amp ξ reserve t hZ hη hcard hend hs hz₁ hz₂
            hV hsource hlogV hRN ha ha₁ hξ hξ₁ hreserve hω bin q hne p hp hpN hslot i Bp υ χ v hυ
          let hest := (hz.1.2 s hlo hhi I R q.2 τ t).2 Q (errorIndex i+1) Bplift υ v
          let hseed := actual_first_live_squarefree
            (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (fun _=>logAnnulus) q.1.val q.1.property
          actual_geometry_error_exceptional_paid reflected s R seed W 1 Z ξ (3*amp) reserve t
            hZ bin q.1.val q.2 wlo whi p0 ε δ θ 126 25 1 J Sp Ck Qfix Kfix hK.1.le hc.1
            N b hb hend.1 hcard a₁ a₂ ha₁p ha₂p hs₁ hs₂ p hp (errorIndex i+1) Bplift υ v hslot
            hest (fun j=>hsP j.val.val) hW₁ hW₂
            (mul_ne_zero (mul_ne_zero hR (allocation_ne s I q.2))
              (pow_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr hp)))
            hseed hseed.ne_zero hadmit.2.2.1 χ₀ m hm hml hm2
            (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ bin q p i)
            hadmit.1 (by simpa only [one_mul] using hadmit.2.1) hadmit.2.2.2 hne)
          And.intro hz.1.1 hpayed)))

/-- Actual label-dependent projector menus are enlarged to their common
union before either reciprocal is paid. The physical D shell remains H
on the left and 1/H on the reflected right. -/
theorem eventual_actual_exceptional_physical_projector_payment (B L ε : ℝ)
    (hB : 0≤B) (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,2≤Z ∧
      ∀(reflected : Bool)(T H factor : ℝ),0<T → T≤Z^B → 0<H → 0≤factor →
      ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,T≤((commonRadical l.1.1 l.1.2).absNorm:ℝ) ∧
        ((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤2*T) →
      (∀l∈labels,H≤(l.1.2.absNorm:ℝ) ∧ (l.1.2.absNorm:ℝ)≤2*H) →
      ∀Ds : FirstSourceLabel→Finset (Ideal O),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,(D.absNorm:ℝ)≤Z^L) →
      (∑l∈labels,∑D∈Ds l,
        (if reflected then 1/(l.1.2.absNorm:ℝ) else (l.1.2.absNorm:ℝ))*factor/
          (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ)))≤
        (if reflected then 1/H else 2*H)*C*factor*Z^(2*ε)/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := eventual_exceptional_radical_projector_payment B L ε hB hL hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro reflected T H factor hT hTZ hH hf seed hs hs0 labels hsup heq hseed hnorm hrad hphysical
    Ds hDs hcap
  let union := labels.biUnion Ds
  let P := if reflected then 1/H else 2*H
  have hP : 0≤P := by dsimp only [P]; split_ifs <;> positivity
  have hunion : ∀D∈union,Squarefree D := by
    intro D hD
    obtain ⟨l,hl,hDl⟩ := Finset.mem_biUnion.mp hD
    exact hDs l hl D hDl
  have hucap : ∀D∈union,(D.absNorm:ℝ)≤Z^L := by
    intro D hD
    obtain ⟨l,hl,hDl⟩ := Finset.mem_biUnion.mp hD
    exact hcap l hl D hDl
  have hc := hz.2 T factor hT hTZ hf seed hs hs0 labels hsup heq hseed hnorm hrad
    union hunion hucap
  calc
    _≤∑l∈labels,∑D∈union,P*(factor/
        (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ))) := by
      apply Finset.sum_le_sum
      intro l hl
      calc
        _≤∑D∈Ds l,P*(factor/
            (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ))) := by
          apply Finset.sum_le_sum
          intro D hD
          have hp : (if reflected then 1/(l.1.2.absNorm:ℝ) else (l.1.2.absNorm:ℝ))≤P := by
            dsimp only [P]
            split_ifs
            · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical l hl).1
            · exact (hphysical l hl).2
          have hfactor : 0≤factor/
              (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ)) :=
            div_nonneg hf (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          have hh := mul_le_mul_of_nonneg_right hp hfactor
          simpa only [mul_div_assoc] using hh
        _≤_ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_biUnion_of_mem Ds hl)
          (fun D _ _=>mul_nonneg hP
            (div_nonneg hf (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    _=P*(∑l∈labels,∑D∈union,factor/
        (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ))) := by
      simp only [Finset.mul_sum]
    _≤P*(C*factor*Z^(2*ε)/(seed.absNorm:ℝ)) := mul_le_mul_of_nonneg_left hc hP
    _=_ := by dsimp only [P]; ring

/-- The original lower endpoint pays every actual restricted lower factor;
empty restrictions are included. -/
def geometryExceptionalLowerConstant (N : ℕ) (lo wlo : ℝ) : ℝ :=
  ((min 1 lo)^N*wlo*wlo)^(-2/3:ℝ)

theorem actual_geometry_exceptional_lower_factor {α : Type*} [Fintype α]
    (s : Input α) (N : ℕ) (lo wlo : ℝ) (hn : Fintype.card α≤N)
    (hlo : 0<lo) (hl : lo≤s.lower) (hwlo : 0<wlo) :
    ((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)≤geometryExceptionalLowerConstant N lo wlo := by
  have hp : (min 1 lo)^N≤∏i,s.lo i := by
    apply (pow_le_pow_of_le_one (lt_min zero_lt_one hlo).le (min_le_left _ _) hn).trans
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod₀ (s:=Finset.univ) (f:=fun _ : α=>min 1 lo)
        (g:=fun i=>s.lo i) (fun _ _=>(lt_min zero_lt_one hlo).le)
        (fun i _=>(min_le_right _ _).trans (hl.trans (s.lower_le i)))
  exact Real.rpow_le_rpow_of_nonpos
    (mul_pos (mul_pos (pow_pos (lt_min zero_lt_one hlo) _) hwlo) hwlo)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hwlo.le) hwlo.le)
    (by norm_num)

omit [DecidableEq ι] in
theorem actual_geometry_exceptional_child_lower_payments
    (s : Input ι) (N : ℕ) (lo wlo : ℝ) (hn : Fintype.card ι≤N)
    (hlo : 0<lo) (hl : lo≤s.lower) (hwlo : 0<wlo)
    (I R : Ideal O) (B : actualAllocations s.pools I) (τ : Character) (t : ℝ) :
    ((∏i,(child s I R B τ t).lo i)*wlo*wlo)^(-2/3:ℝ)≤
      geometryExceptionalLowerConstant N lo wlo ∧
    ∀(Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s I R B τ t).pools (Q^k))
      (υ : Character)(v : ℝ),
    ((∏i,(twiceChild s I R B τ t Q k Bp υ v).lo i)*wlo*wlo)^(-2/3:ℝ)≤
      geometryExceptionalLowerConstant N lo wlo := by
  constructor
  · exact actual_geometry_exceptional_lower_factor (child s I R B τ t) N lo wlo
      ((live_card_le B.val).trans hn) hlo hl hwlo
  · intro Q k Bp υ v
    exact actual_geometry_exceptional_lower_factor (twiceChild s I R B τ t Q k Bp υ v)
      N lo wlo ((live_card_le Bp.val).trans ((live_card_le B.val).trans hn)) hlo hl hwlo

/-- The actual main radius is the radius in the exceptional reference in
either orientation. The denominator retains the original active conductor. -/
theorem geometry_exceptional_main_reference_radius (reflected : Bool)
    (τ : Character) (l : FirstSourceLabel) (K X Z ξ sigma reserve r : ℝ) :
    geometryExceptionalMainReference τ
      (if reflected then l.1.2 else l.1.1)
      (if reflected then l.1.1 else l.1.2)
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val})
      K X Z sigma (frequencyLoss Z 32 ξ) reserve r=
    let I := if reflected then l.1.2 else l.1.1
    let H := if reflected then l.1.1 else l.1.2
    (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6))*
      (X/(I.absNorm:ℝ))^(1/3:ℝ)*
      (firstMainRadius reflected K X Z ξ sigma reserve l)^(5/6:ℝ)*
      Z^(-sigma/3)*Z^(-2*max r 0/3) := by
  cases reflected
  · simp only [geometryExceptionalMainReference,firstMainRadius,Bool.false_eq_true,
      ↓reduceIte]
    ring
  · simp only [geometryExceptionalMainReference,firstMainRadius,↓reduceIte]
    rw [CenteredMomentFirstMixedRightTransport.nominalLog_swap l.1.1 l.1.2,
      CenteredMomentFirstMixedRoot.active_span_swap l.1.1 l.1.2]
    ring

omit [DecidableEq ι] in
/-- The saved main reference contraction controls the literal main radius,
with the original active-conductor denominator in both orientations. -/
theorem actual_geometry_main_exceptional_radius_bound
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (M Z ξ sigma reserve t : ℝ) (hZ : 1<Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    (plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₂) :
    let l := geometryFirstLabel s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let I := if reflected then l.1.2 else l.1.1
    let H := if reflected then l.1.1 else l.1.2
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let X := geometryExceptionalVolume s
    (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6))*
      (X/(I.absNorm:ℝ))^(1/3:ℝ)*
      (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)^(5/6:ℝ)*
      Z^(-sigma/3)*Z^(-2*max (inputCap Z (child s I R B τ t)) 0/3)≤
    Z^(Real.logb Z X-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let l := geometryFirstLabel s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let I := if reflected then l.1.2 else l.1.1
  let H := if reflected then l.1.1 else l.1.2
  let E := Ideal.span {primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val}
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let X := geometryExceptionalVolume s
  let r := inputCap Z (child s I R B τ t)
  have href := actual_geometry_main_exceptional_reference_bound reflected s R seed M Z ξ
    sigma reserve t hZ bin j B plainLoss hX₁ hX₂ hY₁ hY₂
  have he : geometryMainExceptionalReferenceActual reflected s R seed M Z ξ
      sigma reserve t hZ bin j B=
      geometryExceptionalMainReference τ I H E (Z^M) X Z sigma
        (frequencyLoss Z 32 ξ) reserve r := by
    change (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor I H}).absNorm:ℝ)) 0/6))*
      (X/(I.absNorm:ℝ))^(1/3:ℝ)*
      (mainCommonRadius Z (Real.logb Z (H.absNorm:ℝ)) (nominalLog I H E (Z^M) X Z)
        (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve)^(5/6:ℝ)*
      Z^(-sigma/3)*Z^(-2*max r 0/3)=_
    dsimp only [geometryExceptionalMainReference]
    ring
  rw [he,geometry_exceptional_main_reference_radius reflected τ l] at href
  exact href

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_saved_exceptional_sources
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_main_exceptional_closed
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_error_exceptional_closed
#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_actual_exceptional_physical_projector_payment
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_exceptional_lower_factor
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_exceptional_child_lower_payments
#print axioms OAI.SevenEighths.Cycle62InitialMass.geometry_exceptional_main_reference_radius
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_main_exceptional_radius_bound
