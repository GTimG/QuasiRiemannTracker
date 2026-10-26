/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B136
import Candidate.Bundles.B154
import Candidate.Bundles.B155
import Candidate.Bundles.B156
import Candidate.Bundles.B157

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalClosure; sha256 2b4eccaaeb8593582989e9b6232283ee4490fe8d53189d5d6b5da93857cac87e -/
section
                                                                

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
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
open Cycle61Moment CenteredMomentRankinRadical
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ Bcap L Cr : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ) (hB : 0≤ Bcap) (hL : 0≤ L) (hCr : 0< Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤ Ck ∧
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤ Ideal.span {(72:O)} →
      ∃Kfix : ℝ,0< Kfix ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :=
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
          (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p : Profiles wlo whi)
            (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤ Z) (M ξ sigma reserve t : ℝ)
            (hKM : Z^M≤ Z) (hξ : 0≤ξ) (hξ₁ : ξ≤1)
            (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
            (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
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
def geometryExceptionalEventualPredicate {P : ℝ→ Prop} (_ : ∀ᶠZ : ℝ in atTop,P Z) :
    ℝ→ Prop := P

def geometryExceptionalActiveLift (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (Z ξ t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
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
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs) :=
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
          let hpayed := (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hsP : ∀i,1≤ s.P i) (p0 : Profiles wlo whi)
            (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hlogV : |Real.logb Z (volume s)|≤3) (hRN : (R.absNorm:ℝ)≤ Z)
            (amp ξ reserve t : ℝ) (ha : 0≤ amp) (ha₁ : amp≤1)
            (hξ : 0≤ξ) (hξ₁ : ξ≤1) (hreserve : 0≤ reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (a₁ a₂ : ℝ) (ha₁p : 0< a₁) (ha₂p : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
            (reflected : Bool) (bin : ℤ×(Fin 5→ℤ))=>
          let hKMpos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
          fun (q : GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin)
            (hne : frozenCoefficient q.2.val
              (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hKMpos bin q.1.val)
              R s.ν s.W s.P≠0) (p : O) (hp : p≠0)
            (hpN : ((Ideal.span {p}).absNorm:ℝ)≤ Z^(3:ℝ))
            (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ
              hKMpos bin t q).slots j→ IsCoprime (Ideal.span {p}) I) (i : Fin 3)
            (Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hKMpos bin t q)).pools ((Ideal.span {p})^(errorIndex i+1)))
            (υ : Character) (χ : RayCharacter) (v : ℝ)
            (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter
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
    (hB : 0≤ B) (hL : 0≤ L) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,2≤ Z ∧
      ∀(reflected : Bool)(T H factor : ℝ),0< T → T≤ Z^B → 0< H → 0≤ factor →
      ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤ Z^B ∧ (l.1.2.absNorm:ℝ)≤ Z^B) →
      (∀l∈labels,T≤((commonRadical l.1.1 l.1.2).absNorm:ℝ) ∧
        ((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤2*T) →
      (∀l∈labels,H≤(l.1.2.absNorm:ℝ) ∧ (l.1.2.absNorm:ℝ)≤2*H) →
      ∀Ds : FirstSourceLabel→ Finset (Ideal O),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,(D.absNorm:ℝ)≤ Z^L) →
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
  have hP : 0≤ P := by dsimp only [P]; split_ifs <;> positivity
  have hunion : ∀D∈union,Squarefree D := by
    intro D hD
    obtain ⟨l,hl,hDl⟩ := Finset.mem_biUnion.mp hD
    exact hDs l hl D hDl
  have hucap : ∀D∈union,(D.absNorm:ℝ)≤ Z^L := by
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
          have hp : (if reflected then 1/(l.1.2.absNorm:ℝ) else (l.1.2.absNorm:ℝ))≤ P := by
            dsimp only [P]
            split_ifs
            · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical l hl).1
            · exact (hphysical l hl).2
          have hfactor : 0≤ factor/
              (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ)) :=
            div_nonneg hf (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          have hh := mul_le_mul_of_nonneg_right hp hfactor
          simpa only [mul_div_assoc] using hh
        _≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_biUnion_of_mem Ds hl)
          (fun D _ _=>mul_nonneg hP
            (div_nonneg hf (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
    _=P*(∑l∈labels,∑D∈union,factor/
        (((commonRadical l.1.1 l.1.2).absNorm:ℝ)*(D.absNorm:ℝ))) := by
      simp only [Finset.mul_sum]
    _≤ P*(C*factor*Z^(2*ε)/(seed.absNorm:ℝ)) := mul_le_mul_of_nonneg_left hc hP
    _=_ := by dsimp only [P]; ring

/-- The original lower endpoint pays every actual restricted lower factor;
empty restrictions are included. -/
def geometryExceptionalLowerConstant (N : ℕ) (lo wlo : ℝ) : ℝ :=
  ((min 1 lo)^N*wlo*wlo)^(-2/3:ℝ)

theorem actual_geometry_exceptional_lower_factor {α : Type*} [Fintype α]
    (s : Input α) (N : ℕ) (lo wlo : ℝ) (hn : Fintype.card α≤ N)
    (hlo : 0< lo) (hl : lo≤ s.lower) (hwlo : 0< wlo) :
    ((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)≤ geometryExceptionalLowerConstant N lo wlo := by
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
    (s : Input ι) (N : ℕ) (lo wlo : ℝ) (hn : Fintype.card ι≤ N)
    (hlo : 0< lo) (hl : lo≤ s.lower) (hwlo : 0< wlo)
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
    (M Z ξ sigma reserve t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    (plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_saved_exceptional_sources
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_closed
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_error_exceptional_closed
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_exceptional_physical_projector_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_lower_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_exceptional_child_lower_payments
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_exceptional_main_reference_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_radius_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalClosure -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalFullPayment; sha256 a0a9cc2eb5c19e5658da03059062f661a66a388b0f773d66a72b1bdac1a6b3d4 -/
section
                                                              
                                                              
                                                          

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentSourceLiveColumn CenteredMomentCanonicalFirst
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondHeightFamily CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFirstExceptionalChildPaid
open CenteredMomentSecondExceptionalFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentAllocationCost CenteredMomentSourceMass CenteredMomentLogDyadic
open CenteredMomentSecondEnergySplit CenteredMomentAmplificationErrorEnergy
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildSourceCaps
open CenteredMomentPrimeElements
open CenteredMomentPrimePool
open CenteredMomentFirstPhysicalSource CenteredMomentRankinRadical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance fullExceptionalSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Every original allocation is summed, and cancelled frozen coefficients
contribute zero before the whole exceptional part energy is normalized. -/
def geometryExceptionalMainRowMass (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (M Z ξ sigma reserve t : ℝ) (hZ : 1< Z)
    (N : ℕ) (b : ℝ) (bin : ℤ×(Fin 5→ℤ)) (Qfix : Ideal O)
    (χ₀ : RayCharacter) (m : O)
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin)) : ℝ :=
  let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  let l := geometryFirstLabel s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  ∑B : actualAllocations s.pools I,
    if frozenCoefficient B.val I R s.ν s.W s.P≠0 then
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
        (Real.logb Z (geometryExceptionalVolume s))
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin
        (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j B*
      (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
        (coefficient (child s I R B τ t) (R*I) j.2.1.val) W
        (firstMainRadius reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve l)
        (firstMainFourierScale reflected (Z^M) (geometryExceptionalVolume s) Z ξ sigma reserve b N l)
        Z ξ (sourceRadius (child s I R B τ t))‖/geometryExceptionalVolume (child s I R B τ t))
    else 0

private theorem full_error_reference_orientation (reflected : Bool)
    (τ : Character) (l : FirstSourceLabel) (K X Z ξ sigma reserve r : ℝ) (p : O) (k : ℕ) :
    geometryExceptionalErrorReference τ
      (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val})
      K X Z sigma (frequencyLoss Z 32 ξ) reserve r p k=
    let I := if reflected then l.1.2 else l.1.1
    let H := if reflected then l.1.1 else l.1.2
    (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
      Z^(max (3*Real.logb Z (I.absNorm:ℝ)-5*Real.logb Z (H.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6))*
      localErrorCost p (k-1)*(X/(I.absNorm:ℝ)/(normValue p)^k)^(1/3:ℝ)*
      (errorCommonRadius Z (Real.logb Z (H.absNorm:ℝ))
        (nominalLog l.1.1 l.1.2
          (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val}) K X Z)
        (Real.logb Z (I.absNorm:ℝ)) sigma (frequencyLoss Z 32 ξ) reserve p k)^(5/6:ℝ)*
      Z^(-2*max r 0/3) := by
  cases reflected
  · simp only [geometryExceptionalErrorReference,Bool.false_eq_true,↓reduceIte]
    ring
  · simp only [geometryExceptionalErrorReference,↓reduceIte]
    rw [nominalLog_swap l.1.1 l.1.2,active_span_swap l.1.1 l.1.2]
    ring

omit [DecidableEq ι] in
theorem actual_geometry_full_error_reference
    (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (M Z ξ amp reserve t : ℝ) (hZ : 1< Z) (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j))
    (Mprime : Ideal O) [NeZero Mprime] (Hprime : Subgroup (O⧸Mprime)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^amp)))
    (i : Fin 3)
    (Bp : actualAllocations (child s
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) R B
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j) t).pools
      ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v plainLoss : ℝ)
    (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
    (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
    (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
    (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂) :
    let src := geometryFirstSource s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
    let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
    geometryExceptionalErrorReference τ I (if reflected then src.C else src.D)
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      (Z^M) (geometryExceptionalVolume s) Z (3*amp) (frequencyLoss Z 32 ξ) reserve
      (inputCap Z (twiceChild s I R B τ t (Ideal.span {p}) (errorIndex i+1) Bp υ v))
      p (errorIndex i+1)≤
      Z^(Real.logb Z (geometryExceptionalVolume s)-
        (M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
        3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j.1
  have hk : errorIndex i+1=1 ∨ errorIndex i+1=6 ∨ errorIndex i+1=7 := by
    fin_cases i <;> norm_num [errorIndex]
  have hp' : p∈elementPool (primePool Mprime Hprime Sbad (1/2) 1 (Z^((3*amp)/3))) := by
    simpa only [show (3*amp)/3=amp by ring] using hp
  have hklog : Real.logb Z (Z^M)=M := Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hm := actual_geometry_column_modulus reflected s R seed (Z^M) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j
  cases reflected
  · have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter false s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.C src.D
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hC src.hD src.sameSupport src.inactive rfl s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh
  · have hm' : (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j).modulus=
        s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
          Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.D src.C=>q.val)
            (swapSubset src.C src.D src.inactive)*activeConductor src.D src.C} := by
      rw [swapped_modulus_factor]
      exact hm
    have hh := actual_error_twice_exceptional_reference s.η
      (geometryColumnCharacter true s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) bin j)
      src.D src.C
      (Ideal.span {primeSubsetGenerator (fun q : CommonIndex src.C src.D=>q.val) src.inactive})
      src.hD src.hC src.sameSupport.symm (swapSubset src.C src.D src.inactive)
      (by rw [swapSubset_generator]) s R B (Z^M) Z (3*amp)
      (frequencyLoss Z 32 ξ) reserve t plainLoss
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) hZ hm'
      Mprime Hprime Sbad hbad p hp' (errorIndex i+1) hk Bp υ v
      (by simpa only [hklog] using hX₁) (by simpa only [hklog] using hX₂)
      (by simpa only [hklog] using hY₁) (by simpa only [hklog] using hY₂)
    rw [hklog] at hh
    exact hh

private theorem full_main_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D Control bro q volumeRoot kr mr Rpow : ℝ)
    (hpaid : E≤ S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤ Shell) (hlower : lower≤ L) (href : q*volumeRoot*kr*mr≤ Rpow)
    (hS : 0≤ S) (hShell : 0≤ Shell) (hF : 0≤ F) (hA : 0≤ A)
    (hP : 0≤ Pz) (hl : 0≤ lower) (hL : 0≤ L) (hD : 0≤ D)
    (hc : 0≤ Control) (hb : 0≤ bro) (hq : 0≤ q) (hi : 0≤ volumeRoot)
    (hk : 0≤ kr) (hm : 0≤ mr) :
    E≤ Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤ rest := by dsimp only [rest]; positivity
  calc
    E≤(Ck*Cprof)*rest := by convert hpaid using 1; dsimp only [rest]; ring
    _≤ max 1 (Ck*Cprof)*rest := mul_le_mul_of_nonneg_right (le_max_right _ _) hrest
    _≤ max 1 (Ck*Cprof)*(Shell*F*A*Pz*(L/D)*Control*bro*Rpow) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left _ _))
      dsimp only [rest]
      gcongr
    _=_ := by ring

private theorem full_main_paid_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D c height mass bro q root kr m₁ m₂ Rpow : ℝ)
    (hpaid : E≤(S*F*q)*A*(Ck*Pz*m₁*m₂*kr*lower/D)*
      ((Cprof*c*height*mass)*(bro*root)))
    (hside : S≤ Shell) (hlower : lower≤ L) (href : q*root*kr*m₁*m₂≤ Rpow)
    (hS : 0≤ S) (hShell : 0≤ Shell) (hF : 0≤ F) (hA : 0≤ A)
    (hP : 0≤ Pz) (hl : 0≤ lower) (hL : 0≤ L) (hD : 0≤ D)
    (hc : 0≤ c*height*mass) (hb : 0≤ bro) (hq : 0≤ q) (hi : 0≤ root)
    (hk : 0≤ kr) (hm : 0≤ m₁*m₂) :
    E≤ Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*(c*height*mass)*bro*Rpow := by
  exact full_main_fold_algebra E S Shell F A Ck Cprof Pz lower L D
    (c*height*mass) bro q root kr (m₁*m₂) Rpow
    (by convert hpaid using 1; ring) hside hlower
    (by convert href using 1; ring) hS hShell hF hA hP hl hL hD hc hb hq hi hk hm

set_option linter.defProp false in
/-- The complete supported main family derives its allocation costs from
the saved whole exceptional estimate. The original projector and radical
are paid jointly before all four dyads and both rays are counted. -/
def actual_geometry_main_exceptional_full
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (N : ℕ) (b bs : ℝ) (hb : 1≤ b) (hbs : 1≤ bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0< slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1) :=
  let closed := actual_geometry_main_exceptional_closed wlo whi hwlo hwhi lo hi W
    ε δ θ hε hδ hθ η N b bs hb hbs
  let J := closed.1
  let Sp := closed.2.1
  let Ck := closed.2.2.1
  let halloc := actualAllocations_uniform_small_power (N+2) (εalloc/2) (half_pos hea)
  let Da := Classical.choose halloc
  let hDa := Classical.choose_spec halloc
  let hcolumns := eventual_actual_zero_column_payment (ι:=ι) 2 0 3
    (((N:ℝ)+2)*3) ξ εcount (by norm_num) (by norm_num) (by norm_num)
    (by positivity) hξ hec
  let Cd := Classical.choose hcolumns
  let hCd := Classical.choose_spec hcolumns
  (J,Sp,Ck,fun (Qfix : Ideal O) hQ hQt hQ72=>
    let saved := closed.2.2.2 Qfix hQ hQt hQ72
    let Kfix := saved.1
    (Kfix,Cd,Da,PLift.up (And.intro saved.2.down.1 (And.intro hCd.1 (And.intro hDa.1
      (Filter.Eventually.mono (saved.2.down.2.and hCd.2)
        (fun Z hz=>And.intro hz.1.1
          (fun (hZ : 1< Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hcard : Fintype.card ι≤ N) (hend : Endpoints b bs bs s)
            (hlower : slotlo≤ s.lower) (hsP : ∀i,1≤ s.P i)
            (p : Profiles wlo whi) (hW₁ : s.W₁=p.profile 0) (hW₂ : s.W₂=p.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤ Z^(2:ℝ)) (hsourcepos : 0< sourceRadius s)
            (hsource : sourceRadius s≤ Z^(3:ℝ))
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤ Z) (M sigma reserve t plainLoss : ℝ)
            (hM : 0≤ M) (hKM : Z^M≤ Z) (hsigma : 0≤ sigma) (hreserve : 0≤ reserve)
            (hX₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₁)
            (hX₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.X₂)
            (hY₁ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₁)
            (hY₂ : Z^((M+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤ s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0< a₁) (ha₂ : 0< a₂)
            (hs₁ : ∀x,s.W₁ x≠0→ a₁≤ x) (hs₂ : ∀x,s.W₂ x≠0→ a₂≤ x)
            (reflected : Bool) (bin : ℤ×(Fin 5→ℤ))
            (χ₀ : RayCharacter) (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)=>
          let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M
          let rows := firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
            (fun _=>logAnnulus)
          by
          have hZpos : 0< Z := zero_lt_one.trans hZ
          let Hshell := Z^((bin.2 1:ℝ)*Real.logb Z 2)
          have hH : 0< Hshell := Real.rpow_pos_of_pos hZpos _
          have hphysical (j : rows) : Hshell≤
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ) ∧
              ((geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1).D.absNorm:ℝ)≤2*Hshell := by
            have hr := actual_geometry_fiber_range s R seed (Z^M) Z ξ 3 hZ hs hz₁ hz₂
              hsource bin j.val.1 1
            have hn := actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂
              hsource j.val.1.val 1
            have hl := Real.rpow_le_rpow_of_exponent_le hZ.le hr.1
            have hu := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2.le
            rw [geometryExponents,Real.rpow_logb hZpos hZ.ne' (zero_lt_one.trans_le hn.1)] at hl hu
            have he : Z^(((bin.2 1:ℝ)+1)*Real.logb Z 2)=2*Hshell := by
              rw [add_mul,one_mul,Real.rpow_add hZpos,
                Real.rpow_logb hZpos hZ.ne' (by norm_num : (0:ℝ)<2)]
              exact mul_comm _ _
            exact ⟨hl,hu.trans_eq he⟩
          have hfixed : 0< fixedPresentationCost := fixedPresentationCost_pos
          let Control := p.control Sp^2*(1+‖t‖)^(2*J)*(∏i,s.M i)^6
          let Shell := if reflected then 1/Hshell
            else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
          let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
            N b J Qfix Kfix)
          let factor := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
            coef*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Da^2
          let exponent := 2*ε+2*δ+2*41*θ+sigma/3+
            Real.logb Z (geometryExceptionalVolume s)-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
            4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
          let cost := fun j : rows=>geometryExceptionalMainRowMass reflected s R seed W
            M Z ξ sigma reserve t hZ N b bin Qfix χ₀ m j.val
          have hShell : 0≤ Shell := by dsimp only [Shell]; split_ifs <;> positivity
          have hLower : 0≤ geometryExceptionalLowerConstant N slotlo wlo :=
            Real.rpow_nonneg (by positivity) _
          have hControl : 0≤ Control := by dsimp only [Control]; positivity
          have hfactor : 0≤ factor := by dsimp only [factor,coef]; positivity
          have hc : ∀j : rows,0≤ cost j := by
            intro j
            unfold cost geometryExceptionalMainRowMass
            apply Finset.sum_nonneg
            intro B _
            split_ifs
            · exact mul_nonneg (geometryAllocationWeight_nonneg ..)
                (div_nonneg (norm_nonneg _) (CenteredMomentExceptionalAmplitudePair.volume_pos _).le)
            · exact le_rfl
          have hcost : ∀j : rows,cost j≤ factor*
              Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/
                (j.val.2.1.val.absNorm:ℝ) := by
            intro j
            let l := geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.val
            let I := geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.val
            let τ := geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.val
            let src := geometryFirstSource s R seed (Z^M) Z ξ hK bin j.val.1
            let X := geometryExceptionalVolume s
            let Pz := Z^(2*ε+2*δ+2*41*θ+sigma/3)
            let Rpow := Z^(Real.logb Z X-(M+Real.logb Z (s.η.modulus.absNorm:ℝ))+
              4*sigma/3+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3)
            let rad := ((commonRadical src.C src.D).absNorm:ℝ)
            let Dproj := (j.val.2.1.val.absNorm:ℝ)
            let G := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
              coef*Pz*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Rpow
            have hG : 0≤ G := by dsimp only [G,coef,Pz,Rpow]; positivity
            have hrad : 0< rad := CenteredMomentFirstScale.norm_pos _ (commonRadical_ne_zero _ _)
            have hDproj : 0< Dproj := CenteredMomentFirstScale.norm_pos _
              (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
                (fun _=>logAnnulus) j.val j.property).ne_zero
            have hpoint (B : actualAllocations s.pools I)
                (hne : frozenCoefficient B.val I R s.ν s.W s.P≠0) :
                geometryAllocationWeight reflected s R seed (Z^M) Z ξ M (Real.logb Z X) hK bin
                  (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)) N b j.val B*
                (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset (child s I R B τ t).pools))
                  (coefficient (child s I R B τ t) (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius (child s I R B τ t))‖/geometryExceptionalVolume (child s I R B τ t))≤
                ((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
              let u := child s I R B τ t
              have hXpos : 0< X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
              have hIpos : 0<(I.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ (allocation_ne s I B)
              have hτpos : 0<(τ.modulus.absNorm:ℝ) :=
                CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
              have hbase : 0≤(∏i,u.lo i)*wlo*wlo := mul_nonneg
                (mul_nonneg (Finset.prod_nonneg (fun i _=>(u.lo_pos i).le)) hwlo.le) hwlo.le
              let den := (τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
                Z^(max (3*Real.logb Z (I.absNorm:ℝ)-
                  5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                  Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6)
              let qfac := (X/(I.absNorm:ℝ))/den
              let mr := Z^(-sigma/3)*Z^(-2*max (inputCap Z u) 0/3)
              let kr := (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)^(5/6:ℝ)
              let lower := ((∏i,u.lo i)*wlo*wlo)^(-2/3:ℝ)
              let side := if reflected then 1/(src.D.absNorm:ℝ)
                else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)
              have hpayed := hz.1.2 hZ s hlo hhi hη hcard hend hsP p hW₁ hW₂ R seed hR hs
                hz₁ hz₂ hV hsource hRN M ξ sigma reserve t hKM hξ hξ₁ hsigma hreserve
                a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected bin (⟨j,B⟩ : GeometryLowFirstIndex
                  reflected s R seed (Z^M) Z ξ hK bin) hne χ₀ m hm hml hm2
              have hlogs :
                  (if reflected then max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6 else
                    max (3*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 0-
                    5*geometryExponents s R seed (Z^M) Z ξ j.val.1.val 1-
                    geometryExponents s R seed (Z^M) Z ξ j.val.1.val 3) 0/6)=
                  max (3*Real.logb Z (I.absNorm:ℝ)-
                    5*Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)-
                    Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)) 0/6 := by
                cases reflected <;> rfl
              dsimp only at hpayed
              rw [hlogs] at hpayed
              have href := actual_geometry_main_exceptional_radius_bound reflected s R seed
                M Z ξ sigma reserve t hZ bin j.val B plainLoss hX₁ hX₂ hY₁ hY₂
              have hlow := actual_geometry_exceptional_lower_factor u N slotlo wlo
                ((live_card_le B.val).trans hcard) hslot hlower hwlo
              have hside : side≤ Shell := by
                dsimp only [side,Shell]
                split_ifs
                · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
                · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
              have hqfac : 0≤ qfac := by dsimp only [qfac,den]; positivity
              have hside0 : 0≤ side := by dsimp only [side]; split_ifs <;> positivity
              let Enamed := geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
                (Real.logb Z X) hK bin (fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q))
                N b j.val B*
                (‖partEnergy true τ χ₀ Qfix m t (finiteColumns (Fintype.piFinset u.pools))
                  (coefficient u (R*I) j.val.2.1.val) W
                  (firstMainRadius reflected (Z^M) X Z ξ sigma reserve l)
                  (firstMainFourierScale reflected (Z^M) X Z ξ sigma reserve b N l)
                  Z ξ (sourceRadius u)‖/geometryExceptionalVolume u)
              have hh := full_main_paid_fold_algebra Enamed side Shell
                (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad)
                ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
                (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
                Pz lower (geometryExceptionalLowerConstant N slotlo wlo) Dproj
                (p.control Sp^2) ((1+‖t‖)^(2*J)) ((∏i,s.M i)^6)
                ((b^N)^(1/3:ℝ)) qfac ((X/(I.absNorm:ℝ))^(1/3:ℝ)) kr
                (Z^(-sigma/3)) (Z^(-2*max (inputCap Z u) 0/3)) Rpow
                hpayed hside hlow href
                hside0 hShell
                (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le)
                (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _)
                  (Nat.cast_nonneg _))
                (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hbase _)
                hLower hDproj.le hControl
                (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) _) _)
                hqfac (Real.rpow_nonneg (div_nonneg hXpos.le hIpos.le) _)
                (Real.rpow_nonneg
                  (first_main_radius_pos reflected (Z^M) X Z ξ sigma reserve hZpos l).le _)
                (mul_nonneg (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _))
              convert hh using 1; dsimp only [Enamed,G,coef,Control,u]; ring
            have hrow : cost j≤((actualAllocations s.pools I).card:ℝ)^2*G/(rad*Dproj) := by
              calc
                _≤∑_B : actualAllocations s.pools I,((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
                  unfold cost geometryExceptionalMainRowMass
                  apply Finset.sum_le_sum
                  intro B _
                  split_ifs with hne
                  · exact hpoint B hne
                  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hG)
                      (mul_nonneg hrad.le hDproj.le)
                _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]; ring
            have hI0 : I≠0 := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs <;> exact (by first | exact src.hD.1 | exact src.hC.1)
            have hIcap : (I.absNorm:ℝ)≤ Z^(3:ℝ) := by
              dsimp only [I,geometryColumnIdeal]
              split_ifs
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
              · exact (actual_geometry_norm_caps s R seed (Z^M) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
            have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
              s.pools I hI0
            have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
            rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
              show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
            have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤ Da^2*Z^(3*εalloc) := by
              apply hcard2.trans
              rw [Real.rpow_mul (zero_lt_one.trans hZ).le]
              exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hIcap hea.le) (sq_nonneg _)
            apply hrow.trans
            have hrpow : Z^(geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)=rad :=
              Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hrad
            have hpow : Z^(3*εalloc)*Pz*Rpow=Z^exponent := by
              dsimp only [Pz,Rpow,exponent,X]
              rw [←Real.rpow_add (zero_lt_one.trans hZ),←Real.rpow_add (zero_lt_one.trans hZ)]
              congr 1
              ring
            calc
              _≤(Da^2*Z^(3*εalloc))*G/(rad*Dproj) := by gcongr
              _=factor*Z^exponent/(rad*Dproj) := by
                dsimp only [factor,G]
                rw [←hpow]
                ring
              _=factor*Z^(exponent-geometryExponents s R seed (Z^M) Z ξ j.val.1.val 2)/Dproj := by
                rw [Real.rpow_sub (zero_lt_one.trans hZ),hrpow]
                ring
          have hfull := hz.2.2 s R seed (Z^M) hK bin hs hs0 hz₁ hz₂ hsourcepos hsource hV
            (by simpa only [Real.rpow_zero] using
              (inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le hM))) rows
            (fun j _=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ hK bin)
              (fun _=>logAnnulus) j (by assumption))
            (fun j _=>actual_geometry_projector_cap s N R seed (Z^M) Z ξ 3 hK hcard hZ.le
              (by norm_num) hpool bin j)
            factor exponent cost hfactor hc hcost
          have hpost (P : Finset (Ideal O)) (β loss Ccap : ℝ)
              (hbβ : 3401/100000≤β ∧ β≤1/25) (hCcap : 0≤ Ccap)
              (hσ : sigma/3=Cycle61.Arithmetic.amp β)
              (hprime : Z^(Cycle61.Arithmetic.amp β-loss)≤(P.card:ℝ)) :
              (56/(P.card:ℝ))*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*
                (∑j : rows,cost j)≤
              16800*(Ccap+1)*(Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ))*Z^loss := by
            let E := Cd*factor*Z^(exponent+3*εcount-sigma/3)/(seed.absNorm:ℝ)
            have hE : 0≤ E := div_nonneg
              (mul_nonneg (mul_nonneg hCd.1.le hfactor) (Real.rpow_nonneg hZpos.le _))
              (Nat.cast_nonneg _)
            have hp : (0:ℝ)< P.card := (Real.rpow_pos_of_pos hZpos _).trans_le hprime
            have hamp : 0< Cycle61.Arithmetic.amp β := Cycle61.Arithmetic.amp_pos hbβ
            have hpref : 0≤(56/(P.card:ℝ))*
                ((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2)) :=
              mul_nonneg (div_nonneg (by norm_num) hp.le)
                (div_nonneg (add_nonneg hCcap (mul_nonneg (by norm_num) hamp.le))
                  (half_pos hamp).le)
            have hsplit : Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)=
                E*Z^(Cycle61.Arithmetic.amp β) := by
              have hpow : Z^(exponent+3*εcount)=
                  Z^(exponent+3*εcount-sigma/3)*Z^(Cycle61.Arithmetic.amp β) := by
                rw [←Real.rpow_add hZpos,←hσ]
                congr 1
                ring
              rw [hpow]
              dsimp only [E]
              ring
            calc
              _≤(56/(P.card:ℝ))*((Ccap+6*Cycle61.Arithmetic.amp β)/(Cycle61.Arithmetic.amp β/2))*
                  (Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)) :=
                mul_le_mul_of_nonneg_left hfull hpref
              _=_ := by rw [hsplit]
              _≤ _ := geometry_main_prime_payment P Z β loss Ccap E hZpos hbβ hCcap hE hprime
          exact And.intro hfull hpost))))))))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_exceptional_full

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_full_error_reference

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalFullPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalErrorFamily; sha256 bbb288b7ff6b10ad95d1fa68a5837b08633bd222326f6f7fea9172568d8359ad -/
section
                                                                  
                                                             

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondBlockAggregate CenteredMomentSecondBlockHarmonicMass
open CenteredMomentSecondLocalization
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicRowSupport

open CenteredMomentSecondExceptionalPhysicalSaving CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCommonSaving
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance exceptionalErrorFamilySumDecidable {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

open CenteredMomentSecondExceptionalFamily CenteredMomentSecondExceptionalSourceFamily
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceLowerSupport
open CenteredMomentFiniteProfileExceptionalPhysical

open CenteredMomentSecondExceptionalFixedQChosenBlock CenteredMomentSecondExceptionalAggregate
open CenteredMomentSecondBlockRadicalHarmonicMass CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondRetainedAggregate
open CenteredMomentActiveSource

/-- Positive exceptional physical-block mass, retaining every original
arithmetic label and dyadic block before any triangle inequality. -/
def exceptionalPhysicalNormSum (η : Character) (χ : RayCharacter) (Q : Ideal O)
    (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) : ℝ :=
  ∑p∈liveLabels η S β,∑U : Finset (CommonIndex p.val.1 p.val.2),
    ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows true η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖

private theorem exceptional_norm_sum_radical_bound(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(_hV:0< V)(hE:0≤ E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows true η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤ E*radicalWeight p.val.1 p.val.2):
    exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        radicalWeight q.1.1.val.1 q.1.1.val.2):=by
  unfold exceptionalPhysicalNormSum
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          radicalWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤ _:=mul_le_mul_of_nonneg_left (live_radical_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

private theorem source_exceptional_norm_sum_radical_bound (B L Cr ε:ℝ)(hB:0≤ B)(hL:0≤ L)
    (hCr:0< Cr)(hε:0<ε):
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→ seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤ Z^B) →
    ∀(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0< K → frequencyRadius Tsec Z ξ≤ Cr*Z^L → H≤ Z^B → 0< V → 0≤ E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows true η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤ E*radicalWeight p.val.1 p.val.2) →
    exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H/V≤ E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (exceptional_norm_sum_radical_bound η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)


theorem original_exceptional_physical_norm_sum (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ L)(hCr:0< Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤ Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0< Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0< R → R≤ Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤ Z^B →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      exceptionalPhysicalNormSum s.η χ₀ Q m s.t S β W Kphys Tsec Z ξ (sourceRadius s)/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ):=by
  obtain ⟨J,Sprofile,hSp,Ck,hCk,hblock⟩:=chosen_exceptional_block wlo whi hwlo hwhi lo hi W
    ε δ θ B B hε hδ hθ hB hB
  obtain ⟨Cm,hCm,hmass⟩:=source_exceptional_norm_sum_radical_bound B L Cr δ hB hL hCr hδ
  refine ⟨J,Sprofile,hSp,Ck*Cm,mul_nonneg hCk hCm.le,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hblock⟩:=hblock Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hblock,hmass] with Z hZ hmassZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap S β χ₀ m hm hml hm2
    Tsec ξ Kphys hKphys R hR hRcap hcond r hX1 hX2 hY1 hY2
  have hp0 (i:Fin 2):p.profile i 0=0:=by
    by_contra hh
    have hh':=(p.support i hh).1
    linarith
  have hz1:s.W₁ 0=0:=by rw [hW1];exact hp0 0
  have hz2:s.W₂ 0=0:=by rw [hW2];exact hp0 1
  let V:=volume s.toData
  let a:ℝ:=(∏i,s.lo i)*wlo*wlo
  let F:=Ck*profileFactor Sprofile s p J Q K*
    Z^(2*ε+δ+2*B*θ-2*max r 0/3)*V^(1/3:ℝ)*Kphys^(5/6:ℝ)*a^(-2/3:ℝ)
  have hF:0≤ F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have ha:0< a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
    have hzp:0< Z:=zero_lt_one.trans hZ.1
    dsimp only [F,V]
    positivity
  have hsum:=hmassZ seed hseed hseed0 S β
    (fun I _ hI=>original_column_mask s R0 seed I hI)
    (fun I _ hI=>(original_column_norm s R0 seed I hz1 hz2 hI).2.trans hcap)
    s.η χ₀ Q m s.t W Kphys Tsec ξ (sourceRadius s) V F
    hKphys hRcap hcap (volume_pos s.toData) hF
  have hlocal:∀q∈liveLabels s.η S β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀n:CenteredMomentSecondBlockAggregate.SourceBlocks q.val.1 q.val.2 U Kphys R (sourceRadius s),
      ‖physicalBlock s.η s.t (activeSource S β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource S β) _ _ q.property).1
        (commonLabels_supported (activeSource S β) _ _ q.property).2 U R
        (partRows true s.η χ₀ Q m q.val.1 q.val.2 U R) W Kphys (fun i=>(n i:ℤ))‖/V≤
          F*radicalWeight q.val.1 q.val.2:=by
    intro q hq U n
    have hg:=actual_common_gates s R0 seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource S β) _ _ q.property
    have hcnd:(expandedFactor s.η:ℝ)*R0.absNorm*q.val.1.absNorm*q.val.2.absNorm*(4*R)≤ Z^B:=by
      apply le_trans _ hcond
      have hH:0≤ sourceRadius s:=(Nat.cast_nonneg q.val.1.absNorm).trans hg.2.2.2.2.2.1
      calc
        _=(expandedFactor s.η:ℝ)*R0.absNorm*((q.val.1.absNorm:ℝ)*q.val.2.absNorm)*(4*R):=by ring
        _≤(expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s*sourceRadius s)*(4*R):=by
          gcongr
          · exact hg.2.2.2.2.2.1
          · exact hg.2.2.2.2.2.2
        _=_:=by ring
    have hh:=hZ.2 s p hlo hhi hP hW1 hW2 q.val.1 q.val.2 hs.1 hs.2 R0 seed hR0
      hg.2.2.2.1 hg.2.2.2.2.1 (hg.2.2.2.2.2.1.trans hcap) (hg.2.2.2.2.2.2.trans hcap)
      hg.2.2.1 U r hX1 hX2 hY1 hY2 χ₀ ((mem_liveLabels _ _ _ q).mp hq).1
      m hm hml hm2 hcap R Kphys hKphys hcnd (fun i=>(n i:ℤ))
    rw [←physicalBlock_active]
    exact hh.trans_eq (by dsimp only [F,V,a,radicalWeight];ring)
  have hh:=hsum hlocal
  apply hh.trans_eq
  have hp:Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ=
      Z^(2*ε+2*δ+2*B*θ-2*max r 0/3):=by
    rw [←Real.rpow_add (zero_lt_one.trans hZ.1)]
    congr 1
    ring
  dsimp only [F,V,a]
  calc
    _=(Ck*Cm)*profileFactor Sprofile s p J Q K*
      (Z^(2*ε+δ+2*B*θ-2*max r 0/3)*Z^δ)*
      (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ):=by ring
    _=_:=by rw [hp]


/-- Restrict the rows only after the original physical block is retained. -/
def exceptionalSecondDatum {α : Type*}[Fintype α][DecidableEq α]
    (d : SecondInputDatum α) (χ : RayCharacter) (Q : Ideal O) (m : O) :
    SecondInputDatum α :=
  {d with
    rows:=partRows true d.input.η χ Q m d.C d.D d.inactive d.radius
    rows_ne:=fun z hz=>sourceRows_nonzero d.C d.D d.inactive d.radius z
      (Finset.mem_filter.mp hz).1}

variable {α : Type*}[Fintype α][DecidableEq α]

/-- The selector tests the original full physical block, before the
exceptional row restriction and the norm. -/
def originalFilteredExceptionalNormSum (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) : ℝ :=
  let datum := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
  let blocks := Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
    (datum q).block.value W≠0)
  ∑q : blocks,‖(exceptionalSecondDatum (datum q.val) χ Q m).block.value W‖

/-- Literal original-input block norms are the unfiltered positive
exceptional mass. No triangle inequality is reversed. -/
theorem actual_original_exceptional_norm_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    (∑q : ActualSecondBlockIndex s R seed K Tsec Z ξ,
      ‖(exceptionalSecondDatum
        (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q)
        χ Q m).block.value W‖)=
    exceptionalPhysicalNormSum s.η χ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed) W K Tsec Z ξ (sourceRadius s) := by
  unfold exceptionalPhysicalNormSum
  rw [Fintype.sum_sigma]
  conv_rhs => rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [exceptionalSecondDatum,actualSecondBlockDatum,actualSecondInputDatum,
    SecondInputDatum.block,originalSecondBlock,SecondBlockSource.value]
  apply congrArg norm
  exact physicalBlock_active s.η s.t _ _ _ _ _ _ U _ _ W K _

/-- Original zero filtering is a nonnegative subfamily of the physical
exceptional norm sum, even when the two restricted pieces cancel. -/
theorem actual_filtered_exceptional_norm_sum_le (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :
    originalFilteredExceptionalNormSum slots s R seed hseed hz₁ hz₂ χ Q m W K Tsec Z ξ hK≤
      exceptionalPhysicalNormSum s.η χ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) W K Tsec Z ξ (sourceRadius s) := by
  apply le_trans _ (actual_original_exceptional_norm_assembly slots s R seed hseed
    hz₁ hz₂ χ Q m W K Tsec Z ξ hK).le
  unfold originalFilteredExceptionalNormSum
  dsimp only
  rw [Finset.sum_coe_sort
    (Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0))
    (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      ‖(exceptionalSecondDatum (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂
        K Tsec Z ξ hK q) χ Q m).block.value W‖)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _=>norm_nonneg _)

/-- The saved bound consumes the original full-block zero filter before
exceptional restriction. Its proof pays a positive norm sum directly. -/
theorem original_filtered_exceptional_norm_bound (slots : Finset α) (wlo whi:ℝ)(hwlo:0< wlo)(hwhi:0≤ whi)(lo hi:slots→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤ B)(hL:0≤ L)(hCr:0< Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤ Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀(s:Input slots)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤ s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      ∀(R0 seed:Ideal O),R0≠0 → ∀hseed : Squarefree seed,seed≠0 → sourceRadius s≤ Z^B →
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ)(hKphys : 0< Kphys),
      let R:=frequencyRadius Tsec Z ξ
      0< R → R≤ Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤ Z^B →
      ∀r:ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
      originalFilteredExceptionalNormSum slots s R0 seed hseed hz₁ hz₂ χ₀ Q m W Kphys Tsec Z ξ hKphys/volume s.toData≤
        Ck*profileFactor Sprofile s p J Q K*
          Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
          (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/
          (seed.absNorm:ℝ):=by
  obtain ⟨J,Sp,hSp,Ck,hCk,hbound⟩ := original_exceptional_physical_norm_sum
    wlo whi hwlo hwhi lo hi W ε δ θ B L Cr hε hδ hθ hB hL hCr
  refine ⟨J,Sp,hSp,Ck,hCk,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩ := hbound Q hQ hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s p hlo hhi hP hW1 hW2 hz₁ hz₂ R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys R hR hRcap hcond r hX1 hX2 hY1 hY2
  exact (div_le_div_of_nonneg_right
    (actual_filtered_exceptional_norm_sum_le slots s R0 seed hseed hz₁ hz₂ χ₀ Q m
      W Kphys Tsec Z ξ hKphys)
    (CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le).trans
    (hz.2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap χ₀ m hm hml hm2
      Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2)

/-- Saved positive physical-block mass, before original-zero filtering.
The filtered consumer is a literal nonnegative subfamily. -/
def geometryExceptionalNormSourceEstimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (wlo whi : ℝ) (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ) (J : ℕ) (Sp : Finset (ℕ×ℕ)) (Ck : ℝ)
    (Q : Ideal O) (K Z : ℝ) : Prop :=
  ∀(s : Input ι)(p : Profiles wlo whi),
    (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → (∀i,1≤ s.P i) →
    s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(R0 seed : Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤ Z^B →
    ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
    ∀(Tsec ξ Kphys : ℝ),0< Kphys →
    0< frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤ Cr*Z^L →
    (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*
      (4*frequencyRadius Tsec Z ξ)≤ Z^B →
    ∀r : ℝ,Z^r≤ s.X₁ → Z^r≤ s.X₂ → Z^r≤ s.Y₁ → Z^r≤ s.Y₂ →
    exceptionalPhysicalNormSum s.η χ₀ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R0 seed) W Kphys Tsec Z ξ (sourceRadius s)/volume s.toData≤
      Ck*profileFactor Sp s p J Q K*Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*
        ((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)

/-- All finite original-slot restrictions are selected before the source and
scale. The individual profile factors are retained; the maximum degree permits
one later height choice without a cardinality loss in the energy. -/
theorem actual_finite_slot_exceptional_norm_family {Label : Type*} [Fintype Label]
    [DecidableEq Label] (slot : Label→ Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0< wlo)(hwhi : 0≤ whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr) :
    ∃(J : Label→ℕ)(Sp : Label→ Finset (ℕ×ℕ))(Ck : Label→ℝ)(Jmax : ℕ),
      (∀a,(0,0)∈Sp a ∧ 0≤ Ck a ∧ J a≤ Jmax) ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K : Label→ℝ,(∀a,0< K a) ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1< Z ∧ geometryExceptionalNormSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr (J a) (Sp a) (Ck a) Q (K a) Z := by
  have hex (a : Label) := original_exceptional_physical_norm_sum wlo whi hwlo hwhi
    (lo a) (hi a) W ε δ θ B L Cr hε hδ hθ hB hL hCr
  choose J Sp hSp Ck hCk hb using hex
  refine ⟨J,Sp,Ck,Finset.univ.sup J,?_,?_⟩
  · intro a
    exact ⟨hSp a,hCk a,Finset.le_sup (f:=J) (Finset.mem_univ a)⟩
  · intro Q hQ hQt hQ72
    choose K hK hbound using (fun a=>hb a Q hQ hQt hQ72)
    refine ⟨K,hK,?_⟩
    filter_upwards [Filter.eventually_all.mpr hbound] with Z hz
    intro a
    exact ⟨(hz a).1,(hz a).2⟩

theorem actual_finite_slot_exceptional_norm_uniform {Label : Type*} [Fintype Label]
    [DecidableEq Label] (slot : Label→ Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0< wlo)(hwhi : 0≤ whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤ B)(hL : 0≤ L)(hCr : 0< Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤ Ck ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤ Ideal.span {(72:O)} →
      ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1< Z ∧ geometryExceptionalNormSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr J Sp Ck Q K Z := by
  obtain ⟨J,Sp,Ck,Jmax,hdata,hfamily⟩:=actual_finite_slot_exceptional_norm_family slot
    wlo whi hwlo hwhi lo hi W ε δ θ B L Cr hε hδ hθ hB hL hCr
  let Sp₀:=Finset.univ.biUnion Sp
  let C₀:=1+∑a,Ck a
  have hCsum : 0≤∑a,Ck a := Finset.sum_nonneg (fun a _=>(hdata a).2.1)
  have hC₀ : 0≤ C₀ := by dsimp [C₀]; linarith
  refine ⟨Jmax,Sp₀,C₀,hC₀,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hfamily Q hQ hQt hQ72
  let K₀:=1+∑a,K a
  have hKsum : 0≤∑a,K a := Finset.sum_nonneg (fun a _=>(hK a).le)
  have hK₀ : 0< K₀ := by dsimp [K₀]; linarith
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hbound] with Z hz
  intro a
  refine ⟨(hz a).1,?_⟩
  unfold geometryExceptionalNormSourceEstimate
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hh:=(hz a).2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hCa : Ck a≤ C₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hdata a).2.1) (Finset.mem_univ a)
    dsimp [C₀]; linarith
  have hKa : K a≤ K₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hK a).le) (Finset.mem_univ a)
    dsimp [K₀]; linarith
  have hfactor:=CenteredMomentSecondUniformSubsetSource.factor_mono
    (Finset.subset_biUnion_of_mem Sp (Finset.mem_univ a)) s p (hdata a).2.2 Q (hK a).le hKa
  apply hh.trans
  have hp:=profileFactor_nonneg (Sp a) s p (J a) Q (K a) (hK a).le
  have hzpos:=zero_lt_one.trans (hz a).1
  have hV:=(CenteredMomentExceptionalAmplitudePair.volume_pos s.toData).le
  gcongr
  exact Real.rpow_nonneg (mul_nonneg (mul_nonneg
    (Finset.prod_nonneg (fun i _=>(s.lo_pos i).le)) hwlo.le) hwlo.le) _


/-- Uniform strong norm-source receipts for every actual first and twice
restriction, saved before labels, allocations, heights or the scale. -/
theorem actual_geometry_saved_exceptional_norm_sources
    (wlo whi : ℝ) (hwlo : 0< wlo) (hwhi : 0≤ whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ Bcap L Cr : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ) (hB : 0≤ Bcap) (hL : 0≤ L) (hCr : 0< Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤ Ck ∧
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤ Ideal.span {(72:O)} →
      ∃Kfix : ℝ,0< Kfix ∧ ∀ᶠ Z : ℝ in atTop,1< Z ∧
        ∀s : Input ι,s.lo=lo → s.hi=hi →
        ∀(I R : Ideal O)(B : actualAllocations s.pools I)(τ : Character)(t : ℝ),
        geometryExceptionalNormSourceEstimate wlo whi (child s I R B τ t).lo
          (child s I R B τ t).hi W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z ∧
        ∀(Q : Ideal O)(k : ℕ)(Bp : actualAllocations (child s I R B τ t).pools (Q^k))
          (υ : Character)(v : ℝ),
        geometryExceptionalNormSourceEstimate wlo whi (twiceChild s I R B τ t Q k Bp υ v).lo
          (twiceChild s I R B τ t Q k Bp υ v).hi W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z := by
  obtain ⟨J,Sp,Ck,hCk,hfamily⟩ := actual_finite_slot_exceptional_norm_uniform
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
    change geometryExceptionalNormSourceEstimate wlo whi
      (fun i : liveIndices B.val=>lo i.val) (fun i : liveIndices B.val=>hi i.val)
      W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z at hh
    have hl : (child s I R B τ t).lo=(fun i=>lo i.val) := funext (fun i=>congrFun hlo i.val)
    have hu : (child s I R B τ t).hi=(fun i=>hi i.val) := funext (fun i=>congrFun hhi i.val)
    rw [hl,hu]
    exact hh
  · intro Q k Bp υ v
    have hh := (hz (.inr ⟨liveIndices B.val,liveIndices Bp.val⟩)).2
    change geometryExceptionalNormSourceEstimate wlo whi
      (fun i : liveIndices Bp.val=>lo i.val.val) (fun i : liveIndices Bp.val=>hi i.val.val)
      W ε δ θ Bcap L Cr J Sp Ck Qfix Kfix Z at hh
    have hl : (twiceChild s I R B τ t Q k Bp υ v).lo=(fun i=>lo i.val.val) :=
      funext (fun i=>congrFun hlo i.val.val)
    have hu : (twiceChild s I R B τ t Q k Bp υ v).hi=(fun i=>hi i.val.val) :=
      funext (fun i=>congrFun hhi i.val.val)
    rw [hl,hu]
    exact hh


/-- Literal original-full zero filter. It is fixed before restricted rows. -/
abbrev OriginalExceptionalBlocks (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K) :=
  Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
    (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0)

private theorem weighted_selected_norms_le {B R : Type*} [Fintype B] [Fintype R]
    (v : B→ R→ℂ) (χ : B→ R) (w : B→ℂ)
    (A : ℝ) (hA : 0≤ A) (hw : ∀b,‖w b‖≤ A) :
    (∑b,‖w b*v b (χ b)‖)≤ A*∑r,∑b,‖v b r‖ := by
  calc
    _≤∑b,A*(∑r,‖v b r‖) := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw b) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (fun r _=>norm_nonneg (v b r)) (Finset.mem_univ (χ b))) hA)
    _=A*∑r,∑b,‖v b r‖ := by
      rw [←Finset.mul_sum,Finset.sum_comm]

/-- A block-dependent fixed ray is paid by the finite ray sum; arbitrary
complex physical weights use their actual norm cap. The original full-zero
filter remains outside both restricted pieces. -/
theorem actual_filtered_exceptional_weighted_ray_sum_le
    (slots : Finset α) (s : Input slots) (R seed : Ideal O)
    (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0< K)
    (χ : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK→ RayCharacter)
    (w : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK→ℂ)
    (A : ℝ) (hA : 0≤ A) (hw : ∀q,‖w q‖≤ A) :
    (∑q : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK,
      ‖w q*(exceptionalSecondDatum
        (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q.val)
        (χ q) Q m).block.value W‖)≤
      A*∑ψ : RayCharacter,exceptionalPhysicalNormSum s.η ψ Q m s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)
        W K Tsec Z ξ (sourceRadius s) := by
  let datum := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
  let value := fun (q : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK)
    (ψ : RayCharacter)=>(exceptionalSecondDatum (datum q.val) ψ Q m).block.value W
  calc
    _≤ A*∑ψ : RayCharacter,∑q,‖value q ψ‖ :=
      weighted_selected_norms_le value χ w A hA hw
    _≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro ψ _
      exact actual_filtered_exceptional_norm_sum_le slots s R seed hseed hz₁ hz₂
        ψ Q m W K Tsec Z ξ hK

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.original_exceptional_physical_norm_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_original_exceptional_norm_assembly
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_filtered_exceptional_norm_sum_le

#print axioms OAI.SevenEighths.Cycle61InitialMass.original_filtered_exceptional_norm_bound

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finite_slot_exceptional_norm_uniform
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_saved_exceptional_norm_sources

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_filtered_exceptional_weighted_ray_sum_le

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryExceptionalErrorFamily -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainOrdinaryContraction; sha256 32b590b156a889b895b6cd1ca071cb0da63d675f7046ab3a107de706c81df9e0 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentOriginalCommonHarmonic CenteredMomentCommonProfile CenteredMomentLogDyadic
open CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance mainOrdinaryContractionSumDecidable {ι : Type*} :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fixed-inducing part changes only the original physical row set. -/
def mainExceptionalDatum (d : SecondInputDatum α) (χ : RayCharacter)
    (Q : Ideal O) (m : O) : SecondInputDatum α :=
  {d with rows:=partRows true d.input.η χ Q m d.C d.D d.inactive d.radius
          rows_ne:=fun z hz=>sourceRows_nonzero _ _ _ _ z (Finset.mem_filter.mp hz).1}

/-- Split a complete original source family before any ordinary-row contraction. -/
theorem main_original_exceptional_split {Label : Type*} [Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (χ : Label→ RayCharacter)
    (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hrows : ∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) :
    ‖∑l,w l*(d l).block.value W‖ ≤
      (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value W‖)+
      ‖∑l,w l*(ordinarySecondDatum (d l) (χ l) Q m).block.value W‖ := by
  have he (l : Label) : (d l).block.value W =
      (mainExceptionalDatum (d l) (χ l) Q m).block.value W +
      (ordinarySecondDatum (d l) (χ l) Q m).block.value W := by
    have hvalue := congrArg (fun rows=>physicalBlock (d l).block.character
      (d l).block.height (d l).block.pool (d l).block.beta (d l).C (d l).D
      (d l).hC (d l).hD (d l).inactive (d l).radius rows W (d l).K (d l).dyad) (hrows l)
    exact hvalue.trans (geometry_physical_block_split (d l).input.η (χ l) Q m (d l).input.t
      _ _ (d l).C (d l).D (d l).hC (d l).hD (d l).inactive (d l).radius W (d l).K (d l).dyad)

  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (le_refl _))

/-- Constants precede the entire moving family. The sole analytic input is
its literal ordinary normalized bound, on the original selected labels. -/
theorem main_original_from_normalized (W : 𝓢(ℝ,ℂ)) (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label]
    (d : Label→ SecondInputDatum α) (w : Label→ℂ) (χ : Label→ RayCharacter)
    (Q : Ideal O) (m : O) (E H : ℤ→ℝ),
    (∀l,(d l).rows=sourceRows (d l).C (d l).D (d l).inactive (d l).radius) →
    (∀r∈secondRatioBins (fun l=>(d l).block),0≤ E r) →
    (∀r∈secondRatioBins (fun l=>(d l).block),0< H r) →
    SecondNormalizedBound W degree windowDegree
      (fun l=>ordinarySecondDatum (d l) (χ l) Q m) w E H →
    ‖∑l,w l*(d l).block.value W‖ ≤
      (∑l,‖w l*(mainExceptionalDatum (d l) (χ l) Q m).block.value W‖)+
      C*∑r∈secondRatioBins (fun l=>(d l).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hbound⟩ := restricted_second_ratio_from_normalized (α:=α)
    W A degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro Label _ d w χ Q m E H hrows hE hH hnorm
  exact (main_original_exceptional_split d w χ Q m W hrows).trans
    (add_le_add_right (hbound (fun l=>ordinarySecondDatum (d l) (χ l) Q m)
      w E H hE hH hnorm) _)

attribute [local irreducible] geometryLowSecondDatum geometryMainSecondWeight

section Actual
variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
  (Z Mrow amp ξ reserve b t : ℝ) (hZ : 1< Z) (key : ℤ×(Fin 5→ℤ))
  (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "N" => Fintype.card α
local notation "firsts" => GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key
local notation "blocks" => geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂

/-- The literal joint main retained sum: first allocation weight, child seed,
original puncture and second Fourier scales are unchanged. -/
def geometryMainRetainedSum (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) : ℂ :=
  ∑q : firsts,
    (geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ)*
    secondRetainedEnergy
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).η
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).t
      (finiteColumns (Fintype.piFinset (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q).pools))
      (coefficient (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
        (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val) q.1.val.2.1.val)
      ballProfile
      (firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
      (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ

/-- Original full-block filtering precedes the inducing split. -/
theorem actual_main_retained_nonzero_sum (Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ) :
    geometryMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : blocks,
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.val.1 hz₁ hz₂ j.val.2).block.value ballProfile := by
  have hassembly := actual_joint_retained_assembly
    (fun q : firsts=>liveIndices q.2.val)
    (fun q=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key t q)
    (fun q=>R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)
    (fun q=>q.1.val.2.1.val)
    (fun q=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus) q.1.val q.1.property)
    (fun _=>hz₁) (fun _=>hz₂) ballProfile
    (fun q=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val))
    (fun q=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve b N
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)) Z ξ
    (fun q=>first_main_radius_pos reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve
      (zero_lt_one.trans hZ) _)
    (fun q=>(geometryLowFirstWeight reflected s R seed (Z^Mrow) Z ξ Mprice Aprice
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key weight b t q:ℂ))
  have heq : geometryMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key Mprice Aprice weight =
      ∑j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key,
        geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j*
        (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          j.1 hz₁ hz₂ j.2).block.value ballProfile := by
    simpa only [geometryMainRetainedSum,geometryMainSecondWeight,geometryLowSecondDatum] using hassembly
  rw [heq]
  let datum := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    (geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      j.1 hz₁ hz₂ j.2).block
  let coeff := geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight
  let live := fun j : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key=>
    frozenCoefficient j.1.2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key j.1.1.val) R s.ν s.W s.P≠0
  conv_rhs => rw [Finset.sum_coe_sort blocks (fun j=>coeff j*(datum j).value ballProfile)]
  conv_rhs => rw [geometryMainNonzeroBlocks,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · rfl
  · by_cases hlive : live j
    · have hz : (datum j).value ballProfile=0 := by
        by_contra hn
        exact h ⟨hlive,hn⟩
      rw [hz,mul_zero]
    · have hw : coeff j=0 := by
        simp only [coeff,geometryMainSecondWeight,geometryLowFirstWeight,geometryAllocationWeight,
          live] at hlive ⊢
        simp only [hlive,ite_false,zero_div,Complex.ofReal_zero,zero_mul]
      change coeff j*(datum j).value ballProfile=0
      rw [hw,zero_mul]

end Actual

/-- Complete actual main retained contraction. Original nonzero labels are
selected first; the ordinary joint norm is then contracted on exact ratio
fibers. Exceptional block norms remain an explicit, separate remainder.
The constant is chosen before the source, allocations, and live heights. -/
theorem actual_geometry_main_ordinary_contraction (A degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus) (hs : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(Mprice Aprice : ℝ)
    (weight : Cycle61JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ),
    let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t
      (Fintype.card α) hZ key j.val.1 hz₁ hz₂ j.val.2
    let coeff:=fun j : selected=>geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t
      (Fintype.card α) hZ key Mprice Aprice weight j.val
    ∀(χ : selected→ RayCharacter)(Q : Ideal O)(m : O)(E H : ℤ→ℝ),
    (∀r∈secondRatioBins (fun j=>(datum j).block),0≤ E r) →
    (∀r∈secondRatioBins (fun j=>(datum j).block),0< H r) →
    SecondNormalizedBound ballProfile degree windowDegree
      (fun j=>ordinarySecondDatum (datum j) (χ j) Q m) coeff E H →
    ‖geometryMainRetainedSum reflected s R seed Z Mrow amp ξ reserve b t hZ key
      Mprice Aprice weight‖ ≤
      (∑j,‖coeff j*(mainExceptionalDatum (datum j) (χ j) Q m).block.value ballProfile‖)+
      C*∑r∈secondRatioBins (fun j=>(datum j).block),E r/(1+dyadicScale r)^A := by
  obtain ⟨C,hC,hbound⟩ := main_original_from_normalized (α:=α) ballProfile
    A degree windowDegree hc hs
  refine ⟨C,hC,?_⟩
  intro reflected s R seed Z Mrow amp ξ reserve b t hZ key hz₁ hz₂ Mprice Aprice weight
    selected datum coeff χ Q m E H hE hH hnorm
  rw [actual_main_retained_nonzero_sum reflected s R seed Z Mrow amp ξ reserve b t hZ key
    hz₁ hz₂ Mprice Aprice weight]
  exact hbound datum coeff χ Q m E H (fun j=>by unfold datum geometryLowSecondDatum actualSecondBlockDatum actualSecondInputDatum; rfl) hE hH hnorm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_original_exceptional_split
#print axioms OAI.SevenEighths.Cycle61InitialMass.main_original_from_normalized
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_retained_nonzero_sum

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_ordinary_contraction

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainOrdinaryContraction -/
