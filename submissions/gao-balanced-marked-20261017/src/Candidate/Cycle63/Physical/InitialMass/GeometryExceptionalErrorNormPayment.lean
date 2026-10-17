import Candidate.Cycle63.Physical.InitialMass.GeometryExceptionalNormPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorNormalized

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Cycle63Moment HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentSecondEnergySplit RayFourExpansion
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentFirstChildLower CenteredMomentFirstExceptionalChildPaid
open CenteredMomentFirstScale CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentSecondExceptionalFamily
open CenteredMomentCommonProfile ConcretePrimeRowBridge CenteredMomentActive
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstMixedRightTransport
open CenteredMomentFirstMixedRoot CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildSourceCaps
open Filter CenteredMomentLogDyadic CenteredMomentFirstAnnularInput CenteredMomentAmplificationRadicalFamily
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentAllocationCost
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance exceptionalErrorNormPaymentSumDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _


open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentFirstPhysicalSource

section Selected
variable (reflected : Bool) (s : Input ι) (R seed : Ideal O) (Ψ : 𝓢(ℝ,ℂ))
    (Z M amp ξ reserve b t : ℝ) (hZ : 1<Z) (key : ℤ×(Fin 5→ℤ))
variable (q : GeometryLowFirstIndex reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key)
    (P : Finset (Ideal O)) (p : O) (i : Fin 3)
    (Bp : actualAllocations (activeInput
      (geometryLowFirstChild reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q)).pools
        ((Ideal.span {p})^(errorIndex i+1)))
    (υ : Character) (v : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
local notation "selected" => geometryErrorNonzeroBlocks reflected s R seed Z M amp ξ reserve b t
    (Fintype.card ι) hZ key q p i Bp υ v hz₁ hz₂

set_option linter.defProp false in
/-- The literal extracted coefficient pays the original-full-zero-filtered
exceptional block norm sum. The factor 56/P is included once; inducing rays
may vary by block, and the actual second height coefficient costs at most one. -/
def actual_geometry_error_exceptional_selected_norm_le
    (χ : selected→RayCharacter) (Q : Ideal O) (m : O) :=
  let src := geometryErrorChild reflected s R seed Z M ξ t hZ key q p i Bp υ v
  let slots := liveIndices (errorActiveAllocation
    (geometryLowFirstChild reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q) _ Bp).val
  let R₂ := (R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key q.1.val)*
    (Ideal.span {p})^(errorIndex i+1)
  let K₂ := geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key q p i
  let T₂ := geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b
    (Fintype.card ι) hZ key q p i
  let weight := geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key
    (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ c))
    (Fintype.card ι) b q.1.val q.2
  let c := errorNormalizedCoefficient P weight (volume src) p i
  have hc : 0≤c := error_normalized_coefficient_nonneg P weight (volume src)
    (geometryAllocationWeight_nonneg ..)
    (CenteredMomentAmplificationChildInput.volume_pos src) p i
  actual_filtered_exceptional_weighted_ray_sum_le slots src R₂ q.1.val.2.1.val
    (actual_first_live_squarefree (geometryFirstSource s R seed (Z^M) Z ξ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key)
      (fun _=>logAnnulus) q.1.val q.1.property) hz₁ hz₂ Q m ballProfile K₂ T₂ Z ξ
    (actual_geometry_error_source_radius_pos reflected s R seed Z M amp ξ reserve hZ key q p i)
    χ (fun n=>(c:ℂ)*actualSecondBlockWeight src R₂ q.1.val.2.1.val K₂ T₂ Z ξ n.val)
    c hc (fun n=>actual_error_block_weight_norm src R₂ q.1.val.2.1.val K₂ T₂ Z ξ n.val c hc)


/-- Genuine normalized exceptional source mass for one fixed extracted
allocation. Both physical menus are fixed before any second row is summed. -/
def geometryExceptionalErrorNormSourceMass (Q : Ideal O) (m : O)
    (χ₀ : RayCharacter) : ℝ :=
  let src := geometryErrorChild reflected s R seed Z M ξ t hZ key q p i Bp υ v
  errorNormalizedCoefficient P
    (geometryAllocationWeight reflected s R seed (Z^M) Z ξ M
      (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key
      (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^M) Z ξ c))
      (Fintype.card ι) b q.1.val q.2) (volume src) p i*
    exceptionalPhysicalNormSum src.η χ₀ Q m src.t
      (finiteColumns (Fintype.piFinset src.pools))
      (coefficient src ((R*geometryColumnIdeal reflected s R seed (Z^M) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key q.1.val)*
        (Ideal.span {p})^(errorIndex i+1)) q.1.val.2.1.val) ballProfile
      (geometryErrorSourceRadius reflected s R seed Z M amp ξ reserve hZ key q p i)
      (geometryErrorFourierScale reflected s R seed Z M amp ξ reserve b (Fintype.card ι)
        hZ key q p i) Z ξ (sourceRadius src)

omit [DecidableEq ι] in
private theorem active_error_allocation_card (hp : Prime (Ideal.span {p}))
    (hslot : ∀j I,I∈(geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q).slots j→
        IsCoprime (Ideal.span {p}) I) :
    (actualAllocations (activeInput (geometryLowFirstChild reflected s R seed (Z^M) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) M) key t q)).pools
        ((Ideal.span {p})^(errorIndex i+1))).card≤8 := by
  apply CenteredMomentAmplificationAllocationCost.actual_error_allocations_card _ _ hp _
  · fin_cases i <;> norm_num [errorIndex]
  · intro j I hI
    exact ⟨((activeInput _).prime j I hI).ne_zero,
      hslot j I (Finset.mem_filter.mp hI).1⟩

private theorem error_index_price_cap : (16*(errorIndex i+2:ℝ))≤128 := by
  fin_cases i <;> norm_num [errorIndex]

end Selected


open CenteredMomentPrimeElements CenteredMomentAmplificationAllocationCost

private theorem error_menu_count_le {α : Type*} [Fintype α]
    (u : Input α) (P : Finset (Ideal O))
    (hprime : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀p∈elementPool P,∀j I,I∈u.slots j→IsCoprime (Ideal.span {p}) I)
    (f : (p : elementPool P)→(i : Fin 3)→RayCharacter→
      actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))→
      RayCharacter→ℝ) (U : ℝ) (hU : 0≤U)
    (hf : ∀p i ψ Bp χ,f p i ψ Bp χ≤U) :
    (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ : RayCharacter,f p i ψ Bp χ)≤
      (P.card:ℝ)*3*(Fintype.card RayCharacter:ℝ)*8*(Fintype.card RayCharacter:ℝ)*U := by
  have hcard (p : elementPool P) (i : Fin 3) :
      (actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))).card≤8 := by
    have hp : Prime (Ideal.span {p.val}) := hprime _ (elementPool_data P hprime hbad p.val p.property).2.1
    apply actual_error_allocations_card _ _ hp _
    · fin_cases i <;> norm_num [errorIndex]
    · intro j I hI
      exact ⟨((activeInput u).prime j I hI).ne_zero,
        hslot p.val p.property j I (Finset.mem_filter.mp hI).1⟩
  calc
    _≤∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
        ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
          ∑χ : RayCharacter,U := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro ψ _
      apply Finset.sum_le_sum; intro Bp _
      apply Finset.sum_le_sum; intro χ _
      exact hf p i ψ Bp χ
    _≤∑_p : elementPool P,∑_i : Fin 3,∑_ψ : RayCharacter,
        8*((Fintype.card RayCharacter:ℝ)*U) := by
      apply Finset.sum_le_sum; intro p _
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro ψ _
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard p i))
        (mul_nonneg (Nat.cast_nonneg _) hU)
    _=_ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,
        Fintype.card_fin,nsmul_eq_mul,elementPool_card P hprime hbad]
      ring

private theorem prime_average_count_le (P : Finset (Ideal O)) :
    (P.card:ℝ)*(56/(P.card:ℝ))≤56 := by
  by_cases h : P.card=0
  · simp only [h,Nat.cast_zero,div_zero,mul_zero]; norm_num
  · have hp : (P.card:ℝ)≠0 := Nat.cast_ne_zero.mpr h
    exact le_of_eq (by field_simp)

private theorem error_menu_average_le {α : Type*} [Fintype α]
    (u : Input α) (P : Finset (Ideal O))
    (hprime : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀p∈elementPool P,∀j I,I∈u.slots j→IsCoprime (Ideal.span {p}) I)
    (f : (p : elementPool P)→(i : Fin 3)→RayCharacter→
      actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1))→
      RayCharacter→ℝ) (E : ℝ) (hE : 0≤E)
    (hf : ∀p i ψ Bp χ,f p i ψ Bp χ≤(56/(P.card:ℝ))*128*E) :
    (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput u).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ : RayCharacter,f p i ψ Bp χ)≤
      56*128*3*8*(Fintype.card RayCharacter:ℝ)^2*E := by
  have hU : 0≤(56/(P.card:ℝ))*128*E := by positivity
  have hh := error_menu_count_le u P hprime hbad hslot f _ hU hf
  calc
    _≤_ := hh
    _=(P.card:ℝ)*(56/(P.card:ℝ))*(128*3*8*(Fintype.card RayCharacter:ℝ)^2*E) := by ring
    _≤56*(128*3*8*(Fintype.card RayCharacter:ℝ)^2*E) :=
      mul_le_mul_of_nonneg_right (prime_average_count_le P) (by positivity)
    _=_ := by ring

private theorem error_norm_fold_algebra
    (E S Shell F A Ck Cprof Pz lower L D Control bro q volumeRoot kr mr Rpow : ℝ)
    (hpaid : E≤S*F*q*A*(Ck*Pz*mr*kr*lower/D)*(Cprof*Control*bro*volumeRoot))
    (hside : S≤Shell) (hlower : lower≤L) (href : q*volumeRoot*kr*mr≤Rpow)
    (hS : 0≤S) (hShell : 0≤Shell) (hF : 0≤F) (hA : 0≤A)
    (hP : 0≤Pz) (hl : 0≤lower) (hL : 0≤L) (hD : 0≤D)
    (hc : 0≤Control) (hb : 0≤bro) (hq : 0≤q) (hi : 0≤volumeRoot)
    (hk : 0≤kr) (hm : 0≤mr) :
    E≤Shell*F*A*max 1 (Ck*Cprof)*Pz*L/D*Control*bro*Rpow := by
  let rest := S*F*A*Pz*(lower/D)*Control*bro*(q*volumeRoot*kr*mr)
  have hrest : 0≤rest := by dsimp only [rest]; positivity
  calc
    E≤(Ck*Cprof)*rest := by convert hpaid using 1; dsimp only [rest]; ring
    _≤max 1 (Ck*Cprof)*rest := mul_le_mul_of_nonneg_right (le_max_right _ _) hrest
    _≤max 1 (Ck*Cprof)*(Shell*F*A*Pz*(L/D)*Control*bro*Rpow) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (le_max_left _ _))
      dsimp only [rest]
      gcongr
    _=_ := by ring


private theorem error_norm_reference_orientation (reflected : Bool)
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



private theorem exceptional_error_mass_nonneg (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (m : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    0≤exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H := by
  unfold exceptionalPhysicalNormSum
  apply Finset.sum_nonneg; intro p _
  apply Finset.sum_nonneg; intro U _
  apply Finset.sum_nonneg; intro n _
  exact norm_nonneg _

attribute [local irreducible] exceptionalPhysicalNormSum

private theorem error_source_price_identity (P : Finset (Ideal O)) (w V A : ℝ)
    (p : O) (i : Fin 3) :
    errorNormalizedCoefficient P w V p i*A=
      (56/(P.card:ℝ))*(16*(errorIndex i+2:ℝ))*(w*localErrorCost p (errorIndex i)*(A/V)) := by
  unfold errorNormalizedCoefficient
  ring

private theorem error_norm_paid_replace
    (E side F qpre qfac A Ck Power Pz cap cost kr lower D Cprof pc hc mc bro root : ℝ)
    (hq : qpre=qfac) (hpower : Power=Pz*cap)
    (hpaid : E≤(side*F*qpre*A*(Ck*Power*kr*lower/D)*cost)*
      ((Cprof*pc*hc*mc)*(bro*root))) :
    E≤side*F*qfac*A*(Ck*Pz*(cost*cap)*kr*lower/D)*
      (Cprof*(pc*hc*mc)*bro*root) := by
  rw [hq,hpower] at hpaid
  convert hpaid using 1
  ring

private theorem error_norm_zero_price_le (P : Finset (Ideal O))
    (w V A target : ℝ) (p : O) (i : Fin 3) (hw : w=0) (ht : 0≤target) :
    errorNormalizedCoefficient P w V p i*A≤target := by
  rw [hw]
  simpa only [errorNormalizedCoefficient,mul_zero,zero_mul,zero_div] using ht

private theorem error_norm_split_power (z a c : ℝ) (hz : 0<z) :
    z^(a-2*c/3)=z^a*z^(-2*c/3) := by
  calc
    _=z^(a+(-2*c/3)) := congrArg (fun e : ℝ=>z^e) (by ring)
    _=_ := Real.rpow_add hz a (-2*c/3)

private theorem error_lower_base_nonneg {α : Type*} [Fintype α]
    (u : Input α) (w : ℝ) : 0≤((∏a,u.lo a)*w*w) := by
  have hp : 0≤∏a,u.lo a := Finset.prod_nonneg (fun a _=>(u.lo_pos a).le)
  calc
    _=(∏a,u.lo a)*w^2 := by ring
    _≥0 := mul_nonneg hp (sq_nonneg w)

private theorem error_norm_allocation_sum {α : Type*} (A : Finset α)
    (fee G rad D : ℝ) :
    (∑_B : A,fee*(A.card:ℝ)*G/(rad*D))=fee*(A.card:ℝ)^2*G/(rad*D) := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  ring

set_option linter.unusedVariables false in
/-- Pure-data full extracted exceptional payment; its source gates are
arithmetic and profile receipts, and contain no exceptional energy premise. -/
def GeometryExceptionalErrorNormFullSpec
    (wlo whi : ℝ) (lo hi : ι→ℝ) (ε δ θ : ℝ) (η : Character)
    (b bs slotlo εalloc εcount ξ : ℝ) (J : ℕ) (Sp : Finset (ℕ×ℕ))
    (Ck : ℝ) (Qfix : Ideal O) (Kfix Cd Da Z : ℝ) : Prop :=
    ∀(hZ : 1<Z) (s : Input ι) (hlo : s.lo=lo) (hhi : s.hi=hi) (hη : s.η=η)
            (hend : Endpoints b bs bs s) (hlower : slotlo≤s.lower) (hsP : ∀i,1≤s.P i)
            (p0 : Profiles wlo whi) (hW₁ : s.W₁=p0.profile 0) (hW₂ : s.W₂=p0.profile 1)
            (R seed : Ideal O) (hR : R≠0) (hs : Squarefree seed) (hs0 : seed≠0)
            (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
            (hV : volume s≤Z^(2:ℝ)) (hsourcepos : 0<sourceRadius s)
            (hsource : sourceRadius s≤Z^(3:ℝ)) (hlogV : |Real.logb Z (volume s)|≤3)
            (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ))
            (hRN : (R.absNorm:ℝ)≤Z) (amp reserve t v plainLoss : ℝ)
            (hamp : 0≤amp) (hamp₁ : amp≤1) (hreserve : 0≤reserve)
            (hω : frequencyLoss Z 32 ξ+reserve≤3)
            (hX₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₁)
            (hX₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.X₂)
            (hY₁ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₁)
            (hY₂ : Z^((1+Real.logb Z (s.η.modulus.absNorm:ℝ))/4-plainLoss)≤s.Y₂)
            (a₁ a₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
            (hs₁ : ∀x,s.W₁ x≠0→a₁≤x) (hs₂ : ∀x,s.W₂ x≠0→a₂≤x)
            (reflected : Bool) (Ψ : 𝓢(ℝ,ℂ)) (key : ℤ×(Fin 5→ℤ))
            (Mprime : Ideal O) (hMprime : NeZero Mprime),
            letI : NeZero Mprime := hMprime
            ∀(Hprime : Subgroup (O⧸Mprime)ˣ) (Sbad : Finset (Ideal O))
              (hbad : fixedBadPrimes⊆Sbad),
            let P := CenteredMomentPrimePool.primePool Mprime Hprime Sbad (1/2) 1 (Z^amp)
            let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
            let rows := firstLiveColumns (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
              (fun _=>logAnnulus)
            let firsts := GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z ξ hK key
            ∀(υ : firsts→elementPool P→Fin 3→RayCharacter→Character)
              (hcop : ∀q : firsts,∀p∈elementPool P,∀j I,
                I∈(geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ hK key t q).slots j→
                  IsCoprime (Ideal.span {p}) I)
              (hυ : ∀q : firsts,∀p : elementPool P,∀i : Fin 3,∀ψ : RayCharacter,
                (υ q p i ψ).modulus.absNorm≤radicalBound (childCharacter
                  (geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK key q.1.val) ψ)
                    fixedBadMask p.val (errorMovingExponent (errorIndex i)))
              (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m),
            let cost := fun j : rows=>∑B : actualAllocations s.pools
                (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val),
              ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
                ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
                  (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
                  ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
                    Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀

            let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
            let Shell := if reflected then 1/Hshell
              else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
            let Control := p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
            let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant
              (Fintype.card ι) b J Qfix Kfix)
            let factor := (56*128*3*8*(Fintype.card RayCharacter:ℝ)^2)*Shell*
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^(Fintype.card ι)*
              coef*geometryExceptionalLowerConstant (Fintype.card ι) slotlo wlo*Control*
              (b^(Fintype.card ι))^(1/3:ℝ)*Da^2
            let exponent := 2*ε+2*δ+2*126*θ+Real.logb Z (geometryExceptionalVolume s)-
              (1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
              3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
            (∑j : rows,cost j)≤Cd*factor*Z^(exponent+3*εcount)/(seed.absNorm:ℝ)

set_option maxHeartbeats 500000 in
set_option linter.defProp false in
/-- Saved actual exceptional kernels, reference contraction and the complete
extracted allocation/ray/prime menus. The original radical and projector are
summed jointly; the prime factor 56/P is paid once. -/
theorem actual_geometry_error_exceptional_norm_full
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (ε δ θ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ)
    (η : Character) (b bs : ℝ) (hb : 1≤b) (hbs : 1≤bs)
    (slotlo εalloc εcount ξ : ℝ) (hslot : 0<slotlo)
    (hea : 0<εalloc) (hec : 0<εcount) (hξ : 0≤ξ) (hξ₁ : ξ≤1)  :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤Ideal.span {(72:O)} →
      ∃Kfix Cd Da : ℝ,0<Kfix ∧ 0<Cd ∧ 0<Da ∧
        ∀ᶠZ : ℝ in atTop,1<Z ∧ GeometryExceptionalErrorNormFullSpec wlo whi lo hi ε δ θ η
          b bs slotlo εalloc εcount ξ J Sp Ck Qfix Kfix Cd Da Z := by
  let N := Fintype.card ι
  let closed := actual_geometry_error_exceptional_norm_closed wlo whi hwlo hwhi lo hi ballProfile
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
  refine ⟨J,Sp,Ck,?_⟩
  intro Qfix hQ hQt hQ72
  let saved := closed.2.2.2 Qfix hQ hQt hQ72
  let Kfix := saved.1
  let hevent := saved.2.1.down.2.and hCd.2
  refine ⟨Kfix,Cd,Da,saved.2.1.down.1,hCd.1,hDa.1,?_⟩
  filter_upwards [hevent] with Z hz
  let kernel := saved.2.2.down Z hz.1
  refine ⟨kernel.1,?_⟩
  unfold GeometryExceptionalErrorNormFullSpec
  intro hZ s hlo hhi hη hend hlower hsP p0 hW₁ hW₂ R seed hR hs hs0 hz₁ hz₂
    hV hsourcepos hsource hlogV hpool hRN amp reserve t v plainLoss hamp hamp₁ hreserve hω
    hX₁ hX₂ hY₁ hY₂ a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ key Mprime hMprime
  let : NeZero Mprime := hMprime
  intro Hprime Sbad hbad P hK rows firsts υ hcop hυ m hm hml hm2
  let cost := fun j : rows=>∑B : actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val),
    ∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
      ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
        (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
        ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
          Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀
  have hZpos : 0<Z := zero_lt_one.trans hZ
  let Hshell := Z^((key.2 1:ℝ)*Real.logb Z 2)
  have hH : 0<Hshell := Real.rpow_pos_of_pos hZpos _
  have hphysical (j : rows) : Hshell≤
      ((geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1).D.absNorm:ℝ) ∧
      ((geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1).D.absNorm:ℝ)≤2*Hshell := by
    have hr := actual_geometry_fiber_range s R seed (Z^(1:ℝ)) Z ξ 3 hZ hs hz₁ hz₂
      hsource key j.val.1 1
    have hn := actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂
      hsource j.val.1.val 1
    have hl := Real.rpow_le_rpow_of_exponent_le hZ.le hr.1
    have hu := Real.rpow_le_rpow_of_exponent_le hZ.le hr.2.le
    rw [geometryExponents,Real.rpow_logb hZpos hZ.ne' (zero_lt_one.trans_le hn.1)] at hl hu
    have he : Z^(((key.2 1:ℝ)+1)*Real.logb Z 2)=2*Hshell := by
      rw [add_mul,one_mul,Real.rpow_add hZpos,
        Real.rpow_logb hZpos hZ.ne' (by norm_num : (0:ℝ)<2)]
      exact mul_comm _ _
    exact ⟨hl,hu.trans_eq he⟩
  let Shell := if reflected then 1/Hshell
    else (4/((∏i,s.lo i)*a₁*a₂))^2*(2*Hshell)
  let Control := p0.control Sp^2*(1+‖v‖)^(2*J)*(∏i,s.M i)^6
  let coef := max 1 (Ck*CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
  let fee := 56*128*3*8*(Fintype.card RayCharacter:ℝ)^2
  let factor := fee*Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
    coef*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Da^2
  let exponent := 2*ε+2*δ+2*126*θ+Real.logb Z (geometryExceptionalVolume s)-
    (1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
    3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3+3*εalloc
  have hShell : 0≤Shell := by dsimp only [Shell]; split_ifs <;> positivity
  have hControl : 0≤Control := by dsimp only [Control]; positivity
  have hfee : 0≤fee := by dsimp only [fee]; positivity
  have hfixed : 0<fixedPresentationCost := fixedPresentationCost_pos
  have hLower : 0≤geometryExceptionalLowerConstant N slotlo wlo :=
    Real.rpow_nonneg (by positivity) _
  have hfactor : 0≤factor := by dsimp only [factor,coef]; positivity
  have hprimeP : ∀Q∈P,Prime Q := fun Q hQ=>
    (primePool_data Mprime Hprime Sbad hbad (1/2) 1 (Z^amp) Q hQ).1
  have hbadP : ∀Q∈P,Q∉fixedBadPrimes := fun Q hQ=>
    (primePool_data Mprime Hprime Sbad hbad (1/2) 1 (Z^amp) Q hQ).2
  have hc : ∀j : rows,0≤cost j := by
    intro j
    apply Finset.sum_nonneg; intro B _
    apply Finset.sum_nonneg; intro p _
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro ψ _
    apply Finset.sum_nonneg; intro Bp _
    apply Finset.sum_nonneg; intro χ₀ _
    unfold geometryExceptionalErrorNormSourceMass
    exact mul_nonneg (error_normalized_coefficient_nonneg _ _ _
      (geometryAllocationWeight_nonneg ..) (CenteredMomentAmplificationChildInput.volume_pos _) _ _)
      (exceptional_error_mass_nonneg ..)
  have hcost : ∀j : rows,cost j≤factor*
      Z^(exponent-geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)/
        (j.val.2.1.val.absNorm:ℝ) := by
    intro j
    let I := geometryColumnIdeal reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let τ := geometryColumnCharacter reflected s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let src := geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key j.val.1
    let l := geometryFirstLabel s R seed (Z^(1:ℝ)) Z ξ hK key j.val
    let rad := ((commonRadical src.C src.D).absNorm:ℝ)
    let Dproj := (j.val.2.1.val.absNorm:ℝ)
    let X := geometryExceptionalVolume s
    let Pz := Z^(2*ε+2*δ+2*126*θ)
    let Rpow := Z^(Real.logb Z X-(1+Real.logb Z (s.η.modulus.absNorm:ℝ))+
      3*(3*amp)/2+5*(frequencyLoss Z 32 ξ+reserve)/6+2*plainLoss/3)
    let G := Shell*(fixedPresentationCost*(s.η.modulus.absNorm:ℝ))*(max 1 b)^N*
      coef*Pz*geometryExceptionalLowerConstant N slotlo wlo*Control*(b^N)^(1/3:ℝ)*Rpow
    have hG : 0≤G := by dsimp only [G,coef,Pz,Rpow]; positivity
    have hrad : 0<rad := norm_pos _ (commonRadical_ne_zero _ _)
    have hDproj : 0<Dproj := norm_pos _
      (actual_first_live_squarefree (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
        (fun _=>logAnnulus) j.val j.property).ne_zero
    have hrow : cost j≤fee*((actualAllocations s.pools I).card:ℝ)^2*G/(rad*Dproj) := by
      have hmenu (B : actualAllocations s.pools I) :
          (∑p : elementPool P,∑i : Fin 3,∑ψ : RayCharacter,
            ∑Bp : actualAllocations (activeInput (geometryLowFirstChild reflected s R seed
              (Z^(1:ℝ)) Z ξ hK key t ⟨j,B⟩)).pools ((Ideal.span {p.val})^(errorIndex i+1)),
              ∑χ₀ : RayCharacter,geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
                Z 1 amp ξ reserve b t hZ key ⟨j,B⟩ P p.val i Bp (υ ⟨j,B⟩ p i ψ) v Qfix m χ₀)≤
          fee*((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
        let q : firsts := ⟨j,B⟩
        let u1 := geometryLowFirstChild reflected s R seed (Z^(1:ℝ)) Z ξ hK key t q
        let f := fun (p : elementPool P) (i : Fin 3) (ψ : RayCharacter)
          (Bp : actualAllocations (activeInput u1).pools ((Ideal.span {p.val})^(errorIndex i+1)))
          (χ₀ : RayCharacter)=>geometryExceptionalErrorNormSourceMass reflected s R seed Ψ
            Z 1 amp ξ reserve b t hZ key q P p.val i Bp (υ q p i ψ) v Qfix m χ₀
        have hE : 0≤((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) :=
          div_nonneg (mul_nonneg (Nat.cast_nonneg _) hG) (mul_pos hrad hDproj).le
        have hpoint : ∀p i ψ Bp χ₀,f p i ψ Bp χ₀≤
            (56/(P.card:ℝ))*128*(((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) := by
          intro p i ψ Bp χ₀
          dsimp only [f]
          by_cases hne : frozenCoefficient B.val I R s.ν s.W s.P≠0
          · let Bplift : actualAllocations (child s I R B τ t).pools
                ((Ideal.span {p.val})^(errorIndex i+1)) :=
              geometryExceptionalActiveLift reflected s R seed Z ξ t hZ key q p.val i Bp
            let u := geometryErrorChild reflected s R seed Z 1 ξ t hZ key q p.val i Bp (υ q p i ψ) v
            have hpdata := elementPool_data P hprimeP hbadP p.val p.property
            have hp : p.val≠0 := hpdata.1.ne_zero
            have hpN := (actual_geometry_exceptional_prime_cap Mprime Hprime Sbad hbad Z amp hZ
              (hamp₁.trans (by norm_num)) p.val p.property).2
            have hpayed := kernel.2 hZ s hlo hhi hη le_rfl hend hsP p0 hW₁ hW₂ R seed hR hs
              hz₁ hz₂ hV hsource hlogV hRN amp ξ reserve t hamp hamp₁ hξ hξ₁ hreserve hω
              a₁ a₂ ha₁ ha₂ hs₁ hs₂ reflected Ψ key q hne p.val hp hpN (hcop q p.val p.property)
              i Bp (υ q p i ψ) ψ v (hυ q p i ψ) χ₀ m hm hml hm2
            have href := actual_geometry_full_error_reference reflected s R seed 1 Z ξ amp reserve t
              hZ key j.val B Mprime Hprime Sbad hbad p.val p.property i Bplift (υ q p i ψ) v plainLoss
              hX₁ hX₂ hY₁ hY₂
            change geometryExceptionalErrorReference τ
              (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
              (Ideal.span {primeSubsetGenerator (fun q : CommonIndex l.1.1 l.1.2=>q.val) l.2.val})
              (Z^(1:ℝ)) X Z (3*amp) (frequencyLoss Z 32 ξ) reserve
              (inputCap Z (twiceChild s I R B τ t (Ideal.span {p.val})
                (errorIndex i+1) Bplift (υ q p i ψ) v)) p.val (errorIndex i+1)≤Rpow at href
            rw [error_norm_reference_orientation reflected τ l (Z^(1:ℝ)) X Z ξ
              (3*amp) reserve _ p.val (errorIndex i+1)] at href
            let side := if reflected then 1/(src.D.absNorm:ℝ)
              else (4/((∏i,s.lo i)*a₁*a₂))^2*(src.D.absNorm:ℝ)
            let den := (τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
              Z^(max (3*Real.logb Z (I.absNorm:ℝ)-
                5*Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)-
                Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)) 0/6)
            let qfac := (X/(I.absNorm:ℝ))/den
            let root := (X/(I.absNorm:ℝ)/(normValue p.val)^(errorIndex i+1))^(1/3:ℝ)
            let kr := (geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ key q p.val i)^(5/6:ℝ)
            let cap := Z^(-2*max (inputCap Z u) 0/3)
            let lower := ((∏a,u.lo a)*wlo*wlo)^(-2/3:ℝ)
            let Epaid := geometryAllocationWeight reflected s R seed (Z^(1:ℝ)) Z ξ 1
              (Real.logb Z X) hK key (fun c=>normPhase (coordinateBlock s R seed Ψ
                (Z^(1:ℝ)) Z ξ c)) N b j.val B*localErrorCost p.val (errorIndex i)*
                (exceptionalPhysicalNormSum u.η χ₀ Qfix m u.t
                  (finiteColumns (Fintype.piFinset u.pools))
                  (coefficient u ((R*I)*(Ideal.span {p.val})^(errorIndex i+1)) j.val.2.1.val)
                  ballProfile (geometryErrorSourceRadius reflected s R seed Z 1 amp ξ reserve hZ key q p.val i)
                  (geometryErrorFourierScale reflected s R seed Z 1 amp ξ reserve b N hZ key q p.val i)
                  Z ξ (sourceRadius u)/geometryExceptionalVolume u)
            have hulower : u.lower=s.lower := by rfl
            have hlow := actual_geometry_exceptional_lower_factor u N slotlo wlo
              ((live_card_le Bplift.val).trans ((live_card_le B.val).trans le_rfl)) hslot
              (by rw [hulower]; exact hlower) hwlo
            have hside : side≤Shell := by
              dsimp only [side,Shell]
              split_ifs
              · exact div_le_div_of_nonneg_left zero_le_one hH (hphysical j).1
              · exact mul_le_mul_of_nonneg_left (hphysical j).2 (sq_nonneg _)
            have hside0 : 0≤side := by dsimp only [side]; split_ifs <;> positivity
            have hXpos : 0<X := CenteredMomentExceptionalAmplitudePair.volume_pos s.toData
            have hIpos : 0<(I.absNorm:ℝ) := norm_pos I (allocation_ne s I B)
            have hτpos : 0<(τ.modulus.absNorm:ℝ) := norm_pos τ.modulus τ.modulus_ne_bot
            have hq : 0≤qfac := div_nonneg (div_nonneg hXpos.le hIpos.le)
              (mul_nonneg (mul_nonneg hτpos.le (sq_nonneg _)) (Real.rpow_nonneg hZpos.le _))
            have hbase := error_lower_base_nonneg u wlo
            have hlogs :
                (if reflected then max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                  5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                  geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6 else
                  max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                    5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                    geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6)=
                max (3*Real.logb Z (I.absNorm:ℝ)-
                  5*Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)-
                  Real.logb Z ((Ideal.span {activeConductor src.C src.D}).absNorm:ℝ)) 0/6 := by
              cases reflected <;> rfl
            let qpre := (X/(I.absNorm:ℝ))/((τ.modulus.absNorm:ℝ)*(X/(I.absNorm:ℝ))^2*
              Z^(if reflected then max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6 else
                max (3*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 0-
                  5*geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 1-
                  geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 3) 0/6))
            have hqpre : qpre=qfac := by dsimp only [qpre,qfac,den]; rw [hlogs]
            have hsplit : Z^(2*ε+2*δ+2*126*θ-2*max (inputCap Z u) 0/3)=Pz*cap := by
              exact error_norm_split_power Z (2*ε+2*δ+2*126*θ)
                (max (inputCap Z u) 0) hZpos
            have hpaidRewrite := error_norm_paid_replace Epaid side
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad) qpre qfac
              ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
              (Z^(2*ε+2*δ+2*126*θ-2*max (inputCap Z u) 0/3)) Pz cap
              (localErrorCost p.val (errorIndex i)) kr lower Dproj
              (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
              (p0.control Sp^2) ((1+‖v‖)^(2*J)) ((∏a,s.M a)^6)
              ((b^N)^(1/3:ℝ)) root hqpre hsplit hpayed
            change qfac*localErrorCost p.val (errorIndex i)*root*kr*cap≤Rpow at href
            have hfold := error_norm_fold_algebra Epaid side Shell
              (fixedPresentationCost*(s.η.modulus.absNorm:ℝ)/rad)
              ((max 1 b)^N*((actualAllocations s.pools I).card:ℝ)) Ck
              (CenteredMomentFirstChildProfileControl.exceptionalConstant N b J Qfix Kfix)
              Pz lower (geometryExceptionalLowerConstant N slotlo wlo) Dproj Control
              ((b^N)^(1/3:ℝ)) qfac root kr (localErrorCost p.val (errorIndex i)*cap) Rpow
              (by simpa only [Control] using hpaidRewrite)
              hside hlow
              (by convert href using 1; ring)
              hside0 hShell
              (div_nonneg (mul_nonneg hfixed.le (Nat.cast_nonneg _)) hrad.le)
              (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left 1 b)) _) (Nat.cast_nonneg _))
              (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hbase _) hLower hDproj.le hControl
              (Real.rpow_nonneg (pow_nonneg (zero_le_one.trans hb) _) _) hq
              (Real.rpow_nonneg (div_nonneg (div_nonneg hXpos.le hIpos.le)
                (pow_nonneg (by unfold normValue; exact Nat.cast_nonneg _) _)) _)
              (Real.rpow_nonneg (actual_geometry_error_source_radius_pos reflected s R seed Z 1
                amp ξ reserve hZ key q p.val i).le _)
              (mul_nonneg (localErrorCost_nonneg _ _) (Real.rpow_nonneg hZpos.le _))
            have hpoint : Epaid≤((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) := by
              convert hfold using 1; dsimp only [G,coef]; ring
            have hprice : geometryExceptionalErrorNormSourceMass reflected s R seed Ψ Z 1 amp ξ reserve b t
                hZ key q P p.val i Bp (υ q p i ψ) v Qfix m χ₀=
                (56/(P.card:ℝ))*(16*(errorIndex i+2:ℝ))*Epaid := by
              unfold geometryExceptionalErrorNormSourceMass
              rw [error_source_price_identity]
              rfl
            rw [hprice]
            have hprimecoef : 0≤56/(P.card:ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg _)
            have hpricecoef : 0≤16*(errorIndex i+2:ℝ) :=
              mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le (errorIndex i+2)))
            exact (mul_le_mul_of_nonneg_left hpoint (mul_nonneg hprimecoef hpricecoef)).trans
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (error_index_price_cap i) hprimecoef) hE)
          · have hzweight : geometryAllocationWeight reflected s R seed (Z^(1:ℝ)) Z ξ 1
                (Real.logb Z (volume s)) hK key
                (fun c=>normPhase (coordinateBlock s R seed Ψ (Z^(1:ℝ)) Z ξ c)) N b j.val B=0 := by
              simp only [geometryAllocationWeight,I] at hne ⊢
              exact ite_eq_right hne
            exact error_norm_zero_price_le P _ _ _ _ p.val i hzweight
              (mul_nonneg (mul_nonneg
                (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)) hE)
        have hh := error_menu_average_le u1 P hprimeP hbadP (hcop q)
          f (((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) hE hpoint
        calc
          _≤56*128*3*8*(Fintype.card RayCharacter:ℝ)^2*
              (((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj)) := hh
          _=_ := by dsimp only [fee]; ring
      calc
        _≤∑_B : actualAllocations s.pools I,fee*((actualAllocations s.pools I).card:ℝ)*G/(rad*Dproj) :=
          Finset.sum_le_sum (fun B _=>hmenu B)
        _=_ := error_norm_allocation_sum (actualAllocations s.pools I) fee G rad Dproj
    have hI0 : I≠0 := by
      dsimp only [I,geometryColumnIdeal]
      split_ifs
      · exact src.hD.1
      · exact src.hC.1
    have hIcap : (I.absNorm:ℝ)≤Z^(3:ℝ) := by
      dsimp only [I,geometryColumnIdeal]
      split_ifs
      · exact (actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 1).2
      · exact (actual_geometry_norm_caps s R seed (Z^(1:ℝ)) Z ξ 3 hs hz₁ hz₂ hsource j.val.1.val 0).2
    have hcardalloc := hDa.2 (ι:=ι⊕Fin 2) (by simp only [N,Fintype.card_sum,Fintype.card_fin]; omega)
      s.pools I hI0
    have hcard2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardalloc 2
    rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),
      show εalloc/2*(2:ℕ)=εalloc by norm_num] at hcard2
    have hcardZ : ((actualAllocations s.pools I).card:ℝ)^2≤Da^2*Z^(3*εalloc) := by
      apply hcard2.trans
      rw [Real.rpow_mul hZpos.le]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hIcap hea.le) (sq_nonneg _)
    apply hrow.trans
    have hrpow : Z^(geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)=rad :=
      Real.rpow_logb hZpos hZ.ne' hrad
    have hpow : Z^(3*εalloc)*Pz*Rpow=Z^exponent := by
      dsimp only [Pz,Rpow,exponent,X]
      rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos]
      congr 1; ring
    calc
      _≤fee*(Da^2*Z^(3*εalloc))*G/(rad*Dproj) := by gcongr
      _=factor*Z^exponent/(rad*Dproj) := by
        dsimp only [factor,G]
        rw [←hpow]
        ring
      _=factor*Z^(exponent-geometryExponents s R seed (Z^(1:ℝ)) Z ξ j.val.1.val 2)/Dproj := by
        rw [Real.rpow_sub hZpos,hrpow]; ring
  exact hz.2.2 s R seed (Z^(1:ℝ)) hK key hs hs0 hz₁ hz₂ hsourcepos hsource hV
    (by simpa only [Real.rpow_zero,Real.rpow_one] using (inv_le_one_of_one_le₀ hZ.le)) rows
    (fun j _=>actual_first_live_squarefree (geometryFirstSource s R seed (Z^(1:ℝ)) Z ξ hK key)
      (fun _=>logAnnulus) j (by assumption))
    (fun j _=>actual_geometry_projector_cap s N R seed (Z^(1:ℝ)) Z ξ 3 hK le_rfl hZ.le
      (by norm_num) hpool key j)
    factor exponent cost hfactor hc hcost

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_exceptional_selected_norm_le

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_error_exceptional_norm_full
