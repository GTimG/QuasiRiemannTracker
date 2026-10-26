import Candidate.Target836.SourceProvider.ErrorMain
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Target836.Error836.GeometryErrorPhysicalTotal
import Candidate.Cycle63.Physical.InitialMass.SourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Candidate.Target836.Error836.GeometryAffinePrimeGates
import Candidate.Cycle63.Moment.CellGeometry

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Target836ErrorPayment
open OAI.SevenEighths.Cycle63InitialMass
open Target874836.SourceProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open Cycle63Moment CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentRankinRadical ActualEisensteinCubic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O
local instance affineErrorScalarSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _



open Cycle63InitialSource ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedRayDictionary

/-- Increasing a fixed payment constant preserves the actual physical
allocation contract; every remaining factor is nonnegative. -/
theorem error_physical_allocation_constant_mono {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K K' Z : ℝ)
    (hZ : 0 ≤ Z)(hlo : 0 < lo)(hap : 0 < ap)(hK : K ≤ K')
    (paid : ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z) :
    ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K' Z := by
  intro s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot
    C υ vheight A weight cost
  have h:=paid s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot υ vheight
  apply h.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num)
        (geometry_high_factor_pos reflected _ bin
          (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le))
      (Real.rpow_nonneg hZ _)) (Nat.cast_nonneg _)

/-- Finite ambient slot subsets share one constant and one threshold.
Each subset keeps its own literal source and original allocation types. -/
theorem uniform_error_physical_allocation_payment {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc : ℝ)
    (hCs : 1 ≤ Cs)(hlo : 0 < lo)(hap : 0 < ap)(hev : 0 < εv)(hB : 0 ≤ B)(he : 0 < ε)
    (hb : 1 ≤ b)(hbs : 1 ≤ bs)(hMmin : 0 < Mmin)(hU : 0 ≤ U)(heshell : 0 < εshell)
    (hξ : 0 ≤ ξ)(healloc : 0 < εalloc) :
    ∃K : ℝ,0 < K ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧ ∀T : Finset α,
      ErrorPhysicalAllocationBound (ι:=T) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z := by
  have data (T : Finset α):=eventual_actual_error_physical_allocation_payment (ι:=T)
    N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    hCs hlo hap hev hB he hb hbs hMmin hU heshell hξ healloc
  choose C hC hbound using data
  let K:=1+∑T : Finset α,C T
  have hn : ∀T : Finset α,0 ≤ C T:=fun T=>(hC T).le
  have hK : 0 < K:=by
    have hsum:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hn T)
    dsimp only [K];linarith
  have hCK (T : Finset α) : C T ≤ K:=by
    have hh:=Finset.single_le_sum (fun T _=>hn T) (Finset.mem_univ T)
    dsimp only [K];linarith
  refine ⟨K,hK,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound,eventually_ge_atTop (2:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T
  exact error_physical_allocation_constant_mono N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    (C T) K Z (by linarith) hlo hap (hCK T) (hz T).2

/-- Source facts supplied by the literal affine construction, rather than
premises about the extracted energies or desired numerator. -/
structure AffineErrorSourceGates {ι : Type}[Fintype ι]
    (s : Input ι)(N : ℕ)(Cs Z : ℝ)(P : Finset (Ideal O)) : Prop where
  card : Fintype.card ι ≤ N
  mass : ∀i,s.M i ≤ Cs
  lower : (1:ℝ) ≤ s.lower
  endpoints : Endpoints (9/4) (9/4) (9/4) s
  volume : CenteredMomentAmplificationChildInput.volume s ≤ Z^(3:ℝ)
  pool : ∀j I,I∈s.pools j→(I.absNorm:ℝ) ≤ Z^(2:ℝ)
  plainZero₁ : s.W₁ 0=0
  plainZero₂ : s.W₂ 0=0
  radius_pos : 0 < sourceRadius s
  radius : sourceRadius s ≤ Z^(3:ℝ)
  plainLower₁ : ∀x,s.W₁ x≠0→(1/4:ℝ) ≤ x
  plainLower₂ : ∀x,s.W₂ x≠0→(1/4:ℝ) ≤ x
  primes_nonempty : P.Nonempty
  primes : ∀Q∈P,Prime Q
  primes_good : ∀Q∈P,Q∉fixedBadPrimes
  coprime : ∀q : elementPool P,∀j I,I∈s.slots j→IsCoprime (Ideal.span {q.val}) I

variable {α : Type}[Fintype α][DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorScalarFiniteQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)

include hH in
/-- Genuine prime pools are nonempty simultaneously for every physical
width cell. The deleted fixed primes remain in the pool definition. -/
theorem eventual_affine_error_pools_nonempty (Sbad : Finset (Ideal O)) :
    ∀ᶠZ : ℝ in atTop,1 < Z ∧ ∀j : ↥(Finset.Icc 1 600),
      (CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1
        (Z^(Named.amp (Cycle63.Arithmetic.cellUpper j.val)))).Nonempty := by
  have hcell (j : ↥(Finset.Icc 1 600)) :=
    Cycle63.Arithmetic.cellUpper_bounds (Finset.mem_Icc.mp j.property).1 (Finset.mem_Icc.mp j.property).2
  have hp (j : ↥(Finset.Icc 1 600)):=
    CenteredMomentFirstAmplificationChoice.eventually_actual_pool_card rayM H hH Sbad
      (Named.amp (Cycle63.Arithmetic.cellUpper j.val)) 1
      (Named.amp_pos (hcell j)) (by norm_num)
  filter_upwards [Filter.eventually_all.mpr hp,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro j
  apply Finset.card_pos.mp
  exact_mod_cast (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).trans_le (hz j)

set_option maxHeartbeats 1200000 in
/-- All scalar source and prime gates hold uniformly before the live subset,
characters, profiles, lengths and heights are chosen. -/
theorem eventual_actual_affine_error_source_gates
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (mesh : ℝ)(hmesh : mesh < (902420521/120632400000:ℝ)/2) :
    ∃Cs : ℝ,1 ≤ Cs ∧ ∀ᶠZ : ℝ in atTop,1 < Z ∧
      ∀(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
        (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
        (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
        (t X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂),
      (∀i,0 ≤ w i) → (∀i,w i ≤ mesh) →
      (41/100:ℝ) ≤ length Z X₁ → (41/100:ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (44/100:ℝ) → length Z X₂ ≤ (44/100:ℝ) →
      (17/500:ℝ) ≤ ∑i,w i → (∑i,w i) ≤ (1/25:ℝ) →
      let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let beta:=Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(Named.amp beta))
      AffineErrorSourceGates inp (Fintype.card α) Cs Z P := by
  obtain ⟨Cs,bs,bp,hCs,hbs,hbp,hfixed⟩:=fixed_affine_source_caps (α:=α) rayM H hH W hW
    1 2 (33/50) (33/50) (1/4) (9/4) (by norm_num) hWs (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [eventual_affine_polynomial_caps (α:=α) rayM H hH W hW 1 2
      (33/50) (33/50) (1/4) (9/4) 1 (by norm_num) hWs
      (by norm_num) (by norm_num) (by norm_num),
    eventual_geometry_affine_prime_coprime rayM H hH Sbad hbad 2 mesh hmesh,
    eventual_affine_error_pools_nonempty rayM H hH Sbad,
    eventually_ge_atTop (9/4:ℝ)] with Z hc hcop hp hlarge
  refine ⟨hc.1,?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi inp beta P
  have hcaps:=hc.2 T η₀ θ w σ freq hσ bΦ state p 1 t X₁ X₂ hX₁ hX₂
    (by norm_num) le_rfl hw (by simpa only [mul_one] using hlo₁)
    (by simpa only [mul_one] using hlo₂) (by simpa only [mul_one] using hhi₁)
    (by simpa only [mul_one] using hhi₂) (by simpa only [one_div] using hwhi)
  rcases hcaps with ⟨hVge,hVlog,hV,hsource,hcolumns⟩
  rcases hfixed T η₀ θ w σ freq hσ state p 1 t X₁ X₂ hX₁ hX₂ with
    ⟨hcard,hmass,hupper,hend,hb₁,hb₂,hW₁,hW₂,hη,hmatch⟩
  have hplain (j : Fin 2)(x : ℝ)(hne : p.profile j x≠0) : (1/4:ℝ) ≤ x:=
    (p.support j hne).1
  have hzero (j : Fin 2) : p.profile j 0=0:=by
    by_contra hne
    have h:=hplain j 0 hne
    norm_num at h
  have he:=affine_endpoints rayM H hH η₀ θ W hW 1 2 (33/50) (33/50) (by norm_num) hWs
    w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂ (by norm_num) (by norm_num)
  have he' : Endpoints (9/4) (9/4) (9/4) inp:=by
    refine ⟨he.1.trans ?_,he.2⟩
    norm_num
  have hpool:=affine_individual_pool_cap rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
    1 hc.1 (by norm_num) le_rfl (by norm_num) (by simpa using (show (2:ℝ) ≤ Z by linarith))
    hlarge hw (by simpa using hwhi) (by simpa using hhi₁) (by simpa using hhi₂)
  have hpool' : ∀j I,I∈inp.pools j→(I.absNorm:ℝ) ≤ Z^(2:ℝ):=by
    simpa only [show (1:ℝ)+1=2 by norm_num] using hpool
  have hsource' : sourceRadius inp ≤ Z^(3:ℝ):=by
    simpa only [show (1:ℝ)+2=3 by norm_num] using hsource
  have hradpos : 0 < sourceRadius inp:=by
    change 0 < (∏i : T,(2:ℝ))*(9/4)*(9/4)*(X₁*X₂)*(∏i : T,Z^(w i))
    exact mul_pos (mul_pos (mul_pos (mul_pos (Finset.prod_pos (fun _ _=>by norm_num))
      (by norm_num)) (by norm_num)) (mul_pos hX₁ hX₂))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos (zero_lt_one.trans hc.1) _))
  have hcell:=Cycle63.Moment.originalCell_mem ⟨hwlo,hwhi⟩
  let j : ↥(Finset.Icc 1 600):=⟨Cycle63.Moment.originalCell (∑i,w i),Finset.mem_Icc.mpr ⟨hcell.1,hcell.2.1⟩⟩
  have hbeta:=Cycle63.Arithmetic.cellUpper_bounds hcell.1 hcell.2.1
  refine ⟨hcard,hmass,le_rfl,he',?_,hpool',hzero 0,hzero 1,hradpos,hsource',hplain 0,hplain 1,
    hp.2 j,?_,?_,?_⟩
  · exact hV.trans (Real.rpow_le_rpow_of_exponent_le hc.1.le (by norm_num))
  · intro Q hQ
    exact (primePool_data rayM H Sbad hbad _ _ _ Q hQ).1
  · intro Q hQ
    exact (primePool_data rayM H Sbad hbad _ _ _ Q hQ).2
  · exact hcop.2 beta hbeta.1 hbeta.2 inp η₀ θ w σ freq W hmatch hwm

private def affine_error_allocation_frame {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(s : Input ι)(Z ξ εalloc εshell K amp reserve error εcommon : ℝ)
    (reflected second : Bool)(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ))
    (radius : ℝ)(hk : 0 < radius) : Prop :=
  ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s 1 1 radius Z ξ hk bin))),
    rows⊆firstLiveColumns (geometryFirstSource s 1 1 radius Z ξ hk bin) (fun _=>logAnnulus) →
  ∀(height : ℝ)(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) →
    (∀Q∈P,Q∉fixedBadPrimes) →
    (∀q : elementPool P,∀j I,I∈s.slots j→IsCoprime (Ideal.span {q.val}) I) →
  let C:=fun j : rows=>geometryColumnIdeal reflected s 1 1 radius Z ξ hk bin j.val
  ∀(υ : (j : rows)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→Character)
    (vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume s)
  let weight:=fun q=>normPhase (coordinateBlock s 1 1 Φ radius Z ξ q)
  (∑j : rows,∑alloc : actualAllocations s.pools (C j),
    geometryAllocationWeight reflected s 1 1 radius Z ξ 1 A hk bin weight N (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s 1 1 radius Z ξ hk bin j.val) j.val.2.1.val 1 alloc
        (geometryColumnCharacter reflected s 1 1 radius Z ξ hk bin j.val) height P (υ j alloc)
        vheight Z 1 amp (3*amp) reserve error εcommon) ≤ 
    16*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*K*
      Z^(((3:ℝ)+1)*εalloc+εshell-1*(7/60000000))/( (1:Ideal O).absNorm:ℝ)

/-- Literal affine specialization of the complete physical scalar payment.
The actual prime pool, characters and undivided allocation weights are kept. -/
def AffineErrorScalarBound (Sbad : Finset (Ideal O))
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh K Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters rayM H)
    (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(p : Profiles (1/4) (9/4))
    (t X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂),
  (∀i,0 ≤ w i) → (∀i,w i ≤ mesh) →
  (41/100:ℝ) ≤ length Z X₁ → (41/100:ℝ) ≤ length Z X₂ →
  length Z X₁ ≤ (44/100:ℝ) → length Z X₂ ≤ (44/100:ℝ) →
  (17/500:ℝ) ≤ ∑i,w i → (∑i,w i) ≤ (1/25:ℝ) →
  let inp:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
    (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
  let beta:=Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell (∑i,w i))
  let amp:=Named.amp beta
  let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
  ∀(reflected second : Bool)(error εcommon reserve : ℝ),
  0 ≤ εcommon → error+εv+4*εcommon+ε ≤ 64*geometryLossUnit 1 εaffine →
  ∀(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ)),
  let hK:=zero_lt_one.trans hZ
  let rows:=firstLiveColumns (geometryFirstSource inp 1 1 Z Z ξ hK bin) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected inp 1 1 Z Z ξ hK bin j.val
  ∀(height : ℝ)(υ : (j : rows)→actualAllocations inp.pools (C j)→
    elementPool P→Fin 3→RayCharacter→Character)(vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume inp)
  let weight:=fun q=>normPhase (coordinateBlock inp 1 1 Φ Z Z ξ q)
  (∑j : rows,∑alloc : actualAllocations inp.pools (C j),
    geometryAllocationWeight reflected inp 1 1 Z Z ξ 1 A hK bin weight (Fintype.card α) (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost inp reflected second
        (geometryFirstLabel inp 1 1 Z Z ξ hK bin j.val) j.val.2.1.val 1 alloc
        (geometryColumnCharacter reflected inp 1 1 Z Z ξ hK bin j.val) height P (υ j alloc)
        vheight Z 1 amp (3*amp) reserve error εcommon) ≤ 
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-(7/60000000:ℝ))

set_option maxHeartbeats 1600000 in
/-- Actual affine source facts discharge every source and prime gate of the
saved physical payment. A single constant precedes all live slot subsets. -/
theorem eventual_actual_affine_error_scalar_payment
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (εv ε εaffine εshell ξ εalloc mesh : ℝ)
    (hev : 0 < εv)(he : 0 < ε)(heshell : 0 < εshell)(hξ : 0 ≤ ξ)(healloc : 0 < εalloc)
    (hmesh : mesh < (902420521/120632400000:ℝ)/2) :
    ∃K : ℝ,0 < K ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
      AffineErrorScalarBound (α:=α) rayM H hH Sbad W hW hWs εv ε εaffine εshell ξ εalloc mesh K Z := by
  obtain ⟨Cs,hCs,hgates⟩:=eventual_actual_affine_error_source_gates (α:=α) rayM H hH
    Sbad hbad W hW hWs mesh hmesh
  obtain ⟨K,hK,hpaid⟩:=uniform_error_physical_allocation_payment (α:=α)
    (Fintype.card α) Cs 1 (1/4) εv 3 ε (9/4) (9/4) 1 εaffine 2 εshell ξ εalloc
    hCs (by norm_num) (by norm_num) hev (by norm_num) he (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heshell hξ healloc
  refine ⟨K,hK,?_⟩
  filter_upwards [hgates,hpaid] with Z hg hp
  refine ⟨hp.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
    inp beta amp P reflected second error εcommon reserve hecommon hloss Φ bin hpow rows C height υ vheight A weight
  have g:=hg.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwm hlo₁ hlo₂ hhi₁ hhi₂ hwlo hwhi
  have hk : 0 < Z^(1:ℝ):=by simpa only [Real.rpow_one] using hpow
  have hh:=(hp.2 T) inp g.card g.mass g.lower g.endpoints g.volume g.pool
    reflected second 1 error εcommon amp (3*amp) reserve le_rfl hecommon
    (by simpa only [show (3:ℝ)+1=4 by norm_num] using hloss)
    1 1 squarefree_one one_ne_zero g.plainZero₁ g.plainZero₂ g.radius_pos g.radius
    g.plainLower₁ g.plainLower₂ Φ hk bin
  have hframe : affine_error_allocation_frame (Fintype.card α) inp Z ξ εalloc εshell K amp reserve
      error εcommon reflected second Φ bin (Z^(1:ℝ)) hk:=hh
  have heq : (⟨Z^(1:ℝ),hk⟩ : {r : ℝ // 0 < r})=⟨Z,hpow⟩:=Subtype.ext (Real.rpow_one Z)
  have htype:=congrArg (fun r : {r : ℝ // 0 < r}=>
    affine_error_allocation_frame (Fintype.card α) inp Z ξ εalloc εshell K amp reserve
      error εcommon reflected second Φ bin r.val r.property) heq
  have hframeZ:=Eq.mp htype hframe
  have hfinal:=hframeZ rows (Finset.Subset.refl _) height P g.primes_nonempty g.primes g.primes_good g.coprime υ vheight
  simpa only [mul_one,one_mul,map_one,Nat.cast_one,div_one,
    show (3:ℝ)+1=4 by norm_num] using hfinal

end
end OAI.SevenEighths.Target836ErrorPayment
#print axioms OAI.SevenEighths.Target836ErrorPayment.error_physical_allocation_constant_mono
#print axioms OAI.SevenEighths.Target836ErrorPayment.uniform_error_physical_allocation_payment
#print axioms OAI.SevenEighths.Target836ErrorPayment.eventual_affine_error_pools_nonempty
#print axioms OAI.SevenEighths.Target836ErrorPayment.eventual_actual_affine_error_source_gates
#print axioms OAI.SevenEighths.Target836ErrorPayment.eventual_actual_affine_error_scalar_payment
