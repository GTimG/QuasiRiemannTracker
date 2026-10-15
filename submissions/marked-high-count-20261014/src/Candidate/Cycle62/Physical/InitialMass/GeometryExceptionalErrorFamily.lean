import Candidate.Cycle62.Physical.InitialMass.GeometryExceptionalFullPayment
import Candidate.Cycle62.Physical.InitialMass.SecondRetainedContraction

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle62InitialMass
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
    (K Tsec Z ξ H V E:ℝ)(_hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows true η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2):
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
    _≤_:=mul_le_mul_of_nonneg_left (live_radical_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

private theorem source_exceptional_norm_sum_radical_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows true η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2) →
    exceptionalPhysicalNormSum η χ Q m t S β W K Tsec Z ξ H/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (exceptional_norm_sum_radical_bound η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)


theorem original_exceptional_physical_norm_sum (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(R0 seed:Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=coefficient s R0 seed
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ),0<Kphys →
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
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
  have hF:0≤F:=by
    have hp:=profileFactor_nonneg Sprofile s p J Q K hK.le
    have hv:=volume_pos s.toData
    have ha:0<a:=mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) hwlo) hwlo
    have hzp:0<Z:=zero_lt_one.trans hZ.1
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
    have hcnd:(expandedFactor s.η:ℝ)*R0.absNorm*q.val.1.absNorm*q.val.2.absNorm*(4*R)≤Z^B:=by
      apply le_trans _ hcond
      have hH:0≤sourceRadius s:=(Nat.cast_nonneg q.val.1.absNorm).trans hg.2.2.2.2.2.1
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
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) : ℝ :=
  let datum := actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK
  let blocks := Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
    (datum q).block.value W≠0)
  ∑q : blocks,‖(exceptionalSecondDatum (datum q.val) χ Q m).block.value W‖

/-- Literal original-input block norms are the unfiltered positive
exceptional mass. No triangle inequality is reversed. -/
theorem actual_original_exceptional_norm_assembly (slots : Finset α) (s : Input slots)
    (R seed : Ideal O) (hseed : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (χ : RayCharacter) (Q : Ideal O) (m : O)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
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
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
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
theorem original_filtered_exceptional_norm_bound (slots : Finset α) (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:slots→ℝ)(W:𝓢(ℝ,ℂ))
    (ε δ θ B L Cr:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤L)(hCr:0<Cr):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧
      ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input slots)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      ∀(R0 seed:Ideal O),R0≠0 → ∀hseed : Squarefree seed,seed≠0 → sourceRadius s≤Z^B →
      ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(Tsec ξ Kphys:ℝ)(hKphys : 0<Kphys),
      let R:=frequencyRadius Tsec Z ξ
      0<R → R≤Cr*Z^L →
      (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*(4*R)≤Z^B →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
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
    (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → (∀i,1≤s.P i) →
    s.W₁=p.profile 0 → s.W₂=p.profile 1 →
    ∀(R0 seed : Ideal O),R0≠0 → Squarefree seed → seed≠0 → sourceRadius s≤Z^B →
    ∀(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
    ∀(Tsec ξ Kphys : ℝ),0<Kphys →
    0<frequencyRadius Tsec Z ξ → frequencyRadius Tsec Z ξ≤Cr*Z^L →
    (expandedFactor s.η:ℝ)*R0.absNorm*(sourceRadius s)^2*
      (4*frequencyRadius Tsec Z ξ)≤Z^B →
    ∀r : ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
    exceptionalPhysicalNormSum s.η χ₀ Q m s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R0 seed) W Kphys Tsec Z ξ (sourceRadius s)/volume s.toData≤
      Ck*profileFactor Sp s p J Q K*Z^(2*ε+2*δ+2*B*θ-2*max r 0/3)*
        (volume s.toData)^(1/3:ℝ)*Kphys^(5/6:ℝ)*
        ((∏i,s.lo i)*wlo*wlo)^(-2/3:ℝ)/(seed.absNorm:ℝ)

/-- All finite original-slot restrictions are selected before the source and
scale. The individual profile factors are retained; the maximum degree permits
one later height choice without a cardinality loss in the energy. -/
theorem actual_finite_slot_exceptional_norm_family {Label : Type*} [Fintype Label]
    [DecidableEq Label] (slot : Label→Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0<wlo)(hwhi : 0≤whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr) :
    ∃(J : Label→ℕ)(Sp : Label→Finset (ℕ×ℕ))(Ck : Label→ℝ)(Jmax : ℕ),
      (∀a,(0,0)∈Sp a ∧ 0≤Ck a ∧ J a≤Jmax) ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K : Label→ℝ,(∀a,0<K a) ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1<Z ∧ geometryExceptionalNormSourceEstimate wlo whi (lo a) (hi a) W
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
    [DecidableEq Label] (slot : Label→Type*) [∀a,Fintype (slot a)]
    [∀a,DecidableEq (slot a)]
    (wlo whi : ℝ)(hwlo : 0<wlo)(hwhi : 0≤whi)
    (lo hi : ∀a,slot a→ℝ)(W : 𝓢(ℝ,ℂ))
    (ε δ θ B L Cr : ℝ)(hε : 0<ε)(hδ : 0<δ)(hθ : 0<θ)
    (hB : 0≤B)(hL : 0≤L)(hCr : 0<Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤Ck ∧
      ∀Q : Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
        ∀a,1<Z ∧ geometryExceptionalNormSourceEstimate wlo whi (lo a) (hi a) W
          ε δ θ B L Cr J Sp Ck Q K Z := by
  obtain ⟨J,Sp,Ck,Jmax,hdata,hfamily⟩:=actual_finite_slot_exceptional_norm_family slot
    wlo whi hwlo hwhi lo hi W ε δ θ B L Cr hε hδ hθ hB hL hCr
  let Sp₀:=Finset.univ.biUnion Sp
  let C₀:=1+∑a,Ck a
  have hCsum : 0≤∑a,Ck a := Finset.sum_nonneg (fun a _=>(hdata a).2.1)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; linarith
  refine ⟨Jmax,Sp₀,C₀,hC₀,?_⟩
  intro Q hQ hQt hQ72
  obtain ⟨K,hK,hbound⟩:=hfamily Q hQ hQt hQ72
  let K₀:=1+∑a,K a
  have hKsum : 0≤∑a,K a := Finset.sum_nonneg (fun a _=>(hK a).le)
  have hK₀ : 0<K₀ := by dsimp [K₀]; linarith
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hbound] with Z hz
  intro a
  refine ⟨(hz a).1,?_⟩
  unfold geometryExceptionalNormSourceEstimate
  intro s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hh:=(hz a).2 s p hlo hhi hP hW1 hW2 R0 seed hR0 hseed hseed0 hcap
    χ₀ m hm hml hm2 Tsec ξ Kphys hKphys hR hRcap hcond r hX1 hX2 hY1 hY2
  have hCa : Ck a≤C₀ := by
    have h:=Finset.single_le_sum (fun a _=>(hdata a).2.1) (Finset.mem_univ a)
    dsimp [C₀]; linarith
  have hKa : K a≤K₀ := by
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
    (wlo whi : ℝ) (hwlo : 0<wlo) (hwhi : 0≤whi)
    (lo hi : ι→ℝ) (W : 𝓢(ℝ,ℂ)) (ε δ θ Bcap L Cr : ℝ)
    (hε : 0<ε) (hδ : 0<δ) (hθ : 0<θ) (hB : 0≤Bcap) (hL : 0≤L) (hCr : 0<Cr) :
    ∃(J : ℕ)(Sp : Finset (ℕ×ℕ))(Ck : ℝ),0≤Ck ∧
      ∀Qfix : Ideal O,Qfix≠0 → Qfix≠⊤ → Qfix≤Ideal.span {(72:O)} →
      ∃Kfix : ℝ,0<Kfix ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
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
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :=
  Finset.univ.filter (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
    (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0)

private theorem weighted_selected_norms_le {B R : Type*} [Fintype B] [Fintype R]
    (v : B→R→ℂ) (χ : B→R) (w : B→ℂ)
    (A : ℝ) (hA : 0≤A) (hw : ∀b,‖w b‖≤A) :
    (∑b,‖w b*v b (χ b)‖)≤A*∑r,∑b,‖v b r‖ := by
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
    (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K)
    (χ : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK→RayCharacter)
    (w : OriginalExceptionalBlocks slots s R seed hseed hz₁ hz₂ W K Tsec Z ξ hK→ℂ)
    (A : ℝ) (hA : 0≤A) (hw : ∀q,‖w q‖≤A) :
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
    _≤A*∑ψ : RayCharacter,∑q,‖value q ψ‖ :=
      weighted_selected_norms_le value χ w A hA hw
    _≤_ := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro ψ _
      exact actual_filtered_exceptional_norm_sum_le slots s R seed hseed hz₁ hz₂
        ψ Q m W K Tsec Z ξ hK

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.original_exceptional_physical_norm_sum

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_original_exceptional_norm_assembly
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_filtered_exceptional_norm_sum_le

#print axioms OAI.SevenEighths.Cycle62InitialMass.original_filtered_exceptional_norm_bound

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_finite_slot_exceptional_norm_uniform
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_saved_exceptional_norm_sources

#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_filtered_exceptional_weighted_ray_sum_le
