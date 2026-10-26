/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorSelectedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainFirstProjectorShell
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorCoprime
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
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
local notation "O" => HeckeFamily.O
local instance errorPhysicalPaymentSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The extracted scalar is positive before any ordinary-row restriction. -/
theorem extracted_error_label_scalar_nonneg (reflected second : Bool)(l v : FirstSourceLabel)
    (Z M a δ reserve error εcommon V Vextract : ℝ)(p : O)(k : ℕ)
    (hZ : 0≤Z)(hV : 0<Vextract)(hv : Supported v.1.1) :
    0≤extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V Vextract p k := by
  unfold extractedErrorLabelScalar
  apply mul_nonneg
  · apply mul_nonneg
    · unfold firstErrorTailRadius errorCommonRadius
      exact div_nonneg (Real.rpow_nonneg hZ _) hV.le
    · exact mul_nonneg (normalizer_pos _ _ hv _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact Real.rpow_nonneg hZ _

private theorem error_actual_label_scalar_sum_nonneg {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(hs : Squarefree seed)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(reflected second : Bool)(l : FirstSourceLabel)
    (Z M a δ reserve error εcommon V : ℝ)(p : O)(k : ℕ)(hZ : 0≤Z) :
    0≤∑v∈actualSecondLabels s R seed,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V (volume s) p k := by
  apply Finset.sum_nonneg
  intro v hv
  exact extracted_error_label_scalar_nonneg reflected second l v Z M a δ reserve error εcommon
    V (volume s) p k hZ (volume_pos s)
    (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).1

private theorem error_menu_nonneg {Menu : Type*}[Fintype Menu]
    (cost : Menu→ℝ)(hc : ∀m,0≤cost m) : 0≤∑m,cost m :=
  Finset.sum_nonneg (fun m _=>hc m)

private theorem error_weighted_prime_cost {Label PrimeIndex : Type*}
    [Fintype Label][Fintype PrimeIndex]
    (mass : Label→ℝ)(cost : PrimeIndex→Fin 3→RayCharacter→Label→ℝ)
    (outside F : ℝ)(branch : Fin 3→ℝ)
    (hout : 0≤outside)(hb : ∀i,0≤branch i)
    (hc : ∀q i ψ j,0≤cost q i ψ j)(hm : ∀j,mass j≤F) :
    outside*(∑q,∑i,branch i*∑j,∑ψ,mass j*cost q i ψ j)≤
      F*(outside*(∑q,∑i,branch i*∑j,∑ψ,cost q i ψ j)) := by
  calc
    _≤outside*(∑q,∑i,branch i*∑j,∑ψ,F*cost q i ψ j) := by
      apply mul_le_mul_of_nonneg_left _ hout
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hb i)
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun ψ _=>mul_le_mul_of_nonneg_right (hm j) (hc q i ψ j))
    _=_ := by
      have h (q : PrimeIndex)(i : Fin 3) :
          branch i*(∑j,∑ψ,F*cost q i ψ j)=F*(branch i*∑j,∑ψ,cost q i ψ j) := by
        simp only [←Finset.mul_sum]
        ring
      simp_rw [h]
      simp only [←Finset.mul_sum]
      ring

/-- The first-bin mismatch is a fixed factor sixteen, not a new power loss. -/
theorem error_physical_bin_exponent_payment (Z F K seedNorm B εmass p exponent side M : ℝ)
    (hZ : 1<Z)(hF : 0≤F)(hK : 0≤K)(hs : 0≤seedNorm)
    (hbin : p+exponent-side≤4*Real.logb Z 2) :
    (F*Z^(B*εmass-side))*(K*Z^(p+exponent-M*((Cycle63.Arithmetic.lowReserve/2)))/seedNorm)≤
      16*F*K*Z^(B*εmass-M*((Cycle63.Arithmetic.lowReserve/2)))/seedNorm := by
  have hz : 0<Z:=zero_lt_one.trans hZ
  have he : B*εmass-side+(p+exponent-M*((Cycle63.Arithmetic.lowReserve/2)))≤
      4*Real.logb Z 2+(B*εmass-M*((Cycle63.Arithmetic.lowReserve/2))) := by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(F*K/seedNorm)*Z^(B*εmass-side+(p+exponent-M*((Cycle63.Arithmetic.lowReserve/2)))) := by
      rw [Real.rpow_add hz];ring
    _≤(F*K/seedNorm)*Z^(4*Real.logb Z 2+(B*εmass-M*((Cycle63.Arithmetic.lowReserve/2)))) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg (mul_nonneg hF hK) hs)
    _=_ := by rw [Real.rpow_add hz,geometry_low_bin_slack_payment Z hZ];ring

/-- Actual first columns provide all support, seed, and norm gates. -/
theorem actual_error_first_label_gates {ι : Type}[Fintype ι][DecidableEq ι]
    (s : Input ι)(R seed : Ideal O)(K Z ξ B : ℝ)(hK : 0<K)
    (hs : Squarefree seed)(hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤Z^B)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let l:=geometryFirstLabel s R seed K Z ξ hK bin j
    (Supported l.1.1 ∧ Supported l.1.2) ∧
      primeSupport l.1.1=primeSupport l.1.2 ∧
      (seed∣l.1.1 ∧ seed∣l.1.2) ∧
      ((l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) := by
  intro l
  have hc:=actual_common_gates s R seed hs hw₁ hw₂ j.1.val.1.val.1 j.1.val.1.val.2 j.1.val.1.property
  have hh:=commonLabels_supported
    (CenteredMomentActiveSource.activeSource
      (finiteColumns (Fintype.piFinset s.pools))
      (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)) _ _ j.1.val.1.property
  exact ⟨hh,hc.2.2.1,⟨hc.2.2.2.1,hc.2.2.2.2.1⟩,
    ⟨hc.2.2.2.2.2.1.trans hsource,hc.2.2.2.2.2.2.trans hsource⟩⟩

/-- One literal extracted packet before its prime/ray/first-column sum.
The first allocation is stored on the original first index. -/
def geometryErrorPhysicalScalarPacket {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(υ : Character)(vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ) : ℝ :=
  let C:=if reflected then l.1.2 else l.1.1
  let u:=child s C R B₁ χ t
  let Q:=Ideal.span {q}
  let R₂:=(R*C)*Q^k
  ∑Bp : errorLiftedActiveAllocations u Q k,
    let source:=child u (Q^k) (R*C) Bp.val υ vheight
    ∑v∈actualSecondLabels source R₂ L,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
        (volume s) (volume source) q k

/-- Inverse-key selection is exactly the original packet when the actual
extracted character is independent of the active Bp allocator. -/
theorem selected_error_physical_scalar_packet_at {ι Label : Type}[Fintype ι][Fintype Label]
    (s : Input ι)(reflected second : Bool)(first : Label→FirstSourceLabel)
    (projector : Label→Ideal O)(hinj : Function.Injective (fun j=>(first j,projector j)))
    (alloc : (j : Label)→actualAllocations s.pools
      (if reflected then (first j).1.2 else (first j).1.1))
    (R : Ideal O)(χ υ : Label→Character)(t vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ)(j : Label) :
    let e:=selectedLowFirstPairEquiv first projector hinj
    let pair:=e j
    geometryErrorPhysicalScalarPacket s reflected second pair.1.val pair.2.val R
      (selectedErrorAllocation s reflected first projector hinj alloc pair)
      (χ (e.symm pair)) t (υ (e.symm pair)) vheight q k Z M a δ reserve error εcommon=
    geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R (alloc j)
      (χ j) t (υ j) vheight q k Z M a δ reserve error εcommon := by
  intro e pair
  change geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R
    (selectedErrorAllocation s reflected first projector hinj alloc (selectedLowFirstPair first projector j))
    (χ (e.symm (e j))) t (υ (e.symm (e j))) vheight q k Z M a δ reserve error εcommon=_
  rw [Equiv.symm_apply_apply,selected_error_allocation_at]

/-- Literal mass-weighted extracted scalar sum on a common FIRST-projector
shell. Its source menu retains the original occupied-key allocator. -/
def ErrorPhysicalShellBound (N : ℕ)(lo ap εv B ε b bs Mmin εaffine K Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(_hcard : Fintype.card ι≤N)(_hlower : lo≤s.lower)
      (_hend : Endpoints b bs bs s)(_hvolume : volume s≤Z^B)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (_hM : Mmin≤M)(_hecommon : 0≤εcommon)(_hemass : 0≤εmass)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)(_hsource : sourceRadius s≤Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ap≤x)(_hs₂ : ∀x,s.W₂ x≠0→ap≤x)
      (W : 𝓢(ℝ,ℂ))(hK : 0<Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
        (column j).2.1.val)))
      (alloc : (j : Label)→actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
      (_hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
      (χ : Label→Character)(t T : ℝ)(_hT : 1≤T)
      (_hprojector : ∀j,Squarefree (column j).2.1.val)
      (_hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T),
    let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
    let projector:=fun j=>(column j).2.1.val
    let labels:=selectedLowFirstLabels first
    let Ds : labels→Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→Ds l→actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→Ds l→Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    ∀(P : Finset (Ideal O))(_hP : P.Nonempty)(_hprime : ∀Q∈P,Prime Q)
      (_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→IsCoprime (Ideal.span {q.val}) I),
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    ∀(υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→Bps l D q i→Character)(vheight : ℝ),
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (R*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (R*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
      let pair:=e j
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
    let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)
    (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,mass j*cost q i ψ j)≤
      16*F*K*Z^(B*εmass-M*((Cycle63.Arithmetic.lowReserve/2)))/(seed.absNorm:ℝ)

private def error_eventual_predicate {P : ℝ→Prop} (_ : ∀ᶠZ : ℝ in atTop,P Z) : ℝ→Prop := P

set_option maxHeartbeats 1200000 in
set_option linter.defProp false in
/-- Saved extracted-prime payment with literal original first-column mass.
The inverse occupied-key map retains each selected allocation. The FIRST
projector is the SECOND seed; the original outer seed is unchanged. -/
def eventual_actual_error_physical_shell_payment
    (N : ℕ)(lo ap εv B ε b bs : ℝ)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εv)(hB : 0≤B)(he : 0<ε)
    (hb : 1≤b)(hbs : 1≤bs)(Mmin εaffine : ℝ)(hMmin : 0<Mmin) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      2≤Z ∧ ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z :=
  let hBplus : 0≤B+1:=by linarith
  let data:=eventual_actual_error_dependent_saved_payment N lo εv (B+1) ε
    hlo hev hBplus he Mmin εaffine hMmin
  let K:=Classical.choose data
  let hKscalar : 0<K:=(Classical.choose_spec data).1
  let saved:=eventual_actual_selected_error_saved_payment N lo εv (B+1) ε
    hlo hev hBplus he Mmin εaffine hMmin
  let cap:=eventual_geometry_error_child_source_cap N b bs (1/2) hb hbs (by norm_num)
  let combined:=saved.2.and cap
  let pointwise : ∀Z,error_eventual_predicate combined Z →
      2≤Z ∧ ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z :=
    fun (Z : ℝ)(hz : error_eventual_predicate combined Z)=>And.intro hz.1.1 (
    fun {ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(hcard : Fintype.card ι≤N)(hlower : lo≤s.lower)
      (hend : Endpoints b bs bs s)(hvolume : volume s≤Z^B)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (hM : Mmin≤M)(hecommon : 0≤εcommon)(hemass : 0≤εmass)
      (hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
      (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hsource : sourceRadius s≤Z^B)
      (hs₁ : ∀x,s.W₁ x≠0→ap≤x)(hs₂ : ∀x,s.W₂ x≠0→ap≤x)
      (W : 𝓢(ℝ,ℂ))(hK : 0<Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
        (column j).2.1.val)))
      (alloc : (j : Label)→actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
      (hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
      (χ : Label→Character)(t T : ℝ)(hT : 1≤T)
      (hprojector : ∀j,Squarefree (column j).2.1.val)
      (hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T)=>
    let hZ : 1<Z:=by linarith [hz.1.1]
    let hZ0 : 0<Z:=zero_lt_one.trans hZ
    let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
    let projector:=fun j=>(column j).2.1.val
    let A:=Real.logb Z (volume s)
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let pBin:=((bin.2 2:ℝ)+1)*w
    let p:=min (B+1) pBin
    let exponent:=A-(bin.2 c:ℝ)*w+((bin.2 3:ℝ)+1)*w+((bin.2 4:ℝ)+1)*w
    let side:=(bin.2 2:ℝ)*w+A-((bin.2 c:ℝ)+1)*w+(bin.2 3:ℝ)*w+(bin.2 4:ℝ)*w
    let hbin : p+exponent-side≤4*Real.logb Z 2:=by
      have hp : p≤pBin:=min_le_right _ _
      have hg : pBin+exponent-side=4*w:=by dsimp only [pBin,exponent,side];ring
      linarith
    let gates:=actual_geometry_low_bin_scalar_gates s R seed (Z^M) Z ξ B A hK hZ hs hw₁ hw₂ hsource bin reflected
    let firstG:=fun j=>actual_error_first_label_gates s R seed (Z^M) Z ξ B hK hs hw₁ hw₂ hsource bin (column j)
    let hnplus : ∀j,((first j).1.1.absNorm:ℝ)≤Z^(B+1) ∧ ((first j).1.2.absNorm:ℝ)≤Z^(B+1):=
      fun j=>And.intro ((firstG j).2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
        ((firstG j).2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
    let hrad : ∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤Z^p:=by
      intro j
      rcases le_total (B+1) pBin with hp | hp
      · dsimp only [p]
        rw [min_eq_left hp]
        have h:=actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hw₁ hw₂ hsource (column j).1.val 2
        exact h.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
      · dsimp only [p]
        rw [min_eq_right hp]
        exact (gates.2 (column j)).1
    let pay:=hz.1.2 s hcard hlower reflected second T p exponent error εcommon M a δ reserve
      hT (min_le_left _ _) hecommon hM hloss seed hs hs0 first projector hinj
      (fun j=>(firstG j).1) (fun j=>(firstG j).2.1) (fun j=>(firstG j).2.2.1)
      hnplus hrad (fun j=>(gates.2 (column j)).2.1) hprojector hdyad R alloc χ t hf hw₁ hw₂
    let labels:=selectedLowFirstLabels first
    let Ds : labels→Finset (Ideal O):=fun l=>selectedLowFirstProjectors first projector l.val
    let e:=selectedLowFirstPairEquiv first projector hinj
    let alloc' : (l : labels)→Ds l→actualAllocations s.pools
        (if reflected then l.val.1.2 else l.val.1.1):=
      fun l D=>selectedErrorAllocation s reflected first projector hinj alloc ⟨l,D⟩
    let χ' : (l : labels)→Ds l→Character:=fun l D=>χ (e.symm ⟨l,D⟩)
    let u : (l : labels)→(D : Ds l)→Input (liveIndices (alloc' l D).val):=
      fun l D=>child s (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    fun (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
      (hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (hslot : ∀q : elementPool P,∀j I,I∈s.slots j→IsCoprime (Ideal.span {q.val}) I)=>
    let Bps:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)=>
      errorLiftedActiveAllocations (u l D) (Ideal.span {q.val}) (errorIndex i+1)
    fun (υ : (l : labels)→(D : Ds l)→(q : elementPool P)→(i : Fin 3)→
        RayCharacter→Bps l D q i→Character)(vheight : ℝ)=>
    let source:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      child (u l D) ((Ideal.span {q.val})^(errorIndex i+1))
        (R*(if reflected then l.val.1.2 else l.val.1.1)) Bp.val (υ l D q i ψ Bp) vheight
    let R₂:=fun (l : labels)(q : elementPool P)(i : Fin 3)=>
      (R*(if reflected then l.val.1.2 else l.val.1.1))*(Ideal.span {q.val})^(errorIndex i+1)
    let children:=fun (l : labels)(D : Ds l)(q : elementPool P)(i : Fin 3)
        (ψ : RayCharacter)(Bp : Bps l D q i)=>
      actualSecondLabels (source l D q i ψ Bp) (R₂ l q i) D.val
    let hchildslot:=fun (l : labels)(D : Ds l)(q : elementPool P)=>actual_child_full_slot_coprime s (Ideal.span {q.val})
      (hslot q) (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
    let hsource' : ∀l D q i ψ Bp,sourceRadius (source l D q i ψ Bp)≤Z^(B+1):=by
      intro l D q i ψ Bp
      have hc:=hz.2.2 s B hcard hend hvolume
        (if reflected then l.val.1.2 else l.val.1.1) R (alloc' l D) (χ' l D) t
        (selected_error_allocation_nonzero s reflected first projector hinj alloc R hf ⟨l,D⟩)
        q.val (elementPool_data P hprime hbad q.val q.property).1.ne_zero
        (errorIndex i+1) (hchildslot l D q) Bp.val (υ l D q i ψ Bp) vheight
      exact hc.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
    let hpaid:=pay P hP hprime hbad hchildslot υ vheight hsource'
    let cost:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
      let pair:=e j
      ∑Bp : Bps pair.1 pair.2 q i,∑v∈children pair.1 pair.2 q i ψ Bp,
        extractedErrorLabelScalar reflected second pair.1.val v Z M a δ reserve error εcommon
          (volume s) (volume (source pair.1 pair.2 q i ψ Bp)) q.val (errorIndex i+1)
    let hc : ∀(q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label),0≤cost q i ψ j:=by
      intro q i ψ j
      exact error_menu_nonneg _ (fun Bp=>error_actual_label_scalar_sum_nonneg
        (source (e j).1 (e j).2 q i ψ Bp) (R₂ (e j).1 q i) (e j).2.val
        (by
          have h:=(selected_low_pair_inverse_fields first projector hinj (e j)).2
          rw [←h]
          exact hprojector (e.symm (e j))) hw₁ hw₂ reflected second (e j).1.val
        Z M a δ reserve error εcommon (volume s) q.val (errorIndex i+1) hZ0.le)
    let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
    let hF : 0≤F:=(geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le
    let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)
    let hm : ∀j,mass j≤F*Z^(B*εmass-side):=fun j=>actual_geometry_low_uniform_mass
      reflected N lo ap hlo hap s R seed W M Z ξ B εmass side hZ hK hemass hcard hlower
      hs hw₁ hw₂ hsource hs₁ hs₂ bin (column j) (gates.2 (column j)).2.2
    let weighted:=error_weighted_prime_cost mass cost (56/(P.card:ℝ))
      (F*Z^(B*εmass-side)) (fun i=>16*(errorIndex i+2:ℝ))
      (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (fun i=>by positivity) hc hm
    let binPaid:=error_physical_bin_exponent_payment Z F K (seed.absNorm:ℝ) B εmass p exponent side M
      hZ hF hKscalar.le (Nat.cast_nonneg _) hbin
    show (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,mass j*cost q i ψ j)≤
      16*F*K*Z^(B*εmass-M*((Cycle63.Arithmetic.lowReserve/2)))/(seed.absNorm:ℝ) from
    weighted.trans ((mul_le_mul_of_nonneg_left hpaid
      (mul_nonneg hF (Real.rpow_nonneg hZ0.le _))).trans binPaid)
  )
  Exists.intro K (And.intro hKscalar (combined.mono pointwise))

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.extracted_error_label_scalar_nonneg
#print axioms OAI.SevenEighths.Cycle63InitialMass.error_physical_bin_exponent_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_error_first_label_gates

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_error_physical_shell_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.ErrorPhysicalShellBound

#print axioms OAI.SevenEighths.Cycle63InitialMass.geometryErrorPhysicalScalarPacket
#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_error_physical_scalar_packet_at
