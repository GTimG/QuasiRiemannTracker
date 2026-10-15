/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B090
import Candidate.Bundles.B108
import Candidate.Bundles.B109
import Candidate.Bundles.B135
import Candidate.Bundles.B139
import Candidate.Bundles.B140
import Candidate.Bundles.B149
import Candidate.Bundles.B165
import Candidate.Bundles.B166
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

import Candidate.Bundles.B167Part2
/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalTotal; sha256 02be644d441d2153e9ab86f54704ecc6fa7f6de72ae09d6565d465348f1f779f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
                                                                
                                                         
                                                          
                                                                   
                                                           
                                                        

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationActiveFactor CenteredMomentPrimeElements
open CenteredMomentSecondRadicalBudget CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open Cycle61Moment CenteredMomentSourceLiveColumn CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSourceMass CenteredMomentCanonicalFirst
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentRankinRadical ActualEisensteinCubic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
local notation "O" => HeckeFamily.O
local instance errorPhysicalTotalSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


/-- Complete extracted scalar cost retains its prime average and all three
branch factors before the first allocation is paid. -/
def geometryErrorPhysicalCompleteCost {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(P : Finset (Ideal O))
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ)
    (Z M a δ reserve error εcommon : ℝ) : ℝ :=
  (56/(P.card:ℝ))*∑q : elementPool P,∑i : Fin 3,
    (16*(errorIndex i+2:ℝ))*∑ψ : RayCharacter,
      geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t
        (υ q i ψ) vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon

private theorem error_complete_order {Label Q : Type}[Fintype Label][Fintype Q]
    (mass : Label→ℝ)(cost : Q→ Fin 3→ RayCharacter→ Label→ℝ)
    (outside : ℝ)(branch : Fin 3→ℝ) :
    (∑j,mass j*(outside*∑q,∑i,branch i*∑ψ,cost q i ψ j))=
      outside*(∑q,∑i,branch i*∑j,∑ψ,mass j*cost q i ψ j) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro ψ _
  ring

set_option maxHeartbeats 1200000 in
/-- Actual shell payment on the original first indices, with no inverse-key
allocator or extracted-character choice left in the cost. -/
theorem actual_error_physical_complete_shell
    (N : ℕ)(lo ap εv B ε b bs Mmin εaffine K Z : ℝ)
    (paid : ErrorPhysicalShellBound N lo ap εv B ε b bs Mmin εaffine K Z)
    {ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
    (s : Input ι)(hcard : Fintype.card ι≤ N)(hlower : lo≤ s.lower)
    (hend : Endpoints b bs bs s)(hvolume : volume s≤ Z^B)
    (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
    (hM : Mmin≤ M)(hecommon : 0≤εcommon)(hemass : 0≤εmass)
    (hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
    (R seed : Ideal O)(hs : Squarefree seed)(hs0 : seed≠0)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(hsource : sourceRadius s≤ Z^B)
    (hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
    (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j),
      (column j).2.1.val)))
    (alloc : (j : Label)→ actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)))
    (hf : ∀j,frozenCoefficient (alloc j).val
      (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j)) R s.ν s.W s.P≠0)
    (χ : Label→ Character)(t T : ℝ)(hT : 1≤ T)
    (hprojector : ∀j,Squarefree (column j).2.1.val)
    (hdyad : ∀j,T≤((column j).2.1.val.absNorm:ℝ) ∧ ((column j).2.1.val.absNorm:ℝ)<2*T)
    (P : Finset (Ideal O))(hP : P.Nonempty)(hprime : ∀Q∈P,Prime Q)
    (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I)
    (υ : Label→ elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ) :
    (∑j,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)) (column j).2.1.val R
        (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ) := by
  let first:=fun j=>geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j)
  let projector:=fun j=>(column j).2.1.val
  let e:=selectedLowFirstPairEquiv first projector hinj
  have hp:=paid s hcard hlower hend hvolume reflected second M ξ error εcommon εmass a δ reserve
    hM hecommon hemass hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hK bin column hinj
    alloc hf χ t T hT hprojector hdyad P hP hprime hbad hslot
    (fun l D q i ψ _=>υ (e.symm ⟨l,D⟩) q i ψ) vheight
  let paired:=fun (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label)=>
    let pair:=e j
    geometryErrorPhysicalScalarPacket s reflected second pair.1.val pair.2.val R
      (selectedErrorAllocation s reflected first projector hinj alloc pair)
      (χ (e.symm pair)) t (υ (e.symm pair) q i ψ) vheight q.val (errorIndex i+1)
      Z M a δ reserve error εcommon
  change (56/(P.card:ℝ))*(∑q,∑i,(16*(errorIndex i+2:ℝ))*∑j,∑ψ,
    geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j)*paired q i ψ j)≤ _ at hp
  have heq (q : elementPool P)(i : Fin 3)(ψ : RayCharacter)(j : Label) : paired q i ψ j=
      geometryErrorPhysicalScalarPacket s reflected second (first j) (projector j) R (alloc j)
        (χ j) t (υ j q i ψ) vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon :=
    selected_error_physical_scalar_packet_at s reflected second first projector hinj alloc R χ
      (fun j=>υ j q i ψ) t vheight q.val (errorIndex i+1) Z M a δ reserve error εcommon j
  simp_rw [heq] at hp
  unfold geometryErrorPhysicalCompleteCost
  rw [error_complete_order]
  exact hp

private theorem error_total_label_nonneg {κ : Type*}[Fintype κ]
    (s : Input κ)(R seed : Ideal O)(hs : Squarefree seed)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)(reflected second : Bool)(l : FirstSourceLabel)
    (Z M a δ reserve error εcommon V : ℝ)(p : O)(k : ℕ)(hZ : 0≤ Z) :
    0≤∑v∈actualSecondLabels s R seed,
      extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon V (volume s) p k := by
  exact Finset.sum_nonneg (fun v hv=>extracted_error_label_scalar_nonneg reflected second l v
    Z M a δ reserve error εcommon V (volume s) p k hZ
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (actual_second_labels_gates s R seed hs hw₁ hw₂ v hv).1)

private theorem error_total_menu_nonneg {Menu : Type*}[Fintype Menu]
    (cost : Menu→ℝ)(hc : ∀m,0≤ cost m) : 0≤∑m,cost m :=
  Finset.sum_nonneg (fun m _=>hc m)

private theorem error_total_packet_nonneg {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(υ : Character)(vheight : ℝ)(q : O)(k : ℕ)
    (Z M a δ reserve error εcommon : ℝ)(hZ : 0≤ Z)(hL : Squarefree L)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0) :
    0≤ geometryErrorPhysicalScalarPacket s reflected second l L R B₁ χ t υ vheight q k
      Z M a δ reserve error εcommon := by
  let C:=if reflected then l.1.2 else l.1.1
  let u:=child s C R B₁ χ t
  let Q:=Ideal.span {q}
  let source:=fun (Bp : errorLiftedActiveAllocations u Q k)=>child u (Q^k) (R*C) Bp.val υ vheight
  change 0≤∑Bp : errorLiftedActiveAllocations u Q k,∑v∈actualSecondLabels (source Bp) ((R*C)*Q^k) L,
    extractedErrorLabelScalar reflected second l v Z M a δ reserve error εcommon
      (volume s) (volume (source Bp)) q k
  exact error_total_menu_nonneg _ (fun Bp=>error_total_label_nonneg
    (source Bp) ((R*C)*Q^k) L hL hw₁ hw₂ reflected second l
    Z M a δ reserve error εcommon (volume s) q k hZ)

/-- Positivity comes from the actual supported second labels in each
literal extracted child, including allocations before ordinary restriction. -/
theorem geometry_error_physical_complete_cost_nonneg {ι : Type}[Fintype ι]
    (s : Input ι)(reflected second : Bool)(l : FirstSourceLabel)(L R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ)(P : Finset (Ideal O))
    (υ : elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ)
    (Z M a δ reserve error εcommon : ℝ)(hZ : 0≤ Z)(hL : Squarefree L)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0) :
    0≤ geometryErrorPhysicalCompleteCost s reflected second l L R B₁ χ t P υ vheight
      Z M a δ reserve error εcommon := by
  unfold geometryErrorPhysicalCompleteCost
  apply mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  exact error_total_menu_nonneg _ (fun q=>error_total_menu_nonneg _ (fun i=>
    mul_nonneg (by positivity) (error_total_menu_nonneg _ (fun ψ=>
      error_total_packet_nonneg s reflected second l L R B₁ χ t (υ q i ψ) vheight
        q.val (errorIndex i+1) Z M a δ reserve error εcommon hZ hL hw₁ hw₂))))

/-- The first-projector shell is paid before all original selected first
indices are summed. No first arithmetic label is counted. -/
def ErrorPhysicalSelectedBound (N : ℕ)(lo ap εv B ε b bs Mmin εaffine U εshell K Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
      (s : Input ι)(_hcard : Fintype.card ι≤ N)(_hlower : lo≤ s.lower)
      (_hend : Endpoints b bs bs s)(_hvolume : volume s≤ Z^B)
      (_hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
      (reflected second : Bool)(M ξ error εcommon εmass a δ reserve : ℝ)
      (_hM : Mmin≤ M)(_hecommon : 0≤εcommon)(_hemass : 0≤εmass)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)(_hsource : sourceRadius s≤ Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(_hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→ firstLiveColumns
        (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus))
      (_hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j).val,
        (column j).val.2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j).val))
      (_hf : ∀j,frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin (column j).val) R s.ν s.W s.P≠0)
      (χ : Label→ Character)(t : ℝ)(P : Finset (Ideal O))(_hP : P.Nonempty)
      (_hprime : ∀Q∈P,Prime Q)(_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I)
      (υ : Label→ elementPool P→ Fin 3→ RayCharacter→ Character)(vheight : ℝ),
    (∑j,geometryFirstHighMass reflected s R seed W M Z ξ εmass hK bin (column j).val*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin (column j).val) (column j).val.2.1.val R
        (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^(B*εmass+εshell-M*(7/60000000))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1200000 in
/-- Uniform selected first-column payment from actual stored-pool caps and
literal extracted packets. Constants precede every source and height. -/
theorem eventual_actual_error_physical_selected_payment
    (N : ℕ)(lo ap εv B ε b bs Mmin εaffine U εshell : ℝ)
    (hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(hMmin : 0< Mmin)(hU : 0≤ U)(heshell : 0<εshell) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ErrorPhysicalSelectedBound N lo ap εv B ε b bs Mmin εaffine U εshell K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_error_physical_shell_payment N lo ap εv B ε b bs
    hlo hap hev hB he hb hbs Mmin εaffine hMmin
  obtain ⟨C,hC,hcount⟩:=eventual_actual_geometry_selected_first_shell_subpower N U εshell hU heshell
  refine ⟨K*C,mul_pos hK hC,?_⟩
  filter_upwards [hpaid,hcount] with Z hp hc
  refine ⟨hp.1,?_⟩
  intro ι Label _ _ _ s hn hl hend hv hpool reflected second M ξ error εcommon εmass a δ reserve
    hM hecommon hemass hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin column hinj alloc hf
    χ t P hP hprime hbad hslot υ vheight
  let cols:=fun j=>(column j).val
  let mass:=fun j=>geometryFirstHighMass reflected s R seed W M Z ξ εmass hpow bin (cols j)
  let cost:=fun j=>geometryErrorPhysicalCompleteCost s reflected second
    (geometryFirstLabel s R seed (Z^M) Z ξ hpow bin (cols j)) (cols j).2.1.val R
    (alloc j) (χ j) t P (υ j) vheight Z M a δ reserve error εcommon
  let F:=geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin
  let E:=16*F*K*Z^(B*εmass-M*(7/60000000))/(seed.absNorm:ℝ)
  have hz : 1≤ Z:=by linarith [hp.1]
  have hE : 0≤ E:=by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le)
      hK.le) (Real.rpow_nonneg (zero_le_one.trans hz) _)) (Nat.cast_nonneg _)
  have hbound (n : ℤ)(hns : n∈selectedShells (selectedFirstProjectors cols)) :
      (∑j : SelectedFirstShell cols n,mass j.val*cost j.val)≤ E := by
    have hscale:=actual_geometry_selected_first_shell_scale s N R seed (Z^M) Z ξ U hpow
      hn hz hU hpool bin cols n hns
    have hrestrict:=actual_geometry_selected_first_shell_restriction reflected s R seed (Z^M) Z ξ hpow
      bin column alloc hinj hf n
    exact actual_error_physical_complete_shell N lo ap εv B ε b bs Mmin εaffine K Z hp.2
      s hn hl hend hv reflected second M ξ error εcommon εmass a δ reserve hM hecommon hemass hloss
      R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin
      (fun j : SelectedFirstShell cols n=>cols j.val) hrestrict.1 (fun j=>alloc j.val)
      hrestrict.2.1 (fun j=>χ j.val) t (dyadicScale n) hscale.1
      (fun j=>(selected_first_shell_gates cols n j).1) hrestrict.2.2 P hP hprime hbad hslot
      (fun j=>υ j.val) vheight
  have hm:=selected_first_shell_payment cols
    (fun j=>actual_first_live_squarefree _ _ _ (column j).property)
    (fun j=>mass j*cost j) E C Z εshell hE
    (hc.2 s hn hpool R seed (Z^M) ξ hpow bin cols) hbound
  apply hm.trans_eq
  dsimp only [E,F]
  rw [show B*εmass+εshell-M*(7/60000000)=εshell+(B*εmass-M*(7/60000000)) by ring,
    Real.rpow_add (zero_lt_one.trans_le hz)]
  ring

/-- Undivided first allocation weights ingest the complete physical cost.
The displayed exponent includes first selection and shared shell losses. -/
def ErrorPhysicalAllocationBound {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z : ℝ) : Prop :=
  ∀(s : Input ι)(_hcard : Fintype.card ι≤ N)(_hmass : ∀i,s.M i≤ Cs)
      (_hlower : lo≤ s.lower)(_hend : Endpoints b bs bs s)(_hvolume : volume s≤ Z^B)
      (_hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U)
      (reflected second : Bool)(M error εcommon a δ reserve : ℝ)
      (_hM : Mmin≤ M)(_hecommon : 0≤εcommon)
      (_hloss : error+εv+(B+1)*εcommon+ε≤64*geometryLossUnit Mmin εaffine)
      (R seed : Ideal O)(_hs : Squarefree seed)(_hs0 : seed≠0)
      (_hw₁ : s.W₁ 0=0)(_hw₂ : s.W₂ 0=0)
      (_hsourcepos : 0< sourceRadius s)(_hsource : sourceRadius s≤ Z^B)
      (_hs₁ : ∀x,s.W₁ x≠0→ ap≤ x)(_hs₂ : ∀x,s.W₂ x≠0→ ap≤ x)
      (W : 𝓢(ℝ,ℂ))(hK : 0< Z^M)(bin : ℤ×(Fin 5→ℤ))
      (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK bin)))
      (_hrows : rows⊆firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hK bin) (fun _=>logAnnulus))
      (t : ℝ)(P : Finset (Ideal O))(_hP : P.Nonempty)
      (_hprime : ∀Q∈P,Prime Q)(_hbad : ∀Q∈P,Q∉fixedBadPrimes)
      (_hslot : ∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I),
    let C:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^M) Z ξ hK bin j.val
    ∀(υ : (j : rows)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character)
      (vheight : ℝ),
    let A:=Real.logb Z (volume s)
    let weight:=fun q=>normPhase (coordinateBlock s R seed W (Z^M) Z ξ q)
    let cost:=fun (j : rows)(alloc : actualAllocations s.pools (C j))=>
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^M) Z ξ hK bin j.val) j.val.2.1.val R alloc
        (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hK bin j.val) t P
        (υ j alloc) vheight Z M a δ reserve error εcommon
    (∑j : rows,∑alloc : actualAllocations s.pools (C j),
      geometryAllocationWeight reflected s R seed (Z^M) Z ξ M A hK bin weight N b j.val alloc*
        cost j alloc)≤
      16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
        Z^((B+1)*εalloc+εshell-M*(7/60000000))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1600000 in
/-- Genuine selected first mass and allocation selection pay every original
allocation. The prime average occurs once, inside the literal cost. -/
theorem eventual_actual_error_physical_allocation_payment {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc : ℝ)
    (hCs : 1≤ Cs)(hlo : 0< lo)(hap : 0< ap)(hev : 0<εv)(hB : 0≤ B)(he : 0<ε)
    (hb : 1≤ b)(hbs : 1≤ bs)(hMmin : 0< Mmin)(hU : 0≤ U)(heshell : 0<εshell)
    (hξ : 0≤ξ)(healloc : 0<εalloc) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z := by
  obtain ⟨K,hK,hpaid⟩:=eventual_actual_error_physical_selected_payment
    N lo ap εv B ε b bs Mmin εaffine U εshell hlo hap hev hB he hb hbs hMmin hU heshell
  obtain ⟨D,hD,hselection⟩:=actual_geometry_weighted_selected_cost (ι:=ι)
    N Cs b εalloc B 0 B ξ hCs healloc hB (by norm_num) hB hξ
  refine ⟨K*D,mul_pos hK hD,?_⟩
  filter_upwards [hpaid,hselection] with Z hp ha
  refine ⟨hp.1,?_⟩
  intro s hn hm hl hend hv hpool reflected second M error εcommon a δ reserve hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot
    C υ vheight A weight cost
  let E:=16*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*K*
    Z^(B*εalloc+εshell-M*(7/60000000))/(seed.absNorm:ℝ)
  have hKi : (Z^M)⁻¹≤ Z^(0:ℝ):=by
    rw [Real.rpow_zero]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow ha.1 (hMmin.le.trans hM))
  have hC (j : rows) : C j≠0:=by
    cases reflected
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hpow bin j.val.1).hC.1
    · exact (geometryFirstSource s R seed (Z^M) Z ξ hpow bin j.val.1).hD.1
  have hcost (j : rows)(alloc : actualAllocations s.pools (C j)) : 0≤ cost j alloc:=
    geometry_error_physical_complete_cost_nonneg s reflected second
      (geometryFirstLabel s R seed (Z^M) Z ξ hpow bin j.val) j.val.2.1.val R alloc
      (geometryColumnCharacter reflected s R seed (Z^M) Z ξ hpow bin j.val) t P (υ j alloc)
      vheight Z M a δ reserve error εcommon (zero_le_one.trans ha.1)
      (actual_first_live_squarefree _ _ _ (hrows j.property)) hw₁ hw₂
  have hselected {Label : Type}[Fintype Label](column : Label → rows)
      (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^M) Z ξ hpow bin (column j).val,
        (column j).val.2.1.val)))
      (alloc : (j : Label)→ actualAllocations s.pools (C (column j)))
      (hf : ∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) :
      (∑j,‖geometryColumnScalar reflected s R seed (Z^M) Z ξ M A hpow bin weight (column j).val‖^2*
        ((C (column j)).absNorm:ℝ)^(εalloc-1)*cost (column j) (alloc j))≤ E := by
    let live : Label→ firstLiveColumns (geometryFirstSource s R seed (Z^M) Z ξ hpow bin) (fun _=>logAnnulus):=
      fun j=>⟨(column j).val,hrows (column j).property⟩
    have hh:=hp.2 s hn hl hend hv hpool reflected second M ξ error εcommon εalloc a δ reserve
      hM hecommon healloc.le hloss R seed hs hs0 hw₁ hw₂ hsource hs₁ hs₂ W hpow bin live hinj
      alloc hf (fun j=>geometryColumnCharacter reflected s R seed (Z^M) Z ξ hpow bin (column j).val)
      t P hP hprime hbad hslot (fun j=>υ (column j) (alloc j)) vheight
    simpa only [geometryFirstHighMass,live,cost,A,weight,
      CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hpay:=ha.2 s hn hm reflected R seed (Z^M) M A hpow bin weight hs hw₁ hw₂
    hsourcepos hsource hv hKi rows E cost hcost hC hselected
  apply hpay.trans_eq
  dsimp only [E]
  rw [show (B+1)*εalloc+εshell-M*(7/60000000)=
    εalloc+(B*εalloc+εshell-M*(7/60000000)) by ring,
    Real.rpow_add (zero_lt_one.trans_le ha.1)]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_error_physical_complete_shell
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_error_physical_complete_cost_nonneg
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_physical_selected_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_error_physical_allocation_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryErrorPhysicalTotal -/

