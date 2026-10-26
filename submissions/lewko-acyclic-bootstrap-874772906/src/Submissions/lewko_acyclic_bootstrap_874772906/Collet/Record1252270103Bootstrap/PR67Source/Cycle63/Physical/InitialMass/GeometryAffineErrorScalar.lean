import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorPhysicalTotal
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePoolCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffinePrimeGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0 license. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
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
local instance affineErrorScalarSumDecidableEq {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open Cycle63InitialSource ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedRayDictionary

variable [Cycle63.AffineLedger] in
/-- Increasing a fixed payment constant preserves the actual physical
allocation contract; every remaining factor is nonnegative. -/
theorem error_physical_allocation_constant_mono {ι : Type}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K K' Z : ℝ)
    (hZ : 0≤Z)(hlo : 0<lo)(hap : 0<ap)(hK : K≤K')
    (paid : ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z) :
    ErrorPhysicalAllocationBound (ι:=ι) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K' Z := by
  intro s hn hm hl hend hv hpool reflected second unit M error εcommon a δ reserve hunit hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot
    C υ vheight A weight cost
  have h:=paid s hn hm hl hend hv hpool reflected second unit M error εcommon a δ reserve hunit hM hecommon hloss
    R seed hs hs0 hw₁ hw₂ hsourcepos hsource hs₁ hs₂ W hpow bin rows hrows t P hP hprime hbad hslot υ vheight
  apply h.trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (mul_nonneg (by norm_num)
        (geometry_high_factor_pos reflected _ bin
          (geometrySupportConstant_pos N lo ap ap hlo hap hap)).le))
      (Real.rpow_nonneg hZ _)) (Nat.cast_nonneg _)

variable [Cycle63.AffineLedger] in
/-- Finite ambient slot subsets share one constant and one threshold.
Each subset keeps its own literal source and original allocation types. -/
theorem uniform_error_physical_allocation_payment {α : Type}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc : ℝ)
    (hCs : 1≤Cs)(hlo : 0<lo)(hap : 0<ap)(hev : 0<εv)(hB : 0≤B)(he : 0<ε)
    (hb : 1≤b)(hbs : 1≤bs)(hMmin : 0<Mmin)(hU : 0≤U)(heshell : 0<εshell)
    (hξ : 0≤ξ)(healloc : 0<εalloc) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧ ∀T : Finset α,
      ErrorPhysicalAllocationBound (ι:=T) N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc K Z := by
  have data (T : Finset α):=eventual_actual_error_physical_allocation_payment (ι:=T)
    N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    hCs hlo hap hev hB he hb hbs hMmin hU heshell hξ healloc
  choose C hC hbound using data
  let K:=1+∑T : Finset α,C T
  have hn : ∀T : Finset α,0≤C T:=fun T=>(hC T).le
  have hK : 0<K:=by
    have hsum:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=>hn T)
    dsimp only [K];linarith
  have hCK (T : Finset α) : C T≤K:=by
    have hh:=Finset.single_le_sum (fun T _=>hn T) (Finset.mem_univ T)
    dsimp only [K];linarith
  refine ⟨K,hK,?_⟩
  filter_upwards [Filter.eventually_all.mpr hbound,eventually_ge_atTop (2:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T
  exact error_physical_allocation_constant_mono N Cs lo ap εv B ε b bs Mmin εaffine U εshell ξ εalloc
    (C T) K Z (by linarith) hlo hap (hCK T) (hz T).2

variable {α : Type}[Fintype α][DecidableEq α]

variable [Cycle63.AffineLedger] in
/-- The complete physical scalar payment at a parent input with the source gates of the
affine step. The actual prime pool, characters and undivided allocation weights are kept;
the branch reserve is measured in the ledger unit one, the source at the radial scale `Mrow`. -/
def AffineErrorScalarBound (Cs εv ε εaffine εshell ξ εalloc K Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4)),
  GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z →
  ∀(P : Finset (Ideal O)),P.Nonempty → (∀Q∈P,Prime Q) → (∀Q∈P,Q∉fixedBadPrimes) →
    (∀q : elementPool P,∀j I,I∈s.slots j→ IsCoprime (Ideal.span {q.val}) I) →
  ∀(R seed : Ideal O),Squarefree seed → seed≠0 → ∀Mrow : ℝ,0≤ Mrow →
  ∀(reflected second : Bool)(amp error εcommon reserve : ℝ),
  0≤εcommon → error+εv+4*εcommon+ε≤64*geometryLossUnit 1 εaffine →
  ∀(Φ : 𝓢(ℝ,ℂ))(bin : ℤ×(Fin 5→ℤ)),
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK bin) (fun _=>logAnnulus)
  let C:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK bin j.val
  ∀(height : ℝ)(υ : (j : rows)→actualAllocations s.pools (C j)→
    elementPool P→Fin 3→RayCharacter→ Character)(vheight : ℝ),
  let A:=Real.logb Z (CenteredMomentAmplificationChildInput.volume s)
  let weight:=fun q=>normPhase (coordinateBlock s R seed Φ (Z^Mrow) Z ξ q)
  (∑j : rows,∑alloc : actualAllocations s.pools (C j),
    geometryAllocationWeight reflected s R seed (Z^Mrow) Z ξ Mrow A hK bin weight (Fintype.card α) (9/4) j.val alloc*
      geometryErrorPhysicalCompleteCost s reflected second
        (geometryFirstLabel s R seed (Z^Mrow) Z ξ hK bin j.val) j.val.2.1.val R alloc
        (geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ hK bin j.val) height P (υ j alloc)
        vheight Z 1 Mrow amp (3*amp) reserve error εcommon)≤
    16*geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) bin*K*
      Z^(4*εalloc+εshell-((Cycle63.AffineLedger.lowReserve/2):ℝ))/(seed.absNorm:ℝ)

set_option maxHeartbeats 1600000 in
variable [Cycle63.AffineLedger] in
/-- The affine source gates discharge every source gate of the saved physical payment.
A single constant precedes all live slot subsets, parent inputs, punctures and seeds. -/
theorem eventual_actual_affine_error_scalar_payment
    (Cs εv ε εaffine εshell ξ εalloc : ℝ)(hCs : 1≤Cs)
    (hev : 0<εv)(he : 0<ε)(heshell : 0<εshell)(hξ : 0≤ξ)(healloc : 0<εalloc) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      AffineErrorScalarBound (α:=α) Cs εv ε εaffine εshell ξ εalloc K Z := by
  obtain ⟨K,hK,hpaid⟩:=uniform_error_physical_allocation_payment (α:=α)
    (Fintype.card α) Cs 1 (1/4) εv 3 ε (9/4) (9/4) 1 εaffine 3 εshell ξ εalloc
    hCs (by norm_num) (by norm_num) hev (by norm_num) he (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heshell hξ healloc
  refine ⟨K,hK,?_⟩
  filter_upwards [hpaid] with Z hp
  refine ⟨hp.1,?_⟩
  intro hZ T s p caps P hP hprime hbad hslot R seed hs hs0 Mrow hMrow reflected second amp error
    εcommon reserve hecommon hloss Φ bin hK rows C height υ vheight A weight
  have hvol : CenteredMomentAmplificationChildInput.volume s≤Z^(3:ℝ):=
    caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hh:=(hp.2 T) s caps.card caps.controls caps.lower.symm.le caps.endpoints hvol caps.poolCap
    reflected second 1 Mrow error εcommon amp (3*amp) reserve le_rfl hMrow hecommon
    (by simpa only [show (3:ℝ)+1=4 by norm_num] using hloss)
    R seed hs hs0 caps.zero₁ caps.zero₂ caps.sourcePositive caps.sourceCap
    caps.support₁ caps.support₂ Φ hK bin rows (Finset.Subset.refl _) height P hP hprime hbad hslot
    υ vheight
  simpa only [one_mul,show (3:ℝ)+1=4 by norm_num] using hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
