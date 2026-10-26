/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted for the actual MAIN frozen-one constructor from the retained LOW cap/aggregate chain.
Inherited upstream notices remain required.
Actual full-pool and raw-corner support for exceptional first children. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.SelectedExceptionalInitialCapsFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.Contraction.SelectedMainExceptionalAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularSelectedStateCapsCharacter
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Contraction.SelectedMainExceptional
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization CenteredMomentSupport
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceRow
open Cycle61InitialMass Record1252270103Second OAI.SevenEighths.Record1252270103Source
open QRH.Record1252270103Low InitialPhysical InitialTruncated
open Low.SelectedExceptionalNormalized ForcedCost Pool
open CenteredMomentWholeDivisorShell
open High.GlobalPhysical SecondSectorDatum CenteredMomentMobiusRegroup CenteredMomentDivisorBoundary
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _



variable {α:Type*} [Fintype α]

open QRH.Record1252270103Source.Low.SelectedExceptionalInitialCaps
open QRH.Record1252270103Source.InitialRegularToTruncated
section Family
variable {α Label:Type*}[Fintype α][Fintype Label]
variable (s:Input α)(W W₁ W₂:𝓢(ℝ,ℂ))(Z:ℝ)(R:Ideal O)
    (C seed:Label→Ideal O)(B:∀l,actualAllocations s.pools (C l))
    (τ:Label→Character)(t:Label→ℝ)(P:Finset (Ideal O))
    (hseed:∀l,Squarefree (seed l))(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (K Tsec Tenergy amplitude:Label→ℝ)(ξ:ℝ)(hK:∀l,0<K l)
    (χ₀:Label→RayCharacter)(m:O)

local notation "fam"=>mainAllocatedFamily s W W₁ W₂ Z R C seed B τ t P hseed hz₁ hz₂ K Tsec Tenergy amplitude ξ hK χ₀ m

/-- Every exceptional cap is discharged from the original parent data,
actual first allocation and fixed-cell pool. The caller supplies polynomial
input bounds only; no second-label, energy or physical-norm premise remains. -/
theorem mainAllocatedFamily_polynomialCaps (Q:Ideal O)(a b amp ell mesh loss Bsource:ℝ)(depth:ℕ)
    (hZ:1<Z)(hb:0≤b)(hR:R≠0)(hRcap:(R.absNorm:ℝ)≤Z)
    (hC:∀l,C l≠0)(hCcap:∀l,((C l).absNorm:ℝ)≤Z^(2:ℝ))
    (hW₁:s.W₁=(W₁:ℝ→ℂ))(hW₂:s.W₂=(W₂:ℝ→ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (hb₁:s.b₁≤b)(hb₂:s.b₂≤b)(hb₁0:0≤s.b₁)(hb₂0:0≤s.b₂)
    (hhi:∀i,1≤s.hi i)(hP:∀i,1≤s.P i)(hsource:sourceRadius s≤Z^(2:ℝ))
    (hfull:∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^(4:ℝ))
    (hplain:b^2*(s.X₁*s.X₂)≤Z^(2:ℝ))
    (hpool:FixedCellPoolData P Z amp ell mesh loss 12 Bsource depth)
    (hdepth:(2:ℝ)/ell≤depth)(havoid:∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (hchar:∀l,((τ l).modulus.absNorm:ℝ)≤Z^(5:ℝ))
    (hradius:∀l,frequencyRadius (Tsec l) Z ξ≤Z^(3:ℝ))
    (hfour:(4:ℝ)≤Z)(hfixed:(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)*2≤Z)
    (Lref:ℝ)(hLref:0<Lref)(hX₁:Lref≤s.X₁)(hX₂:Lref≤s.X₂)(hY₁:Lref≤s.Y₁)(hY₂:Lref≤s.Y₂):
    PolynomialCaps fam ((fam).retainedRadial Q (fun q=>Lref/((C q.1).absNorm:ℝ)))
      Q a b 5 13 4 4 12 amp 2 12 ell 4 depth := by
  intro q
  let f:=fam
  let d:=f.datum Q q
  let rad:=f.retainedRadial Q (fun q=>Lref/((C q.1).absNorm:ℝ))
  have hcsource:sourceRadius (child s (C q.1) R (B q.1) (τ q.1) (t q.1))≤Z^(2:ℝ):=
    (child_source_radius_le s (C q.1) R (B q.1) (τ q.1) (t q.1) hhi hP hb₁0 hb₂0).trans hsource
  have hcommon:=modified_retained_seed_and_caps (liveIndices (B q.1).val)
    (child s (C q.1) R (B q.1) (τ q.1) (t q.1)) (f.modifier q.1) (R*C q.1) (seed q.1)
    (hseed q.1) hz₁ hz₂ (K q.1) (Tsec q.1) Z ξ (hK q.1) q.2.val
  have hNC:(d.C.absNorm:ℝ)≤Z^(2:ℝ):=hcommon.2.2.1.trans hcsource
  have hND:(d.D.absNorm:ℝ)≤Z^(2:ℝ):=hcommon.2.2.2.trans hcsource
  have hcols:∀I∈finiteColumns (Fintype.piFinset d.input.pools),(I.absNorm:ℝ)≤Z^(4:ℝ):=
    child_full_column_cap s (C q.1) R (B q.1) (τ q.1) (t q.1) (Z^(4:ℝ)) hfull
  have hsector:∀I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools)),
      ((I:Ideal O).absNorm:ℝ)≤Z^(4:ℝ):=sector_full_pool_cap _ d.D d.hD.1 _ hcols
  have hrad:=f.retainedRadial_gates Q (fun q=>Lref/((C q.1).absNorm:ℝ)) q
  have hraw:=child_reference_raw_lower s (C q.1) R (hC q.1) (B q.1) (τ q.1) (t q.1) Lref
    hLref hX₁ hX₂ hY₁ hY₂
  refine ⟨hW₁,hW₂,hs₁,hs₂,(fun i=>hP i.val),hrad.1,hrad.2.1,hrad.2.2.1,
    hrad.2.2.2.1,hrad.2.2.2.2,hchar q.1,?_,?_,hfixed,hraw.1,hraw.2.1,hraw.2.2.1,hraw.2.2.2.1,hraw.2.2.2.2,?_,hsector⟩
  · exact frequency_cap_four d.C d.D d.hC d.hD d.sameSupport d.inactive Z (zero_lt_one.trans hZ) hNC
  · have hh:=retained_scale_cap d.C d.D d.hC d.inactive d.radius Z 3 hZ.le (by norm_num) (hradius q.1) hfour
    convert hh using 1 <;> first | rfl | norm_num
  · intro X hX L hL hLsf alloc
    intro _halloc
    have hX0:X≠0:=by rcases hX with rfl|rfl; exact d.hC.1; exact d.hD.1
    have hXcap:(X.absNorm:ℝ)≤Z^(2:ℝ):=by rcases hX with rfl|rfl; exact hNC; exact hND
    have hLcap: (L.absNorm:ℝ)≤Z^(4:ℝ):=
      (divisorPool_nonzero_norm Finset.univ
        (fun I:sectorPool d.D d.hD.1 (finiteColumns (Fintype.piFinset d.input.pools))=>(I:Ideal O))
        (fun I _=>(sectorPool_supported d.D d.hD.1 _ I).1) (Z^(4:ℝ)) (fun I _=>hsector I) L hL).2
    exact first_child_allocation_caps s (C q.1) R (hC q.1) hR (B q.1) (τ q.1) (t q.1) W₁ W₂
      b Z amp ell mesh loss Bsource depth hZ hb (hCcap q.1) hRcap hW₁ hW₂ hb₁ hb₂ hplain
      P hpool hdepth havoid X L hX0 hXcap hLsf hLcap alloc
end Family
end
end QRH.Record1252270103Source.Contraction.SelectedMainExceptional
#print axioms QRH.Record1252270103Source.Contraction.SelectedMainExceptional.mainAllocatedFamily_polynomialCaps
