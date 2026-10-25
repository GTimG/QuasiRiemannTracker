/- Copyright (c) 2026 Sil. Apache-2.0.
The exact artificial Moebius-divisor sum of the actual outer pair.
The physical fixedPool retains the original supplier seed and is never
replaced by a guessed pool or by a cardinality estimate.

-/
import Candidate.SilPrior.FourthPower.OuterFreshActualAllocationPair
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.MobiusHarmonicMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshArtificialSum
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentSourceRow CenteredMomentSectorLocalization CenteredMomentFirstPhysicalSource
open CenteredMomentSecondHeightFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondEnergySplit
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentSecondSectorColumns
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open CenteredMomentActiveSource CenteredMomentLiveDomain CenteredMomentMobiusRegroup
open CenteredMomentWholeDivisorShell CenteredMomentMobiusHarmonicMass
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceWindow MixedFirstSourceMoment
open MixedFirstProfileEnvelope MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstActualNonexceptional MixedFirstLiveSource MixedFirstSourceGeometry
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open MixedSupplierOriginalFrequency MixedCanonicalSource ReferencePrimeEnclosure
open MixedOriginalTail MixedOriginalNormCap MixedOriginalTailCaps
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair OuterFreshRows OuterFreshNonexceptionalFamily OuterFreshStructure
open OuterFreshAllocatedWindow OuterFreshRootAdmission OuterFreshPairedAllocatedWindow
open OuterFreshAllocationMass OuterFreshActualAllocationPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The literal divisor pool in rawKernelPair at its D-independent fixed
source support. The original supplier seed remains in commonColumn. -/
def fixedDivisors (q : Data ι) (x : Frozen q)
    (r : Source (RestIndex q) a b) (seed G : Id) (hG : Supported G) : Finset Id :=
  divisorPool (Finset.univ : Finset (sectorPool G hG.1 (fixedPool q x r seed)))
    (fun I : sectorPool G hG.1 (fixedPool q x r seed)=>(I:Id))

/-- Every actual sector ideal divides an actual nonzero original column.
The bound uses its full norm, not the radical or the number of columns. -/
theorem fixed_sector_norm (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (seed G : Id) (hG : Supported G)
    (I : sectorPool G hG.1 (fixedPool (supplierData s ha u L J) x
      (residualSource s ha cover u L J x) seed)) :
    (I.val.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d := by
  let q:=supplierData s ha u L J
  let r:=residualSource s ha cover u L J x
  have hGI : G*I.val∈supportedColumns (fixedPool q x r seed) :=
    (mem_residualPool G hG.1 (supportedColumns (fixedPool q x r seed)) I.val).mp
      (Finset.mem_filter.mp I.property).1
  have hcol : commonColumn q x seed (G*I.val)≠0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hGI).1).2
  have hcoeff:=common_coefficient q x r ha (residual_matches s ha cover u L J x) seed (G*I.val)
  rw [hcoeff] at hcol
  have hbound:=original_coefficient_cap r ha seed (G*I.val) (mul_ne_zero_iff.mp hcol).2
  exact ((CenteredExceptionalCount.norm_le_of_dvd hbound.1
    (dvd_mul_left I.val G)).trans hbound.2).trans (residual_norm_cap s ha cover u L J x)

set_option maxHeartbeats 600000 in
theorem fixed_divisor_norm (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (seed G : Id) (hG : Supported G) (D : Id)
    (hD : D∈fixedDivisors (supplierData s ha u L J) x
      (residualSource s ha cover u L J x) seed G hG) :
    D≠0 ∧ (D.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d := by
  let S := fixedPool (supplierData s ha u L J) x
    (residualSource s ha cover u L J x) seed
  exact divisorPool_nonzero_norm (Finset.univ : Finset (sectorPool G hG.1 S))
    (fun I : sectorPool G hG.1 S => I.val)
    (fun I _=>(sectorPool_supported G hG.1 S I).1)
    (sourceNormCap s.P b s.T s.d)
    (fun I _=>fixed_sector_norm s ha cover u L J x seed G hG I) D hD

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 800000 in
/-- Complete summation over the ACTUAL artificial divisors at a fixed
common label, unit subset and physical Fourier window. The actual analytic
pair theorem is called internally; the actual full divisor norms are derived
from the original canonical source. No bound for a pair, energy or divisor
mass is an input. Only the displayed numerical root/gate admissions remain.

Both genuine common norms and the original prefix stay on the right. The
whole Moebius sum costs only Z^epsilonArt, with no divisor cardinality loss. -/
theorem uniform_actual_artificial_sum
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ epsilonArt : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤Bwindow)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : Bwindow≤Lcap)
    (hslots : (N:ℝ)*Lslot+1≤Bwindow) (hCap : 2≤Cap)
    (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBdecl : 0≤Bdecl)
    (hdeclWindow : Bdecl+1≤Bwindow)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hseedExp : commonExponent Lorig (N:ℝ) Lslot≤Bseed)
    (hε : 0<ε) (hrho : 0<rho) (hδ : 0<δ) (hArt : 0<epsilonArt)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep Bwindow Bseed ε rho
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∃Cg Ca : ℝ,0<Cg ∧ 0<Ca ∧
    ∀η₀ : Character,Q≤η₀.modulus→
    ∃Cw : ℝ,0<Cw ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s→
      (∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀cover : OriginalEnclosure s,∀u : Id,∀L : Finset ι,∀J : Finset {i // i∉Lᶜ},
    let q:=supplierData s ha u L J
    ∀x : Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0→
    ∀seed : Id,Squarefree seed→u=frozenProduct q x*seed→
    ∀p : FixedLabel (fixedPool q x (residualSource s ha cover u L J x) seed),
    ∀(hC : Supported p.val.1)(hE : Supported p.val.2),
    ∀(τ : Character)(ξ χ₀ : RayCharacter)(U : Finset (CommonIndex p.val.1 p.val.2))
      (ψ : RayCharacter→Character),
      SharpFamily τ (frozenProduct q x) ξ p.val.1 p.val.2 hC hE U ψ→
    ∀(Rfreq : ℝ)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),0<K→∀n : Fin 4→ℤ,
    ∀y₀ : Selected q,
      physicalBlock τ tp (fixedPool q x (residualSource s ha cover u L J x) seed)
        (outerColumn q x y₀ seed ξ) p.val.1 p.val.2 hC hE U Rfreq
        (outerRows false q x y₀ τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K n≠0→
    ∀Rdecl : ℝ,physicalWidth τ (frozenProduct q x) p.val.1 p.val.2 U Rfreq Z≤Rdecl→
      Rdecl≤Bdecl→
    let r:=unavoidedResidual s ha cover u L J x
    let ra:=residualSource s ha cover u L J x
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    (∀G : Id,G=p.val.1 ∨ G=p.val.2→∀B : actualAllocations (tuplePools r) G,
      frozenCoefficient B.val G r.R r.ν r.Wslot r.P≠0→
      Real.logb Z (s.T/pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))+
        2*(∑i : liveIndices B.val,w i.val.val.val)+4*d≤Rdecl-rho ∧
        (3/4:ℝ)*(∑i : liveIndices B.val,w i.val.val.val)<d)→
    ∀(χleft χright : RayCharacter)(Xleft Xright θwin : ℝ),0<Xleft→0<Xright→
    let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
      (sourceRows p.val.1 p.val.2 U Rfreq)) n
    let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
    let EL:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
      logAnnulus_smooth t₀ tp V θwin Z Rdecl ε
    let ER:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
      logAnnulus_smooth t₀ tp V (-θwin) Z Rdecl ε
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*
      (∑D∈fixedDivisors q x ra seed p.val.2 hE,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*
        pairedWindowMass q rows keep
          (fun F z=>residualWindow false ra ha p.val.1 hC seed D F (ψ χleft) tp θwin Xleft z)
          (fun F z=>residualWindow true ra ha p.val.2 hE seed D F (ψ χright) tp θwin Xright (-z)))≤
      (Ca*Z^epsilonArt)*
        Real.sqrt ((Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
          (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))*
          Real.sqrt (EL*ER) := by
  dsimp only
  obtain ⟨degree,control,Cg,hCg,hpair⟩ := uniform_actual_residual_pair (ι:=ι) M Hray hHray
    N Holes hcard Wslot a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ
    hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBdecl hdeclWindow hβ hKslot hBseed hε hrho hδ Q hQt hQ72 hQM
  obtain ⟨Ca,hCa,hart⟩ := full_mass_subpower Bseed epsilonArt hBseed hArt
  have hnorm := eventually_source_caps N b Lorig ((N:ℝ)*Lslot) 1 (by norm_num)
  refine ⟨degree,control,Cg,Ca,hCg,hCa,?_⟩
  intro η₀ hη₀
  obtain ⟨Cw,hCw,hpair⟩ := hpair η₀ hη₀
  refine ⟨Cw,hCw,?_⟩
  filter_upwards [hpair,hart,hnorm] with Z hpairZ hartZ hnormZ
  have hZ:=hpairZ.1
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap hgates
    χleft χright Xleft Xright θwin hXL hXR
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let ra:=residualSource s ha cover u L J x
  let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
    (sourceRows p.val.1 p.val.2 U Rfreq)) n
  let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
  let A:=Z^(budgetStep Bwindow Bseed ε rho)*‖normalization (r.X₁*r.X₂) r.P‖^2
  let EL:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
    logAnnulus_smooth t₀ tp V θwin Z Rdecl ε
  let ER:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
    logAnnulus_smooth t₀ tp V (-θwin) Z Rdecl ε
  let B:=Real.sqrt ((Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
    (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))*Real.sqrt (EL*ER)
  let Ds:=fixedDivisors q x ra seed p.val.2 hE
  let pair:=fun D:Id=>pairedWindowMass q rows keep
    (fun F z=>residualWindow false ra ha p.val.1 hC seed D F (ψ χleft) tp θwin Xleft z)
    (fun F z=>residualWindow true ra ha p.val.2 hE seed D F (ψ χright) tp θwin Xright (-z))
  have hB0:0≤B:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hproduct := (canonical_product M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀
    s hcanonical N Lslot ((N:ℝ)*Lslot) hZ hcard hLslot hw hwL le_rfl).2.2
  have hnormCap:sourceNormCap s.P b s.T s.d≤Z^(commonExponent Lorig (N:ℝ) Lslot) := by
    simpa only [commonExponent] using
      (hnormZ.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hproduct).2
  have hDs (D:Id) (hD:D∈Ds) : (D.absNorm:ℝ)≤Z^Bseed :=
    ((fixed_divisor_norm s ha cover u L J x seed p.val.2 hE D hD).2.trans hnormCap).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hseedExp)
  have hsource:=hpairZ.2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx
    seed hseed hu p hC hE τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap hgates
  have hpoint (D:Id) (hD:D∈Ds) :
      ‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*(A*pair D)≤
        B*(‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ)) := by
    by_cases hμ:(UniqueFactorizationMonoid.moebius D:ℂ)=0
    · simp only [hμ,norm_zero,zero_mul,zero_div,mul_zero,le_refl]
    have hd:Squarefree D:=squarefree_of_moebius_ne_zero D hμ
    have he:A*pair D≤B/(D.absNorm:ℝ):=
      hsource D hd (hDs D hD) χleft χright Xleft Xright θwin hXL hXR
    exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (by ring)
  have hmass:(∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ))≤Ca*Z^epsilonArt :=
    hartZ.2 Ds (fun D hD _=>hDs D hD)
  change A*(∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*pair D)≤_
  calc
    _=∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖*(A*pair D) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤∑D∈Ds,B*(‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ)) :=
      Finset.sum_le_sum hpoint
    _=B*(∑D∈Ds,‖(UniqueFactorizationMonoid.moebius D:ℂ)‖/(D.absNorm:ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _≤B*(Ca*Z^epsilonArt):=mul_le_mul_of_nonneg_left hmass hB0
    _=_ := by dsimp only [B];ring

end
end Candidate.SilPrior.FourthPower.OuterFreshArtificialSum
