/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original nonexceptional physical block after selected averaging,
both genuine allocation sums, the artificial divisor sum, and Fourier/ray
integration. The same original common label, unit subset and dyadic index
remain explicit.
-/
import Candidate.SilPrior.FourthPower.OuterFreshSelectedKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalBlock
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
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar CenteredMomentSecondEnergySplit
open CenteredMomentFirstSectors
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceWindow MixedFirstSourceMoment
open MixedFirstProfileEnvelope MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstActualNonexceptional MixedFirstLiveSource MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedCanonicalSource ReferencePrimeEnclosure
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair OuterFreshRows OuterFreshNonexceptionalFamily OuterFreshStructure
open OuterFreshBlock
open OuterFreshAllocatedWindow OuterFreshRootAdmission OuterFreshPairedAllocatedWindow
open OuterFreshAllocationMass OuterFreshActualAllocationPair OuterFreshArtificialSum
open OuterFreshFixedWindows OuterFreshWeightedKernel OuterFreshSelectedKernel
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The actual original selected average, with its genuine selected scale.
The common height coefficient is retained separately by the main theorem. -/
def physicalAverage (q:Data ι)(x:Frozen q)(r:Source (RestIndex q) a b)
    (seed:Id)(τ:Character)(ξ χ₀:RayCharacter)(Q C E:Id)
    (hC:Supported C)(hE:Supported E)(U:Finset (CommonIndex C E))
    (t R:ℝ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ) : ℂ :=
  ∑y∈activeSelected q,((selectedPositiveWeight q x y τ/MixedSelectedVolume.scale q:ℝ):ℂ)*
    physicalBlock τ t (fixedPool q x r seed) (outerColumn q x y seed ξ)
      C E hC hE U R (outerRows false q x y τ ξ χ₀ Q C E U R) Φ K n

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 1000000 in
/-- Complete actual block estimate. There is no pair/window/kernel energy
premise. A zero selected average is handled exactly. Otherwise it supplies
one real nonzero selected physical block for the uniform sharp caps.
The actual Fourier kernel is then applied to the entire weighted family,
without a selected cardinality factor. The original outerScalar, normalizer,
common height, source normalization and selected scale all remain visible. -/
theorem uniform_actual_nonexceptional_block
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
    ∀(Φ:𝓢(ℝ,ℂ))(decay:ℕ),∃Ckernel:ℝ,0≤Ckernel ∧
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
    ∀(Rfreq K:ℝ),0<K→∀n : Fin 4→ℤ,
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
    let H:=heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2)
    let B:= (Ca*Z^epsilonArt)*
      Real.sqrt ((Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
        (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))*
      angleEnvelope r Cw Kslot N degree control t₀ tp V Z Rdecl ε
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*(1+kernelScale n)^decay*
      ‖H*physicalAverage q x ra seed τ ξ χ₀ Q p.val.1 p.val.2 hC hE U tp Rfreq Φ K n‖≤
      outerScalar p.val.1 p.val.2 K n*normalizer p.val.1 p.val.2 U*(‖H‖*Ckernel*B) := by
  dsimp only
  obtain ⟨degree,control,Cg,Ca,hCg,hCa,hsource⟩:=uniform_actual_artificial_sum (ι:=ι) M Hray hHray
    N Holes hcard Wslot a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ epsilonArt
    hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc hBR0 hBH hBdecl
    hdeclWindow hβ hKslot hBseed hseedExp hε hrho hδ hArt Q hQt hQ72 hQM
  refine ⟨degree,control,Cg,Ca,hCg,hCa,?_⟩
  intro Φ decay
  obtain ⟨Ckernel,hCkernel,hkernel⟩:=weighted_normalized_block Φ decay (2*degree)
  refine ⟨Ckernel,hCkernel,?_⟩
  intro η₀ hη₀
  obtain ⟨Cw,hCw,hsource⟩:=hsource η₀ hη₀
  refine ⟨Cw,hCw,?_⟩
  filter_upwards [hsource] with Z hsourceZ
  have hZ:=hsourceZ.1
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq K hK n Rdecl hpaid hcap hgates
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let ra:=residualSource s ha cover u L J x
  let S:=fixedPool q x ra seed
  let H:=heightCoeff τ tp p.val.1*star (heightCoeff τ tp p.val.2)
  let A:=Z^(budgetStep Bwindow Bseed ε rho)*‖normalization (r.X₁*r.X₂) r.P‖^2
  let commonBudget:=Real.sqrt ((Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
    (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))
  let B:=(Ca*Z^epsilonArt)*commonBudget*angleEnvelope r Cw Kslot N degree control t₀ tp V Z Rdecl ε
  let P:=physicalAverage q x ra seed τ ξ χ₀ Q p.val.1 p.val.2 hC hE U tp Rfreq Φ K n
  let pref:=outerScalar p.val.1 p.val.2 K n*normalizer p.val.1 p.val.2 U
  have hA:0≤A:=mul_nonneg (Real.rpow_nonneg hZ0.le _) (sq_nonneg _)
  have hangle:=angleEnvelope_nonneg r Cw Kslot N degree control t₀ tp V Z Rdecl ε
    hCw.le (zero_le_one.trans hKslot) hV hZ0.le
  have hB0:0≤B:=mul_nonneg (mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg hZ0.le _))
    (Real.sqrt_nonneg _)) hangle
  have houter:0≤outerScalar p.val.1 p.val.2 K n:=by unfold outerScalar;positivity
  have hnormalizer:0≤normalizer p.val.1 p.val.2 U:=(normalizer_pos _ _ hC U).le
  have hpref:0≤pref:=mul_nonneg houter hnormalizer
  change A*(1+kernelScale n)^decay*‖H*P‖≤pref*(‖H‖*Ckernel*B)
  by_cases hzero:P=0
  · rw [hzero,mul_zero,norm_zero,mul_zero]
    exact mul_nonneg hpref (mul_nonneg (mul_nonneg (norm_nonneg _) hCkernel) hB0)
  have hnonzero:
      (∑y∈activeSelected q,((selectedPositiveWeight q x y τ/MixedSelectedVolume.scale q:ℝ):ℂ)*
        physicalBlock τ tp S (outerColumn q x y seed ξ) p.val.1 p.val.2 hC hE U Rfreq
          (outerRows false q x y τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K n)≠0:=hzero
  obtain ⟨y₀,hy₀,hterm⟩:=Finset.exists_ne_zero_of_sum_ne_zero hnonzero
  have hne:=right_ne_zero_of_mul hterm
  have hCE:CompletedGauss.primeSupport p.val.1=CompletedGauss.primeSupport p.val.2:=
    (commonLabels_data _ _ _ _ p.property).2.2
  have hqP:∀i,0<q.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hscale:=MixedSelectedVolume.scale_pos q hqP
  let weight:=fun y:Selected q=>selectedPositiveWeight q x y τ/MixedSelectedVolume.scale q
  let rows:=fun y:Selected q=>dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
    (outerRows false q x y τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq)) n
  have hwgt (y:Selected q):0≤weight y:=div_nonneg (selected_positive_nonneg q x y τ) hscale.le
  have hart:=hsourceZ.2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p hC hE
    τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap hgates
  have hraw (χ ρ:RayCharacter)(angle:ℝ):
      A*rawAverage q x ra seed τ ξ χ₀ χ ρ Q p.val.1 p.val.2 hC hE U tp angle
        (dyadicScale (n 2)) (dyadicScale (n 3)) Rfreq n≤B*(1+‖angle‖)^(2*degree) := by
    have hg:=selected_raw_pair_le q x hqP ra ha (residual_matches s ha cover u L J x)
      seed τ ξ χ₀ χ ρ Q p.val.1 p.val.2 hC hE U ψ hψ tp angle
      (dyadicScale (n 2)) (dyadicScale (n 3)) Rfreq n
    have hp:=hart χ (ρ⁻¹) (dyadicScale (n 2)) (dyadicScale (n 3)) angle
      (dyadicScale_pos _) (dyadicScale_pos _)
    have he:=(mul_le_mul_of_nonneg_left hg hA).trans hp
    have hang:=paired_envelope_polynomial r Cw Kslot N degree control t₀ tp V angle Z Rdecl ε
      hCw.le (zero_le_one.trans hKslot) hV hZ0.le
    have hfactor:0≤(Ca*Z^epsilonArt)*commonBudget:=
      mul_nonneg (mul_nonneg hCa.le (Real.rpow_nonneg hZ0.le _)) (Real.sqrt_nonneg _)
    exact he.trans ((mul_le_mul_of_nonneg_left hang hfactor).trans_eq (by dsimp only [B];ring))
  have hrawFamily (χ ρ:RayCharacter)(angle:ℝ):
      (∑y∈activeSelected q,(A*weight y)*rawKernelPair τ tp S (outerColumn q x y seed ξ)
        p.val.1 p.val.2 hC hE U χ ρ angle (dyadicScale (n 2)) (dyadicScale (n 3)) (rows y))≤
      B*(1+‖angle‖)^(2*degree) := by
    simpa only [rawAverage,weight,rows,Finset.mul_sum,mul_assoc] using hraw χ ρ angle
  have hk:=hkernel (activeSelected q) (fun y=>A*weight y) rows
    (fun y=>mul_nonneg hA (hwgt y)) τ tp S (fun y=>outerColumn q x y seed ξ)
    p.val.1 p.val.2 hC hE hCE U Rfreq K n B hB0 hrawFamily
  let Nsum:=∑y∈activeSelected q,((A*weight y:ℝ):ℂ)*
    normalizedBlock τ tp S (outerColumn q x y seed ξ) p.val.1 p.val.2 hC hE U Rfreq (rows y) Φ K n
  have hblock (y:Selected q):
      physicalBlock τ tp S (outerColumn q x y seed ξ) p.val.1 p.val.2 hC hE U Rfreq
        (outerRows false q x y τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K n=
      (pref:ℂ)*normalizedBlock τ tp S (outerColumn q x y seed ξ)
        p.val.1 p.val.2 hC hE U Rfreq (rows y) Φ K n := by
    rw [physicalBlock_live_dyadic_rows,
      physicalBlock_eq τ tp S (outerColumn q x y seed ξ) p.val.1 p.val.2 hC hE U Rfreq
        (rows y) (fun z hz=>dyadicRows_nonzero _ n z hz) Φ K hK n]
    simp only [pref,Complex.ofReal_mul,mul_assoc]
  have hcomplex:(A:ℂ)*P=(pref:ℂ)*Nsum := by
    change (A:ℂ)*(∑y∈activeSelected q,(weight y:ℂ)*
      physicalBlock τ tp S (outerColumn q x y seed ξ) p.val.1 p.val.2 hC hE U Rfreq
        (outerRows false q x y τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K n)=_
    simp_rw [hblock]
    dsimp only [Nsum]
    simp only [Finset.mul_sum,Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [weight]
    ring
  have hnorm:A*‖P‖=pref*‖Nsum‖:=by
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hA,Real.norm_of_nonneg hpref]
      using congrArg norm hcomplex
  calc
    _=(‖H‖*(1+kernelScale n)^decay)*(A*‖P‖):=by rw [norm_mul];ring
    _=(pref*‖H‖)*((1+kernelScale n)^decay*‖Nsum‖):=by rw [hnorm];ring
    _≤(pref*‖H‖)*(Ckernel*B):=mul_le_mul_of_nonneg_left hk (mul_nonneg hpref (norm_nonneg _))
    _=_:=by ring

end
end Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalBlock
