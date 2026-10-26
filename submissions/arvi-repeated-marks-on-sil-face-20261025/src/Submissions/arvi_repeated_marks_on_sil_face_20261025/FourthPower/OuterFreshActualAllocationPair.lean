/- Copyright (c) 2026 Sil. Apache-2.0.
Actual residual-window estimate after BOTH genuine allocation sums.
The two analytic window applications and the zero-allocation branches are
discharged internally. Only original numerical capacity/support gates remain.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshAllocationMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshActualAllocationPair
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
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredExceptionalProfile
open CenteredMomentUncenteredTerminal CenteredMomentSecondEnergySplit CenteredMomentCanonicalFirst
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceWindow MixedFirstSourceMoment
open MixedFirstProfileEnvelope MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstActualNonexceptional MixedFirstLiveSource
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open MixedSupplierOriginalFrequency MixedCanonicalSource ReferencePrimeEnclosure
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair OuterFreshRows OuterFreshNonexceptionalFamily OuterFreshStructure
open OuterFreshAllocatedWindow OuterFreshRootAdmission OuterFreshPairedAllocatedWindow
open OuterFreshAllocationMass
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

private theorem envelope_nonneg {α : Type*} [Fintype α]
    (r : Source α a b) (C Kslot : ℝ) (N degree : ℕ)
    (control : Finset (ℕ×ℕ)) (t₀ tp V θ Z Rdecl ε : ℝ)
    (hC : 0≤C) (hKslot : 0≤Kslot) (hV : 0≤V) (hZ : 0≤Z) :
    0≤windowEnvelope r C Kslot N degree control logAnnulus
      logAnnulus_compact logAnnulus_smooth t₀ tp V θ Z Rdecl ε := by
  have hheight : 0≤height t₀ V r.t₁ r.t₂ := by unfold height;positivity
  have hwindow := (heightCost_pos tp θ).le
  have hfixed := fixedPresentationCost_pos.le
  unfold windowEnvelope
  positivity

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 800000 in
/-- One actual common label and its original nonexceptional row partition.
Both genuine allocation sets have been summed. No individual or whole energy
estimate is a premise. The two numerical gates are requested only when the
corresponding canonical frozen coefficient is nonzero, as supplied by the
original RootAdmission theorem. The actual zero branches are proved here.

The constants and the event precede every source, common label, allocation,
sharp character, selected product and Fourier angle. The original residual
normalization and the full artificial divisor norm are retained exactly. -/
theorem uniform_actual_residual_pair
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho δ : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤Bwindow)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : Bwindow≤Lcap)
    (hslots : (N:ℝ)*Lslot+1≤Bwindow) (hCap : 2≤Cap)
    (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBdecl : 0≤Bdecl)
    (hdeclWindow : Bdecl+1≤Bwindow)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho) (hδ : 0<δ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep Bwindow Bseed ε rho
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∃Cg : ℝ,0<Cg ∧
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
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    ∀(χleft χright : RayCharacter)(Xleft Xright θwin : ℝ),0<Xleft→0<Xright→
    let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
      (sourceRows p.val.1 p.val.2 U Rfreq)) n
    let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
    let EL:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
      logAnnulus_smooth t₀ tp V θwin Z Rdecl ε
    let ER:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
      logAnnulus_smooth t₀ tp V (-θwin) Z Rdecl ε
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*
      pairedWindowMass q rows keep
        (fun F z=>residualWindow false ra ha p.val.1 hC seed D F (ψ χleft) tp θwin Xleft z)
        (fun F z=>residualWindow true ra ha p.val.2 hE seed D F (ψ χright) tp θwin Xright (-z))≤
      Real.sqrt ((Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
        (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))))*
        Real.sqrt (EL*ER)/(D.absNorm:ℝ) := by
  dsimp only
  obtain ⟨degree,control,hpair⟩ := uniform_actual_paired_allocated_window (ι:=ι) M Hray hHray
    logAnnulus logAnnulus_compact logAnnulus_smooth N Holes hcard Wslot
    a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho
    hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBdecl hdeclWindow hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  obtain ⟨Cg,hCg,hcore⟩ := uniform_pair_core_mass N δ hδ
  refine ⟨degree,control,Cg,hCg,?_⟩
  intro η₀ hη₀
  obtain ⟨Cw,hCw,hpair⟩ := hpair η₀ hη₀
  refine ⟨Cw,hCw,?_⟩
  filter_upwards [hpair] with Z hpairZ
  have hZ:=hpairZ.1
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap hgates
    D hD hDcap χleft χright Xleft Xright θwin hXL hXR
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let ra:=residualSource s ha cover u L J x
  let A₁:=actualAllocations (tuplePools r) p.val.1
  let A₂:=actualAllocations (tuplePools r) p.val.2
  let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
    (sourceRows p.val.1 p.val.2 U Rfreq)) n
  let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
  let A:=Z^(budgetStep Bwindow Bseed ε rho)*‖normalization (r.X₁*r.X₂) r.P‖^2
  let EL:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
    logAnnulus_smooth t₀ tp V θwin Z Rdecl ε
  let ER:=windowEnvelope r Cw Kslot N degree control logAnnulus logAnnulus_compact
    logAnnulus_smooth t₀ tp V (-θwin) Z Rdecl ε
  let cL:=fun B : A₁=>OuterFreshAllocationMass.scalar ra p.val.1 B
  let cR:=fun B : A₂=>OuterFreshAllocationMass.scalar ra p.val.2 B
  let fL:=fun (B : A₁)(F : Id)(z : O)=>
    windowedPolynomial (allocatedLiveSource ra (zero_le_one.trans hb) cover p.val.1 B)
      ha D F (ψ χleft) fixedBadMask 1 tp logAnnulus Xleft θwin z
  let fR:=fun (B : A₂)(F : Id)(z : O)=>
    windowedPolynomial (allocatedLiveSource ra (zero_le_one.trans hb) cover p.val.2 B)
      ha D F (ψ χright) fixedBadMask 1 tp logAnnulus Xright (-θwin) (-z)
  let costL:=fun B : A₁=>allocationWindowCost r p.val.1 B Cw Kslot N degree control
    logAnnulus logAnnulus_compact logAnnulus_smooth t₀ tp V θwin Z Rdecl ε D
  let costR:=fun B : A₂=>allocationWindowCost r p.val.2 B Cw Kslot N degree control
    logAnnulus logAnnulus_compact logAnnulus_smooth t₀ tp V (-θwin) Z Rdecl ε D
  have hA:0≤A:=mul_nonneg (Real.rpow_nonneg hZ0.le _) (sq_nonneg _)
  have hEL:0≤EL:=envelope_nonneg r Cw Kslot N degree control t₀ tp V θwin Z Rdecl ε
    hCw.le (zero_le_one.trans hKslot) hV hZ0.le
  have hER:0≤ER:=envelope_nonneg r Cw Kslot N degree control t₀ tp V (-θwin) Z Rdecl ε
    hCw.le (zero_le_one.trans hKslot) hV hZ0.le
  have hDN:0<(D.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)
  have hpairSource:=hpairZ.2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx
    seed hseed hu p hC hE τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap
  have hpairB (B₁ : A₁) (B₂ : A₂) :
      A*‖cL B₁‖*‖cR B₂‖*pairedWindowMass q rows keep (fL B₁) (fR B₂)≤
        Real.sqrt (costL B₁*costR B₂) := by
    by_cases hz₁:frozenCoefficient B₁.val p.val.1 r.R r.ν r.Wslot r.P=0
    · have hc: cL B₁=0:=actual_scalar_zero_of_canonical s ha cover u p.val.1 L J x B₁ hz₁
      simp only [hc,norm_zero,mul_zero,zero_mul]
      exact Real.sqrt_nonneg _
    by_cases hz₂:frozenCoefficient B₂.val p.val.2 r.R r.ν r.Wslot r.P=0
    · have hc: cR B₂=0:=actual_scalar_zero_of_canonical s ha cover u p.val.2 L J x B₂ hz₂
      simp only [hc,norm_zero,mul_zero,zero_mul]
      exact Real.sqrt_nonneg _
    obtain ⟨hmixedL,hnativeL⟩:=hgates p.val.1 (Or.inl rfl) B₁ hz₁
    obtain ⟨hmixedR,hnativeR⟩:=hgates p.val.2 (Or.inr rfl) B₂ hz₂
    exact hpairSource B₁ B₂ hmixedL hnativeL hmixedR hnativeR
      D hD hDcap χleft χright Xleft Xright θwin hXL hXR
  have hseedCE:=fixed_label_seed s ha cover u L J x seed hseed p
  have hqP:∀i,0<q.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have htriangle:=residual_pair_le_allocations q hqP ra ha (zero_le_one.trans hb) cover
    p.val.1 p.val.2 seed D hC hE hseedCE.1 hseedCE.2
    (ψ χleft) (ψ χright) tp θwin Xleft Xright rows keep
  have hscalar:0≤Real.sqrt (EL*ER)/(D.absNorm:ℝ):=
    div_nonneg (Real.sqrt_nonneg _) hDN.le
  let coreMass:=∑B₁ : A₁,∑B₂ : A₂,
    Real.sqrt (OuterFreshAllocationMass.core r p.val.1 B₁*OuterFreshAllocationMass.core r p.val.2 B₂)
  have hcardr:Fintype.card (RestIndex q)≤N:=(rest_card_le q).trans hcard
  have hcoreBound:=hcore hcardr a b r p.val.1 p.val.2 hC.1 hE.1
  have hcoreNonneg:0≤coreMass:=Finset.sum_nonneg (fun _ _=>
    Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
  have hBoundNonneg:0≤
      (Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
        (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ))) := by
    apply mul_nonneg
    all_goals
      exact mul_nonneg (mul_nonneg hCg.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (div_nonneg (rootFactor_nonneg r) (Nat.cast_nonneg _))
  have hcoreSqrt:coreMass≤Real.sqrt (
      (Cg*(p.val.1.absNorm:ℝ)^δ*(rootFactor r/(p.val.1.absNorm:ℝ)))*
        (Cg*(p.val.2.absNorm:ℝ)^δ*(rootFactor r/(p.val.2.absNorm:ℝ)))) :=
    (Real.le_sqrt hcoreNonneg hBoundNonneg).mpr hcoreBound
  have hcostFactor:(∑B₁ : A₁,∑B₂ : A₂,Real.sqrt (costL B₁*costR B₂))=
      coreMass*Real.sqrt (EL*ER)/(D.absNorm:ℝ) := by
    dsimp only [costL,costR]
    simp_rw [allocationWindowCost_factored]
    exact pair_cost_factor r p.val.1 p.val.2 EL ER (D.absNorm:ℝ) hEL hER hDN
  change A*pairedWindowMass q rows keep
      (fun F z=>residualWindow false ra ha p.val.1 hC seed D F (ψ χleft) tp θwin Xleft z)
      (fun F z=>residualWindow true ra ha p.val.2 hE seed D F (ψ χright) tp θwin Xright (-z))≤_
  calc
    _≤A*(∑B₁ : A₁,∑B₂ : A₂,
        ‖cL B₁‖*‖cR B₂‖*pairedWindowMass q rows keep (fL B₁) (fR B₂)) :=
      mul_le_mul_of_nonneg_left htriangle hA
    _=∑B₁ : A₁,∑B₂ : A₂,
        A*‖cL B₁‖*‖cR B₂‖*pairedWindowMass q rows keep (fL B₁) (fR B₂) := by
      simp only [Finset.mul_sum,mul_assoc]
    _≤∑B₁ : A₁,∑B₂ : A₂,Real.sqrt (costL B₁*costR B₂) :=
      Finset.sum_le_sum (fun B₁ _=>Finset.sum_le_sum (fun B₂ _=>hpairB B₁ B₂))
    _=coreMass*Real.sqrt (EL*ER)/(D.absNorm:ℝ) := hcostFactor
    _≤_ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hcoreSqrt hscalar

end
end Candidate.FourthPower.OuterFreshActualAllocationPair
