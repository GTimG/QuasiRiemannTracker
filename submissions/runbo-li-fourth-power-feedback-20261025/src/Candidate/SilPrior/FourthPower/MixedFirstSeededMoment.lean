/- Copyright (c) 2026 Sil. Apache-2.0.
Full seed and ordinary-prefix reconstruction of the actual selected
moment. The finite seed allocation is paid once, after applying the
uniform centered-source theorem to every literal rebased live source.

-/
import Candidate.SilPrior.FourthPower.MixedFirstCenteredSourceMoment
import Candidate.SilPrior.FourthPower.MixedFirstSeededEnergy
import Candidate.SilPrior.FourthPower.MixedFirstCanonicalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstSeededMoment
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT ActualEisensteinCubic RayFourExpansion
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentDivisorAllocation
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyCapacityRemoval
open CenteredMomentFiniteProfileExceptional CenteredMomentAbsoluteEnergy
open CenteredMomentSourceRow CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstPhysicalApplication MixedLiveNormalization
open MixedFirstSeededSource MixedFirstSeededEnergy MixedFirstLiveSource MixedFirstRebase
open MixedFirstCanonicalGeometry MixedFirstReferenceDispatch MixedFirstProfileEnvelope
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedFixedSupport
open MixedSupplierSource MixedSupplierFourthRow MixedSupplierPositive
open MixedFirstGeometricCaps MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstSourceMoment MixedFirstCenteredSourceMoment
open MixedCanonicalSource ReferencePrimeEnclosure MixedFirstActualNonexceptional
open MixedFirstReferenceChoice MixedFirstCutoffs
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The original seed, prefix, selected weights and F-dependent keep.
The source-volume denominator is the original one, not a live volume. -/
def seededGroupedMoment {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (D : Id) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    selectedEnergy s ha D F.val η fixedBadMask 1 tp (keep F.val) Φ K)/sourceVolume s

/-- For the original, unallocated tuple the stored enclosure is already
at the original ordinary prefixes. No new support assertion is needed. -/
theorem original_enclosure (s : Source ι a b) (hB : s.B=fun _=>1) :
    OriginalEnclosure s := by
  intro I hI hlen
  apply s.henclose I hI
  simpa only [hB,mul_one] using hlen

/-- All four original lengths shorten by actual nonzero full norms. -/
theorem seeded_four_scales_le (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (D : Id) (hD : D≠0)
    (B : boundedLabels (tuplePools s) D) :
    let r:=seededRebasedSource s hb cover D hD B
    r.X₁≤s.X₁ ∧ r.X₂≤s.X₂ ∧ r.Y₁≤s.Y₁ ∧ r.Y₂≤s.Y₂ ∧ r.T≤s.T := by
  let hB := (allocation_data (tuplePools s) D B.val (Finset.mem_filter.mp B.property).1).1
  have hp₁ := ideal_norm_one_le (mul_ne_zero s.hd.1 (hB (Sum.inr 0)))
  have hp₂ := ideal_norm_one_le (mul_ne_zero s.hd.2 (hB (Sum.inr 1)))
  have hpair : 1≤pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) :=
    one_le_mul_of_one_le_of_one_le hp₁ hp₂
  change s.X₁/(s.d.1*B.val (Sum.inr 0)).absNorm≤s.X₁ ∧
    s.X₂/(s.d.2*B.val (Sum.inr 1)).absNorm≤s.X₂ ∧
    s.Y₁/(s.d.1*B.val (Sum.inr 0)).absNorm≤s.Y₁ ∧
    s.Y₂/(s.d.2*B.val (Sum.inr 1)).absNorm≤s.Y₂ ∧
    s.T/pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))≤s.T
  exact ⟨div_le_self (s.hL.trans_le s.hX₁).le hp₁,
    div_le_self (s.hL.trans_le s.hX₂).le hp₂,
    div_le_self (s.hL.trans_le s.hY₁).le hp₁,
    div_le_self (s.hL.trans_le s.hY₂).le hp₂,
    div_le_self s.total_pos.le hpair⟩

/-- Seed allocation shortens the already-prefix-adjusted ordinary
product. This is the actual P entering the outer mixed capacity ledger. -/
theorem seeded_effective_product_le (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (D : Id) (hD : D≠0)
    (B : boundedLabels (tuplePools s) D) :
    (seededRebasedSource s hb cover D hD B).T≤s.T/pairNorm s.d := by
  let hB := (allocation_data (tuplePools s) D B.val
    (Finset.mem_filter.mp B.property).1).1
  have hplain : 1≤plainNorm B.val := by
    change (1:ℝ)≤(B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm
    exact one_le_mul_of_one_le_of_one_le
      (ideal_norm_one_le (hB (Sum.inr 0)))
      (ideal_norm_one_le (hB (Sum.inr 1)))
  have hp : 0<pairNorm s.d := pairNorm_pos s.hd.1 s.hd.2
  have hden : pairNorm s.d≤
      pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) := by
    rw [extracted_pair_norm]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hplain hp.le
  change s.T/pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))≤_
  exact div_le_div_of_nonneg_left s.total_pos.le hp hden

/-- Actual mixed reserve after seed allocation, with the original
ordinary prefixes already removed in the hypothesis. -/
theorem seeded_mixed_gates (s : Source ι a b) (hb : 0≤b)
    (cover : OriginalEnclosure s) (D : Id) (hD : D≠0)
    (B : boundedLabels (tuplePools s) D) (Z R d rho : ℝ) (w : ι→ℝ)
    (hZ : 1<Z) (hw : ∀i,0≤w i)
    (hmixed : Real.logb Z (s.T/pairNorm s.d)+2*(∑i,w i)+4*d≤R-rho)
    (hnative : (3/4:ℝ)*(∑i,w i)<d) :
    let r:=seededRebasedSource s hb cover D hD B
    Real.logb Z r.T+2*(∑i : liveIndices B.val,w i.val)+4*d≤R-rho ∧
      (3/4:ℝ)*(∑i : liveIndices B.val,w i.val)<d := by
  let r:=seededRebasedSource s hb cover D hD B
  have hT := seeded_effective_product_le s hb cover D hD B
  have hP := Real.logb_le_logb_of_le hZ r.total_pos hT
  have hS : (∑i : liveIndices B.val,w i.val)≤∑i,w i := by
    simpa only [Finset.sum_coe_sort] using Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ (liveIndices B.val)) (fun i _ _=>hw i)
  constructor <;> linarith

/-- The already proved positive seed allocation, summed over the SAME
selected family and keep. Neither the count nor normalization is repeated. -/
theorem grouped_seed_allocation {α : Type v} [Fintype α]
    (q : Data α) (hP : ∀i,0<q.P i) (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (D : Id) (hD : Squarefree D)
    (η : Character) (tp : ℝ) (keep : Id→O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re) :
    seededGroupedMoment q s ha D η tp keep Φ K≤
      ((Fintype.card (Allocation D (Finset.univ : Finset (ι⊕Fin 2))):ℝ)*
        (boundedLabels (tuplePools s) D).card)*
      ∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
        ∑B : boundedLabels (tuplePools s) D,
          normalizedFrozen s D alloc B*
            groupedMoment q (seededRebasedSource s hb cover D hD.ne_zero B) ha η tp keep Φ K := by
  unfold seededGroupedMoment groupedMoment
  simp only [Finset.sum_div]
  calc
    _≤∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
      (((Fintype.card (Allocation D (Finset.univ : Finset (ι⊕Fin 2))):ℝ)*
        (boundedLabels (tuplePools s) D).card)*
      ∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
        ∑B : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc B*
          (selectedEnergy (seededRebasedSource s hb cover D hD.ne_zero B) ha 1 F.val
            η fixedBadMask 1 tp (keep F.val) Φ K/
            sourceVolume (seededRebasedSource s hb cover D hD.ne_zero B))) := by
      apply Finset.sum_le_sum
      intro F hF
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left
        (selected_energy_normalized s ha hb cover D hD F.val η fixedBadMask 1 tp
          (keep F.val) Φ K 2 hK hΦs (fun z=>hΦ _))
        (div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hP).le)
    _=_ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro alloc halloc
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro F hF
      ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 1000000 in
/-- Full actual seed and prefix reconstruction. The live analytic bound
is supplied internally. Its N(D)^step reserve pays the complete finite
seed-allocation mass; the Z^step reserve remains in the conclusion.
The original product of slot controls is explicit, and there is exactly
one reciprocal original prefix norm and one reciprocal seed norm. -/
theorem uniform_seeded_source_moment
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep B Bseed ε rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      θ w σ freq t₀ R₀ s→s.B=(fun _=>1)→(∀i,s.M i≤Kslot)→
      (s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R:=inputWidth η K Z
    let P:=Real.logb Z (s.T/pairNorm s.d)
    let S:=∑i,w i
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    Z^step*seededGroupedMoment q s ha D η tp keep Φ K≤
      C*Kslot^(2*N)*(∏i,s.M i)^2*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε/
          (pairNorm s.d*(D.absNorm:ℝ)) := by
  dsimp only
  let step:=budgetStep B Bseed ε rho
  have hstep : 0<step := budget_step_pos B Bseed ε rho (by linarith) hBseed hε hrho
  obtain ⟨Cmass,hCmass,hmass⟩ := uniform_normalized_frozen_mass (ι:=ι) step hstep
  obtain ⟨J,control,hbase⟩ := uniform_centered_source_moment (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap (BR0+Bseed) BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    (add_nonneg hBR0 hBseed) hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨Cbase,hCbase,hbase⟩ := hbase η₀ hη₀
  refine ⟨Cmass*(2:ℝ)^Fintype.card ι*Cbase,by positivity,?_⟩
  filter_upwards [hbase] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hBunit hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible D hD hDcap
  have hb0 : 0≤b := zero_le_one.trans hb
  have hz : 0<Z := zero_lt_one.trans hZ.1
  let cover:=original_enclosure s hBunit
  let cost:=Cbase*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε
  let nd:=(D.absNorm:ℝ)^step
  have hnd : 0<nd := Real.rpow_pos_of_pos
    (zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)) _
  have hcost : 0≤cost := by
    have hheight : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    dsimp only [cost]
    positivity
  have hchild (Blabel : boundedLabels (tuplePools s) D) :
      Z^step*groupedMoment q (seededRebasedSource s hb0 cover D hD.ne_zero Blabel)
        ha η tp keep Φ K≤cost/nd := by
    let r:=seededRebasedSource s hb0 cover D hD.ne_zero Blabel
    have hc:=seeded_canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀
      s hcanonical hb0 cover D hD.ne_zero Blabel
    have hdata:=seeded_rebased_data s hb0 cover D hD.ne_zero Blabel
    have hscale:=seeded_four_scales_le s hb0 cover D hD.ne_zero Blabel
    have hpuncture:=seeded_puncture_cap s hb0 cover D hD.ne_zero Blabel Z BR0 Bseed
      (zero_lt_one.trans hZ.1) hR hDcap
    have hgates:=seeded_mixed_gates s hb0 cover D hD.ne_zero Blabel Z
      (inputWidth η K Z) (Real.logb Z (MixedSelectedVolume.volume q)) rho w hZ.1 hw hmixed hnative
    have he:=hZ.2 (liveIndices Blabel.val) θ w σ freq t₀ tp V R₀
      hw hwL hσ hσhi hV hfreq hR₀ r hc hdata.1 hdata.2.2.1
      (fun i=>hMs i.val) hpuncture hHholes hholes (fun i=>hHR i.val) hFhole
      (hscale.1.trans hX₁) (hscale.2.1.trans hX₂)
      (hscale.2.2.1.trans hY₁) (hscale.2.2.2.1.trans hY₂)
      η hη K hK hKcap hKinv χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW
      hWcap hWinv hqvolume hR0 hgates.1 hgates.2 keep hkeep heligible D hD.ne_zero hDcap
    change (nd*Z^step)*groupedMoment q r ha η tp keep Φ K≤cost at he
    apply (le_div_iff₀ hnd).mpr
    calc
      _=(nd*Z^step)*groupedMoment q r ha η tp keep Φ K := by ring
      _≤cost := he
  let count:=((Fintype.card (Allocation D (Finset.univ : Finset (ι⊕Fin 2))):ℝ)*
    (boundedLabels (tuplePools s) D).card)
  have hcount : 0≤count := by dsimp only [count];positivity
  have hsplit:=grouped_seed_allocation q hqP s ha hb0 cover D hD η tp keep Φ K hK hΦs hΦ
  have hmassD:=hmass a b s D hD
  change count*(∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
    ∑Blabel : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc Blabel)≤
    Cmass*nd*((∏i,s.M i)^2*(2:ℝ)^Fintype.card ι)/(pairNorm s.d*(D.absNorm:ℝ)) at hmassD
  calc
    _≤Z^step*(count*∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
      ∑Blabel : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc Blabel*
        groupedMoment q (seededRebasedSource s hb0 cover D hD.ne_zero Blabel) ha η tp keep Φ K) :=
      mul_le_mul_of_nonneg_left hsplit (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
    _=count*∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
      ∑Blabel : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc Blabel*
        (Z^step*groupedMoment q (seededRebasedSource s hb0 cover D hD.ne_zero Blabel)
          ha η tp keep Φ K) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alloc halloc
      apply Finset.sum_congr rfl
      intro Blabel hBlabel
      ring
    _≤count*∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
      ∑Blabel : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc Blabel*(cost/nd) := by
      apply mul_le_mul_of_nonneg_left _ hcount
      apply Finset.sum_le_sum
      intro alloc halloc
      apply Finset.sum_le_sum
      intro Blabel hBlabel
      exact mul_le_mul_of_nonneg_left (hchild Blabel) (normalized_frozen_nonneg s D alloc Blabel)
    _=(count*(∑alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)),
      ∑Blabel : boundedLabels (tuplePools s) D,normalizedFrozen s D alloc Blabel))*(cost/nd) := by
      simp_rw [←Finset.sum_mul]
      ring
    _≤(Cmass*nd*((∏i,s.M i)^2*(2:ℝ)^Fintype.card ι)/(pairNorm s.d*(D.absNorm:ℝ)))*(cost/nd) :=
      mul_le_mul_of_nonneg_right hmassD (div_nonneg hcost hnd.le)
    _=_ := by
      dsimp only [cost]
      field_simp [hnd.ne',(pairNorm_pos s.hd.1 s.hd.2).ne',
        (zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)).ne']
      <;> ring

end
end Candidate.SilPrior.FourthPower.MixedFirstSeededMoment
