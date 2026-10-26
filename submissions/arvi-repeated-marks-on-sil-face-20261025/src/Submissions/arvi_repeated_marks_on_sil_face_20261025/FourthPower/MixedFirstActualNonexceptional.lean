/- Copyright (c) 2026 Sil. Apache-2.0.
Actual nonexceptional contribution after first genuine extraction.
All live source estimates are supplied by the checked finite-subset
theorem. The per-block admissibility ledger is discharged from full
norm caps, and the artificial divisor remains the live source seed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstLiveSource
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstUniformNonexceptional
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstNonexceptionalAllocation
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedActualAdmissibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstActualNonexceptional
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open RayFourExpansion QRH.Record1252270103KernelMass
open QuadraticInitialBound NativeInjectiveEnergy
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentLattice CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondEnergySplit CenteredMomentSecondWindowBudget CenteredMomentSecondLiveBlock
open CenteredMomentActiveSource CenteredMomentSectorLocalization CenteredMomentSecondRadicalBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentPrimeSlot (primePool)
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalHeights
open MixedHeightEnergy MixedHeightEnvelope MixedCommonCoefficient MixedCommonRestriction
open MixedLiteralAllocation MixedOriginalNormCap MixedOriginalTail MixedFirstLiveSource
open MixedLiveNormalization MixedFirstUniformNonexceptional MixedFirstNonexceptionalAllocation
open MixedActualNonexceptionalBound MixedActualAdmissibility MixedPoissonLocalization
open MixedCanonicalSource ReferencePrimeEnclosure MixedCompletedRows
open CenteredMomentCommonRawScale
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Genuine extraction can only decrease the full finite source radius.
Both ordinary prime-power prefixes are retained in this comparison. -/
theorem live_norm_cap (s : Source ι a b) :
    sourceNormCap (liveSource s).P b (liveSource s).T (liveSource s).d≤
      sourceNormCap s.P b s.T s.d := by
  have hnorm (I : Id) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : 1≤plainNorm s.B :=
    one_le_mul_of_one_le_of_one_le (hnorm _ (s.hB _)) (hnorm _ (s.hB _))
  have hprefix : pairNorm s.d≤pairNorm s.prefixPair := by
    rw [Source.prefixPair,extracted_pair_norm]
    exact le_mul_of_one_le_right (pairNorm_pos s.hd.1 s.hd.2).le hp
  have hdiv := div_le_div_of_nonneg_left s.total_pos.le
    (pairNorm_pos s.hd.1 s.hd.2) hprefix
  have hprod : (∏i : liveIndices s.B,2*s.P i.val)≤∏i,2*s.P i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) (fun i=>2*s.P i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
      (fun i _ _=>by linarith [s.hP i])
  change b^2*(s.T/pairNorm s.prefixPair)*(∏i : liveIndices s.B,2*s.P i.val)≤
    b^2*(s.T/pairNorm s.d)*(∏i,2*s.P i)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)) hprod
    (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i.val))))
    (mul_nonneg (sq_nonneg _) (div_nonneg s.total_pos.le (pairNorm_pos s.hd.1 s.hd.2).le))

/-- A scalar interface for transporting the column, coefficient and
support cap. In particular no dependent family of block labels is
transported through a source dictionary. -/
private def columnDifference (S : Finset Id) (β : Id→ℂ) (Hsource : ℝ)
    (η : Character) (tp K Wblock Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  ‖localizedDensity Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S=>β I*heightCoeff η tp I)
      K Wblock (retainedWeight (frequencyRadius Tsec Z ξ))-
    partEnergy true η χ₀ Q m tp S β
      ballProfile (16*K*Wblock^4) Tsec Z ξ Hsource/(Wblock:ℂ)‖

/-- This is the literal nonexceptional retained difference of a live
source. It is only ONE component of its full positive Gauss energy. -/
def nonexceptionalPart (s : Source ι a b) (ha : 0<a) (D : Id)
    (η : Character) (tp K Wblock Tsec Z ξ : ℝ) (Q : Id) (m : O) (χ₀ : RayCharacter) : ℝ :=
  ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha D I*heightCoeff η tp I)
      K Wblock (retainedWeight (frequencyRadius Tsec Z ξ))-
    partEnergy true η χ₀ Q m tp (sourceColumns s) (sourceCoefficient s ha D)
      ballProfile (16*K*Wblock^4) Tsec Z ξ (sourceNormCap s.P b s.T s.d)/(Wblock:ℂ)‖

def allocatedPart (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G D : Id) (η : Character) (tp K Wblock Tsec Z ξ : ℝ) (Q : Id) (m : O)
    (χ₀ : RayCharacter) : ℝ :=
  ((actualAllocations (tuplePools s) G).card:ℝ)*∑B : actualAllocations (tuplePools s) G,
    ‖frozenWeight (punctureProduct s.S s.H) B.val*frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*
      nonexceptionalPart (allocatedLiveSource s hb cover G B) ha D η tp K Wblock Tsec Z ξ Q m χ₀

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- These are exact data identities, not an estimate on a source. -/
def Canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b) : Prop :=
  s.S=enclosure (Cap*Z^Lcap) ∧
  s.pool=(fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) ∧
  s.ν=slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t ∧
  s.Wslot=(fun i=>slotProfile W (σ i) (freq i)) ∧ s.P=(fun i=>Z^(w i))

theorem uniform_actual_allocated_part
    (N Holes : ℕ) (hι : Fintype.card ι≤N) (W : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bcap Meta ε δ δG lo hi κ Lradius Cr εg ζ : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hM : 0<Mcap)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBcap : 0≤Bcap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ) (hδG : 0<δG)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg) (hζ : 0<ζ)
    (hMcap : Lradius+Meta+Bcap+ζ≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃Cs Cp Cg Ccount : ℝ,0<Cs ∧ 0<Cp ∧ 0<Cg ∧ 0<Ccount ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bcap→
    ∀cover : OriginalEnclosure s,∀G D : Id,G≠0→(G.absNorm:ℝ)≤Z^BG→Squarefree D→
    ∀(η : Character)(tp K Wblock Tsec ξ : ℝ)(m : O)(χ₀ : RayCharacter),
      (η.modulus.absNorm:ℝ)≤Z^Meta→0<K→0<Wblock→m≠0→
      ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→frequencyRadius Tsec Z ξ≤Cr*Z^Lradius→
    let A := Cs*diagonalControl ballProfile*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
      sourceHeight t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))^degree
    allocatedPart s ha (zero_le_one.trans hb) cover G D η tp K Wblock Tsec Z ξ Q m χ₀≤
      Ccount*(G.absNorm:ℝ)^δG*
        fullCost s.P s.M degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg) A b s.T tp Wblock D s.d*
        (η.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2 := by
  obtain ⟨degree,control,hs⟩ := uniform_nonexceptional_subsets (α:=ι) M Hray hHray Holes W
    a b Mcap L Lslot Lcap Cap (BR+BG) BH Bcap ε δ lo hi κ Lradius Cr εg
    hWs hW ha haUpper hb hM hLslot hLcap hCap (add_nonneg hBR hBG) hBH hBcap
    hCapb hLordinary hε hδ hLradius hCr hεg hβ hκ Q hQt hQ72 hQM
  obtain ⟨Ccount,hCcount,hcount⟩ := uniform_allocation_budget N δG hδG
  have hadm := uniform_actual_admissibility Lradius Meta Bcap Cr ζ Mcap hCr hζ hMcap
  refine ⟨degree,control,?_⟩
  intro η₀ hη₀
  obtain ⟨Cs,Cp,Cg,hCs,hCp,hCg,hs⟩ := hs η₀ hη₀
  refine ⟨Cs,Cp,Cg,Ccount,hCs,hCp,hCg,hCcount,?_⟩
  filter_upwards [hs,hadm] with Z hZ hadmZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hRcap hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource cover G D hG hGcap hD η tp K Wblock Tsec ξ m χ₀
    hη hK hWblock hm hml hm2 hradius A
  obtain ⟨hS,hpool,hν,hWslot,hP⟩ := hcanonical
  have hZ0 : 0<Z := zero_lt_one.trans hZ.1
  have hRG : ((s.R*G).absNorm:ℝ)≤Z^(BR+BG) := by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hZ0]
    exact mul_le_mul hRcap hGcap (Nat.cast_nonneg _) (Real.rpow_nonneg hZ0.le _)
  have hA : 0≤A := by
    have hdiag := diagonalControl_nonneg ballProfile
    have hh := sourceHeight_one_le t V (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi)) hV
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hCs.le hdiag) (sq_nonneg _))
      (pow_nonneg (zero_le_one.trans hh) _)
  have hpart (B : actualAllocations (tuplePools s) G) :
      nonexceptionalPart (allocatedLiveSource s (zero_le_one.trans hb) cover G B) ha D
        η tp K Wblock Tsec Z ξ Q m χ₀≤
      closedBudget (Fintype.card (liveIndices B.val)) degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg)
        A b (s.T*∏i : liveIndices B.val,s.P i.val) tp Wblock η D
        (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) := by
    let q := allocatedLiveSource s (zero_le_one.trans hb) cover G B
    let Hq := sourceNormCap q.P b q.T q.d
    have hqcap : Hq≤Z^Bcap :=
      (live_norm_cap (allocationSource s (zero_le_one.trans hb) cover G B)).trans hsource
    have hqcol (I : Id) (_hI : I∈sourceColumns q) (hi : sourceCoefficient q ha D I≠0) :
        (I.absNorm:ℝ)≤Hq := (original_coefficient_cap q ha D I hi).2
    let pool₀ := fun i : liveIndices B.val=>supportedPool (primePool M Hray 2 (Z^(w i.val)))
    let S₀ := finiteColumns (Fintype.piFinset (sourcePools pool₀ q.d q.hd b s.X₁ s.X₂ s.Y₁ s.Y₂))
    let β₀ := originalColumn (enclosure (Cap*Z^Lcap)) s.H pool₀ q.d q.hd (s.R*G) D
      (slotCoefficient (fun i : liveIndices B.val=>relativeCharacter M Hray hHray η₀ (θ i.val))
        (fun i=>R₀ i.val) t)
      (fun i : liveIndices B.val=>slotProfile W (σ i.val) (freq i.val))
      (fun i : liveIndices B.val=>Z^(w i.val))
      (phaseProfile s.W₁ (s.t₁/(2*Real.pi))) (phaseProfile s.W₂ (s.t₂/(2*Real.pi)))
      b s.X₁ s.X₂ s.Y₁ s.Y₂
    let H₀ := sourceNormCap (fun i : liveIndices B.val=>Z^(w i.val)) b (s.X₁*s.X₂) q.d
    have he := hZ.2 (liveIndices B.val) θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
      (s.R*G) D (mul_ne_zero s.hR hG) hRG hD s.H hH hholes (fun i=>hHR i.val)
      s.W₁ s.W₂ s.hs₁ s.hs₂ (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
      (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) hX₁ hX₂ hY₁ hY₂ (s.hpX.trans s.hpY.symm)
      q.d q.hd
    have hcolumns : sourceColumns q=S₀ := by
      change finiteColumns (Fintype.piFinset (sourcePools (fun i : liveIndices B.val=>s.pool i.val)
        q.d q.hd b s.X₁ s.X₂ s.Y₁ s.Y₂))=_
      rw [hpool]
    have hcoefficient : sourceCoefficient q ha D=β₀ := by
      change originalColumn s.S s.H (fun i : liveIndices B.val=>s.pool i.val) q.d q.hd
        (s.R*G) D (fun i : liveIndices B.val=>s.ν i.val) (fun i=>s.Wslot i.val) (fun i=>s.P i.val)
        (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        b s.X₁ s.X₂ s.Y₁ s.Y₂=_
      rw [hS,hpool,hν,hWslot,hP,norm_power_profile_phase,norm_power_profile_phase]
      rfl
    have hcapEq : H₀=Hq := by
      change sourceNormCap _ b (s.X₁*s.X₂) q.d=sourceNormCap (fun i : liveIndices B.val=>s.P i.val) b s.T q.d
      rw [hP,s.hpX]
    have hcap₀ : H₀≤Z^Bcap := hcapEq.trans_le hqcap
    have hcol₀ (I : Id) (hI : I∈S₀) (hi : β₀ I≠0) : (I.absNorm:ℝ)≤H₀ := by
      have hmem : I∈sourceColumns q := hcolumns.symm ▸ hI
      have hne : sourceCoefficient q ha D I≠0 :=
        fun hz=>hi ((congrFun hcoefficient I).symm.trans hz)
      calc
        (I.absNorm:ℝ)≤Hq := hqcol I hmem hne
        _=H₀ := hcapEq.symm
    -- Construct the geometry in the native column types of `he`.
    -- No ActiveLabel/SourceBlocks type is rewritten along the dictionary.
    let ρ₀ := fun (p : ActiveLabel S₀ β₀)
      (U : Finset (CommonIndex p.val.1 p.val.2))
      (_n : SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) H₀)=>
        Lradius+Meta+Bcap+ζ
    have hgeometry₀ : ∀p∈liveLabels η S₀ β₀,∀U,
      ∀n : SourceBlocks p.val.1 p.val.2 U (16*K*Wblock^4) (frequencyRadius Tsec Z ξ) H₀,
      physicalBlock η tp S₀ β₀ p.val.1 p.val.2
        (commonLabels_supported (activeSource S₀ β₀) _ _ p.property).1
        (commonLabels_supported (activeSource S₀ β₀) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
        (partRows false η χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        ballProfile (16*K*Wblock^4) (fun i=>(n i:ℤ))≠0→
      Real.logb Z (frequencyRadius Tsec Z ξ)+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator p.val.1 p.val.2))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ))≤ρ₀ p U n ∧
        ρ₀ p U n≤Mcap := by
      intro p hp U n hn
      exact hadmZ.2 η S₀ β₀ H₀ hη hcol₀ hcap₀ p U _
        (actual_nonzero_radius_pos η tp S₀ β₀ _ _ _ _ U _ _ _ _ _ hn) hradius
    have hh : columnDifference S₀ β₀ H₀ η tp K Wblock Tsec Z ξ Q m χ₀≤
        closedBudget (Fintype.card (liveIndices B.val)) degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg)
          A b (s.X₁*s.X₂*∏i : liveIndices B.val,Z^(w i.val)) tp Wblock η D q.d :=
      he hcap₀ η tp K Wblock Tsec ξ m χ₀ hK hWblock hm hml hm2 hradius ρ₀ hgeometry₀
    have hvalue : nonexceptionalPart q ha D η tp K Wblock Tsec Z ξ Q m χ₀=
        columnDifference S₀ β₀ H₀ η tp K Wblock Tsec Z ξ Q m χ₀ := by
      change columnDifference (sourceColumns q) (sourceCoefficient q ha D) Hq
        η tp K Wblock Tsec Z ξ Q m χ₀=_
      calc
        _ = columnDifference S₀ (sourceCoefficient q ha D) Hq
            η tp K Wblock Tsec Z ξ Q m χ₀ :=
          congrArg (fun S=>columnDifference S (sourceCoefficient q ha D) Hq
            η tp K Wblock Tsec Z ξ Q m χ₀) hcolumns
        _ = columnDifference S₀ β₀ Hq η tp K Wblock Tsec Z ξ Q m χ₀ :=
          congrArg (fun β=>columnDifference S₀ β Hq η tp K Wblock Tsec Z ξ Q m χ₀) hcoefficient
        _ = columnDifference S₀ β₀ H₀ η tp K Wblock Tsec Z ξ Q m χ₀ :=
          congrArg (fun H=>columnDifference S₀ β₀ H η tp K Wblock Tsec Z ξ Q m χ₀) hcapEq.symm
    have hhActual := hvalue.le.trans hh
    have hprefix : q.d=(s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)) := rfl
    rw [hprefix] at hhActual
    simpa only [q,s.hpX,hP] using hhActual
  have hsum : allocatedPart s ha (zero_le_one.trans hb) cover G D η tp K Wblock Tsec Z ξ Q m χ₀≤
      allocationBudget (punctureProduct s.S s.H) (tuplePools s) G s.R s.ν s.Wslot s.P degree Cp Cg Z
        (κ*(∑i,w i)+ε+δ+εg) A b s.T tp Wblock η D s.d := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro B hB
    exact mul_le_mul_of_nonneg_left (hpart B) (sq_nonneg _)
  exact hsum.trans (hcount hι (punctureProduct s.S s.H) (tuplePools s) G s.R hG s.ν s.Wslot
    s.P s.M (fun i=>zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm s.hM s.hW
    degree Cp Cg Z (κ*(∑i,w i)+ε+δ+εg) A b s.T tp Wblock hCp.le hCg.le hZ0.le hA hWblock.le η D s.d)

end
end Candidate.FourthPower.MixedFirstActualNonexceptional
