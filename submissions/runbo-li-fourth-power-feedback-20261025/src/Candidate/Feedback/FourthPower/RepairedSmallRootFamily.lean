/- Copyright (c) 2026 Sil. Apache-2.0.
ALL-FOUR uniformity for an arbitrary fixed finite root-type family.
Actual selectedJ is indexed directly, making the residual type defeq.
This is the final RootInput/Frame-facing uniform provider interface.

-/
import Candidate.Feedback.FourthPower.RepairedSmallUniformFour

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedSmallRootFamily
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal HeckeDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedNativeFloor MixedInnerExceptionalBlock MixedFirstActualNonexceptional
open MixedFirstProfileEnvelope MixedCanonicalSource MixedFirstAvoidance OuterFreshSelectedWindow
open RepairedSmallRowAllocation RepairedSmallRawBudget RepairedSmallNativeRaw RepairedSmallNativeFamily
open QuadraticInitialBound
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)


open RayFourExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSecondEnergySplit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWindowBudget CenteredMomentSecondHeightFamily
open MixedActualFamily MixedPhysicalEnvelopes MixedRawEnvelope
open RepairedSmallAvoidedNative


open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondRadicalBudget CenteredMomentCompleteCommon
open MixedCanonicalEnvelope MixedOriginalCoprimality MixedOriginalNormCap
open MixedInnerExceptionalLedger MixedActualGeometry
open RepairedSmallPhysical


open CenteredMomentSecondLiveBlock CenteredMomentSecondActivePhysicalDictionary
open MixedActualRetained MixedLocalizedDictionary RepairedSmallActivePhysical


open MixedActualNonexceptionalBound RepairedSmallRetained


open RepairedSmallClosed MixedActualAdmissibility

open EisensteinSchwartzPoisson
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondNonexceptionalScalar
open MixedPrincipalBudget MixedInnerExceptionalLedger MixedOriginalTail
open RepairedSmallOriginalScale RepairedSmallWholeGauss RepairedSmallCommonProfile
open RepairedSmallFourShapes RepairedPlainRemainders RepairedSmallCostControl



open RepairedSmallUniformFour MixedSupplierSource
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

abbrev OuterLive {κ : Type u} [Fintype κ] (L : Finset κ) := {j // j∉Lᶜ}

abbrev SupplierShape (Index : Type v) [Fintype Index]
    (RootSlot : Index → Type u) [∀k,Fintype (RootSlot k)] :=
  Σk : Index, ΣB : Finset (RootSlot k), ΣL : Finset B, Finset (OuterLive L)

-- Match the abstract first-live supplier convention ONLY at its base B.
-- Nested OuterLive/RestIndex subtypes retain their ordinary derived instances.
local instance (priority := 2000)
    {Index : Type v} [Fintype Index] {RootSlot : Index → Type u} [∀k,Fintype (RootSlot k)]
    (i : SupplierShape Index RootSlot) : DecidableEq ↥i.2.1 := Classical.decEq _
abbrev SupplierSlot {Index : Type v} [Fintype Index]
    {RootSlot : Index → Type u} [∀k,Fintype (RootSlot k)] (i : SupplierShape Index RootSlot) :=
  {j : OuterLive i.2.2.1 // j∉i.2.2.2}

theorem supplier_slot_card {Index : Type v} [Fintype Index]
    {RootSlot : Index → Type u} [∀k,Fintype (RootSlot k)] (i : SupplierShape Index RootSlot) :
    Fintype.card (SupplierSlot i)≤Fintype.card (RootSlot i.1) := by
  let f : SupplierSlot i → RootSlot i.1 := fun j => j.val.val.val
  have hf : Function.Injective f := by
    intro j k h
    exact Subtype.ext (Subtype.ext (Subtype.ext h))
  exact Fintype.card_le_of_injective f hf

/-- Selected J itself is indexed, so this is DEFINITIONAL equality;
no complementary-membership transport or Fintype cast is required. -/
theorem supplier_rest_type {Index : Type v} [Fintype Index]
    {RootSlot : Index → Type u} [∀k,Fintype (RootSlot k)]
    (k : Index) (B : Finset (RootSlot k)) (q : MixedSupplierFourthRow.Data B) :
    SupplierSlot (Index:=Index) (RootSlot:=RootSlot) ⟨k,B,q.L,q.J⟩=RestIndex q := rfl


theorem uniform_root_full_gauss
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (RootSlot k)≤N) (Wslot : ℝ → ℂ)
    (a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi Lradius Cr εg Meta ζ Bcap εEx δEx εsum εZero Btail BU ξTail saving Kslot : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hMcap : 0≤Mcap) (hε : 0<ε) (hδCount : 0<δCount) (hδPhys : 0<δPhys)
    (hLradius : 0≤Lradius) (hCr : 0<Cr) (hεg : 0<εg)
    (hζ : 0<ζ) (hMready : Lradius+Meta+Bnorm+ζ≤Mcap)
    (hBcap : 0≤Bcap) (hεEx : 0<εEx) (hδEx : 0<δEx) (hδExSmall : δEx<1/8)
    (hεsum : 0<εsum) (hεZero : 0<εZero) (hBT : Bnorm≤Btail) (hξTail : 0<ξTail)
    (hKslot : 1≤Kslot)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)

 :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧ ∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀i : SupplierShape Index RootSlot,∀(θ : SupplierSlot i → RayQuotient.Characters M Hray)(w σ freq : SupplierSlot i → ℝ)(t₀ V : ℝ)
      (R₀ : SupplierSlot i → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source (SupplierSlot i) a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
      (∀i,s.M i≤Kslot) → (s.R.absNorm:ℝ)≤Z^BR →
      s.H⊆ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap) →
      ((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH →
      (∀i,∀P∈s.H,P.val∈R₀ i) →
      s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
      sourceNormCap s.P b s.T s.d≤Z^Bnorm → poolCap s≤Z^Bnorm →
      (s.Fhole.absNorm:ℝ)≤Z^Bcap → (∏i,2*s.P i)≤Z^Bcap →
    ∀cover : OriginalEnclosure s,∀u seed : Id,u≠0 → (u.absNorm:ℝ)≤Z^BU → Squarefree seed → u∣s.R*seed →
    let Sco:=sourceColumns s;
    let beta:=sourceCoefficient (avoidSource s u) ha seed;
    let base:=(3/4:ℝ)*rho+ε+Bnorm*δCount;

    let Hsource:=sourceNormCap s.P b s.T s.d;

    ∀(η : Character)(tp K Tsec : ℝ),
      0<K → (η.modulus.absNorm:ℝ)≤Z^Meta →
      frequencyRadius Tsec Z ξTail≤Cr*Z^Lradius →
      K≤Z^Btail → Tsec≤Z^Btail →
      Hsource^2/K≤Tsec →
      familyConductorBudget (avoidSource s u) η (frequencyRadius Tsec Z ξTail)≤Z^Bcap →
      (sourceGaussEnergy Sco beta (heightCoeff η tp) ballProfile K).re≤
        C*commonProfile s degree control t₀ V tp*
          fullShape s η u seed K Z (base+δPhys+εg)
            (2*εEx+2*Bnorm*δEx+εsum) (Bnorm*εZero) saving

 := by
  choose deg ctl hbase using fun i : SupplierShape Index RootSlot =>
    uniform_full_gauss (ι:=SupplierSlot i) M Hray hHray N Holes
      ((supplier_slot_card i).trans (hcard i.1)) Wslot
      a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi Lradius Cr εg Meta ζ
      Bcap εEx δEx εsum εZero Btail BU ξTail saving Kslot
      hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm hMcap
      hε hδCount hδPhys hLradius hCr hεg hζ hMready hBcap hεEx hδEx hδExSmall
      hεsum hεZero hBT hξTail hKslot hβ Q hQt hQ72 hQM
  let J:=∑i : SupplierShape Index RootSlot,deg i
  let U:=((Finset.univ : Finset (SupplierShape Index RootSlot)).biUnion ctl)∪{(0,0)}
  have hJ (i : SupplierShape Index RootSlot) : deg i≤J :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hU (i : SupplierShape Index RootSlot) : ctl i⊆U :=
    (Finset.subset_biUnion_of_mem ctl (Finset.mem_univ i)).trans Finset.subset_union_left
  have h00 : (0,0)∈U := by simp only [U,Finset.mem_union,Finset.mem_singleton];tauto
  refine ⟨J,U,h00,?_⟩
  intro η₀ hQη₀
  choose C hC hpoint using fun i : SupplierShape Index RootSlot => hbase i η₀ hQη₀
  let Ctotal:=1+∑i : SupplierShape Index RootSlot,C i
  have hCtotal : 1≤Ctotal := by
    have hs:=Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset (SupplierShape Index RootSlot))) => (hC i).le)
    dsimp only [Ctotal]
    linarith
  have hCle (i : SupplierShape Index RootSlot) : C i≤Ctotal := by
    have hs:=Finset.single_le_sum
      (fun j (_ : j∈(Finset.univ : Finset (SupplierShape Index RootSlot))) => (hC j).le)
      (Finset.mem_univ i)
    dsimp only [Ctotal]
    linarith
  refine ⟨Ctotal,hCtotal,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpoint,Filter.eventually_gt_atTop (1:ℝ)]
    with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro i θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap hpoolcap hFcap hPcap
    cover u seed hu0 huCap hseed hu Sco beta base Hsource η tp K Tsec hK hη hradius
    hKcap hTcap hcutoff hconductor
  have he:=(hZ i).2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap hpoolcap hFcap hPcap
    cover u seed hu0 huCap hseed hu η tp K Tsec hK hη hradius hKcap hTcap hcutoff hconductor
  have hprof : commonProfile s (deg i) (ctl i) t₀ V tp≤commonProfile s J U t₀ V tp :=
    profile_powers_le s (deg i) (2*deg i) J (ctl i) U t₀ V tp
      (hU i) (hJ i) (Nat.mul_le_mul_left 2 (hJ i)) hV
  have hcoef:=mul_le_mul (hCle i) hprof
    (common_profile_nonneg s (deg i) (ctl i) t₀ V tp hV) (zero_le_one.trans hCtotal)
  have hz : 0≤Z := zero_le_one.trans hZ1.le
  have hshape : 0≤fullShape s η u seed K Z (base+δPhys+εg)
      (2*εEx+2*Bnorm*δEx+εsum) (Bnorm*εZero) saving := by
    exact add_nonneg (add_nonneg (add_nonneg
      (zero_shape_nonneg s seed K Z _ hK.le hz)
      (native_shape_nonneg s η seed Z _ hz))
      (exceptional_shape_nonneg s seed K Z _ hK.le hz))
      (tail_shape_nonneg u Z saving hz)
  exact he.trans (mul_le_mul_of_nonneg_right hcoef hshape)

end
end Candidate.Feedback.FourthPower.RepairedSmallRootFamily
