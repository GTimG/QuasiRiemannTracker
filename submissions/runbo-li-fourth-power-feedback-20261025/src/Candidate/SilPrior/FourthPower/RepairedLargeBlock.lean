/- Copyright (c) 2026 Sil. Apache-2.0.
Actual large nonexceptional block for a GENERIC root Source. The ordinary
reference and Source.L may move. Canonical/geometric inputs are structural;
the checked analytic block supplier and actual root admission are invoked
inside, not supplied as energy hypotheses.
-/
import Candidate.SilPrior.FourthPower.RepairedLargeTail
import Candidate.SilPrior.FourthPower.RepairedRootParameters
import Candidate.SilPrior.FourthPower.RepairedRawRetained
import Candidate.SilPrior.FourthPower.OuterFreshRootAdmission

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedLargeBlock
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion ActualEisensteinCubic
open CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondBlockAggregate MixedFirstExceptionalWindow OuterFreshAllocatedWindow
open CenteredMomentSecondRetainedAggregate
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn CenteredMomentSourceMass
open CenteredMomentCanonicalFirst CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar CenteredMomentUncenteredTerminal
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedLiveNormalization
open MixedFirstLiveSource MixedFirstActualNonexceptional MixedFirstSourceGeometry
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstCutoffs MixedFirstExceptionalNormalization
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierSource
open OuterFreshSource OuterFreshSelectedWindow OuterFreshSelection OuterFreshSelected
open OuterFreshRootAdmission OuterFreshCutoffAllowance OuterFreshNonexceptionalFamily
open OuterFreshWindowPair OuterFreshConsumer OuterFreshNonexceptionalBlock OuterFreshSelectedKernel
open OuterFreshAllocationMass RepairedBlockUniformity RepairedRootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ:=Classical.decEq _

abbrev FirstShape (Index:Type v)(RootSlot:Index → Type u)[Fintype Index][∀k,Fintype (RootSlot k)] :=
  Σk:Index,Finset (RootSlot k)
abbrev FirstSlot {Index:Type v}{RootSlot:Index → Type u}[Fintype Index][∀k,Fintype (RootSlot k)]
    (shape:FirstShape Index RootSlot) := ↥shape.2

private theorem coarse_gates (N:ℕ)(ε:ℝ)(hε:0<ε) :
    8≤windowCap N ε ∧ 0≤seedCap N ε ∧
    2*(3:ℝ)+1≤windowCap N ε ∧ (N:ℝ)*mesh ε+1≤windowCap N ε ∧
    mesh ε≤windowCap N ε ∧ 7+1≤windowCap N ε ∧
    commonExponent 3 (N:ℝ) (mesh ε)≤seedCap N ε ∧
    (9/4:ℝ)/comparisonScale (9/4)≤16 := by
  have hm:=mesh_spec ε hε
  have hprod:=mul_nonneg (Nat.cast_nonneg N) hm.1.le
  have hm1:mesh ε≤1:=hm.2.1.trans (by norm_num [rootReserve])
  dsimp only [windowCap,seedCap,commonExponent]
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,?_⟩
  norm_num [comparisonScale]

private theorem cutoff_le_one (N:ℕ)(ε:ℝ)(hε:0<ε) : cutoffLoss N ε≤1 := by
  have h:internalScale N ε≤omegaLoss ε:=(internal_spec N ε hε).2.2.1
  have ho:omegaLoss ε≤1/10000000000:=(omega_spec ε hε).2.2.2
  unfold cutoffLoss
  linarith

variable (M:Id)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray:Subgroup (O⧸M)ˣ)(hHray:RayOrthogonality.globalUnits M≤Hray)

/-- Keep normalization of the decay-zero factor entirely at scalar level.
The huge Source-dependent conclusion is supplied as an expected type. -/
private theorem remove_zero_decay (A B R k : ℝ)
    (h : A*(1+k)^(0:ℕ)*B ≤ R) : A*B ≤ R := by
  simpa only [pow_zero,mul_one] using h
/-- Positivity proved once with abstract scalar/ideal parameters. -/
private theorem nominal_child_positive (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z pad : ℝ) (n : ℤ) (hZ : 0 < Z) :
    0 < nominalChildScale C D E K V Z pad n := by
  unfold nominalChildScale
  exact Real.rpow_pos_of_pos hZ _
set_option maxHeartbeats 1400000 in
/-- One constant and event before all root-family members and first live
subtypes. The only upstream root assumptions are its real canonical data,
ordinary/support caps, and the original numerical face. Source.L is free.
-/
theorem uniform_generic_first_large_block
    (Index:Type v)[Fintype Index](RootSlot:Index → Type u)[∀k,Fintype (RootSlot k)]
    (N Holes:ℕ)(hcards:∀k,Fintype.card (RootSlot k)≤N)(ε:ℝ)(hε:0<ε)
    (Wslot:ℝ → ℂ)(hW:ContDiff ℝ ∞ Wslot)(hWs:Function.support Wslot⊆Icc (1:ℝ) 2)
    (Kslot:ℝ)(hKslot:1≤Kslot)(hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q:Id)[NeZero Q](hQt:Q≠⊤)(hQ72:Q≤Ideal.span {(72:O)})(hQM:Q≤M) :
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,Q≤η₀.modulus →
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀k:Index,∀(chars:RootSlot k → RayQuotient.Characters M Hray)(w freq:RootSlot k → ℝ)
      (t₀ V:ℝ)(R₀:RootSlot k → Finset Id),
      ∀hw:(∀i,0≤w i),∀hwm:(∀i,w i≤mesh ε),0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) →
    ∀root:Source (RootSlot k) (1/4) (9/4),
      Canonical M Hray hHray Wslot 16 (windowCap N ε) Z η₀ chars w (fun _=>33/50) freq t₀ R₀ root →
      (∀i,root.M i≤Kslot) → root.R=1 → root.H=∅ → root.Fhole=1 →
      root.X₁≤Z^(3:ℝ) → root.X₂≤Z^(3:ℝ) → root.Y₁≤Z^(3:ℝ) → root.Y₂≤Z^(3:ℝ) →
      sourceNormCap root.P (9/4) root.T root.d≤Z^(seedCap N ε) →
    ∀cover:OriginalEnclosure root,∀(η:Character)(Kroot:ℝ),0<Kroot → Kroot≤Z^(2:ℝ) →
      (η.modulus.absNorm:ℝ)≤Z →
      Real.logb Z (root.T/pairNorm root.d)+(93/25:ℝ)*(∑i,w i) ≤ inputWidth η Kroot Z-rootReserve  →
    ∀p₁:ActiveLabel (sourceColumns root) (sourceCoefficient root (by norm_num) 1),
    ∀E₁:Finset (CommonIndex p₁.val.1 p₁.val.2),∀B₁:actualAllocations (tuplePools root) p₁.val.1,
      frozenCoefficient B₁.val p₁.val.1 root.R root.ν root.Wslot root.P≠0 →
    RepairedLargeTail.Result (α := liveIndices B₁.val) N ε hε Kslot degree control C Z t₀ V Q
      (allocatedLiveSource root (by norm_num) cover p₁.val.1 B₁)
      (live_enclosure (allocationSource root (by norm_num) cover p₁.val.1 B₁))
      (fun i => w i.val) (fun i => hw i.val) (fun i => hwm i.val)
      η p₁.val.1 p₁.val.2 E₁ Kroot (sourceVolume root) := by
  have hfamilyCard (shape:FirstShape Index RootSlot):Fintype.card (FirstSlot shape)≤N:=
    (Fintype.card_le_of_injective (fun i:shape.2=>i.val) Subtype.val_injective).trans (hcards shape.1)
  obtain ⟨hWin,hSeed,hOrig,hSlots,hMesh,hDecl,hSeedExp,hCapc⟩:=coarse_gates N ε hε
  have hcap:=cap_spec N ε hε
  have hloss:=internal_losses_paid N ε hε
  obtain ⟨degree,control,hfamily⟩:=uniform_actual_block_family M Hray hHray
    (FirstShape Index RootSlot) FirstSlot N Holes hfamilyCard Wslot
    (1/4) (9/4) 3 (windowCap N ε) (mesh ε) (windowCap N ε) 16 (seedCap N ε) 0 7
    (33/50) (33/50) Kslot (seedCap N ε) (windowLoss ε) mixedReserve (commonPower N ε) (artificialLoss N ε)
    hWs hW (by norm_num) le_rfl (by norm_num) (by norm_num) hOrig (mesh_spec ε hε).1.le
    hMesh le_rfl hSlots (by norm_num) hCapc hSeed (by norm_num) (by norm_num) hDecl hβ hKslot hSeed hSeedExp
    hcap.2.2.1 hcap.2.2.2 hloss.2.2.2.1 hloss.2.1 Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨C,hC,hfamily⟩:=hfamily ballProfile 0 η₀ hQη₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hfamily,uniform_event (9/4) N (cutoffLoss N ε) hloss.1,
    eventually_ge_atTop fixedPresentationCost] with Z hfamilyZ hevent hfixed
  refine ⟨hfamilyZ.1,?_⟩
  intro k chars w freq t₀ V R₀ hw hwm hV hfreq hholes root hcanonical hM hR hH hF
    hX₁ hX₂ hY₁ hY₂ hsource cover η Kroot hK hKcap hη hroot p₁ E₁ B₁ hf₁
  let first : Source (liveIndices B₁.val) (1/4) (9/4) :=
    allocatedLiveSource root (by norm_num) cover p₁.val.1 B₁
  let cover₁ : OriginalEnclosure first :=
    live_enclosure (allocationSource root (by norm_num) cover p₁.val.1 B₁)
  change RepairedLargeTail.Result (α := liveIndices B₁.val) N ε hε Kslot degree control C Z t₀ V Q
    first cover₁ (fun i => w i.val) (fun i => hw i.val) (fun i => hwm i.val)
    η p₁.val.1 p₁.val.2 E₁ Kroot (sourceVolume root)
  unfold RepairedLargeTail.Result
  intro τ hmod n₁ hret u L hlarge J q x hx seed hseed hu p₂ ξ χ₀ U n₂ tp Kchild ra r Rfreq Rdecl H Budget
  have hsupp₁:=commonLabels_supported _ _ _ p₁.property
  have hsupp₂:=commonLabels_supported _ _ _ p₂.property
  have hCD₁:CompletedGauss.primeSupport p₁.val.1=CompletedGauss.primeSupport p₁.val.2:=
    (commonLabels_data _ _ _ _ p₁.property).2.2
  have hCD₂:CompletedGauss.primeSupport p₂.val.1=CompletedGauss.primeSupport p₂.val.2:=
    (commonLabels_data _ _ _ _ p₂.property).2.2
  have hfirstCan:=allocated_canonical M Hray hHray Wslot 16 (windowCap N ε) Z η₀ chars w
    (fun _=>33/50) freq t₀ R₀ root hcanonical (by norm_num) cover p₁.val.1 B₁
  have hCcap:=(commonLabel_norm_bounds (sourceColumns root) (sourceCoefficient root (by norm_num) 1)
    (sourceNormCap root.P (9/4) root.T root.d)
    (fun I _ hI=>(original_coefficient_cap root (by norm_num) 1 I hI).2) _ _ p₁.property).1.trans hsource
  have hfirstR:(first.R.absNorm:ℝ)≤Z^(seedCap N ε) := by
    change ((root.R*p₁.val.1).absNorm:ℝ)≤_
    simpa only [hR,one_mul] using hCcap
  have hfirstH:first.H=∅:=hH
  have hfirstF:first.Fhole=1:=hF
  have hrootEvent:UniformEvent (9/4) (Fintype.card (RootSlot k)) (cutoffLoss N ε) Z:=
    ⟨hevent.1,hevent.2.1,hevent.2.2.1,fun n hn=>hevent.2.2.2 n (hn.trans (hcards k))⟩
  have hPs:∀i,root.P i=Z^(w i):=fun i=>congrFun hcanonical.2.2.2.2 i
  have hgate (G:Id)(hG:G=p₂.val.1 ∨ G=p₂.val.2):=
    actual_first_large_admission root (by norm_num) (by norm_num) cover w (widthFloor ε) (mesh ε)
      (mesh_spec ε hε).1.le hw hwm η τ p₁.val.1 p₁.val.2 hsupp₁.1 hsupp₁.2 hCD₁ E₁ B₁ hf₁
      Z Kroot (cutoffLoss N ε) rootReserve mixedReserve hK hloss.1 hrootEvent
      (original_reserve_paid N ε hε) hPs hroot hmod n₁ hret u L (mesh_spec ε hε).1 hlarge
      p₂.val.1 p₂.val.2 hsupp₂.1 hsupp₂.2 hCD₂ U G hG
  have hpaid:=((hgate p₂.val.1 (Or.inl rfl)) x hx).1
  have hdecl:=declared_width_polynomial_cap q (fun i=>first.hP i) η Kroot Z
    (deficit p₁.val.1 p₁.val.2 E₁ Kroot (sourceVolume root) Z n₁)
    (Real.logb Z (p₁.val.1.absNorm:ℝ)) (cutoffLoss N ε) 2 1 1 hK hfamilyZ.1 hKcap
    (by simpa only [Real.rpow_one] using hη) (by simpa only [Real.rpow_one] using hfixed)
    p₂.val.1 p₂.val.2 hsupp₂.1 U
  have hdecl7:declaredWidth q η Kroot Z (deficit p₁.val.1 p₁.val.2 E₁ Kroot (sourceVolume root) Z n₁)
      (Real.logb Z (p₁.val.1.absNorm:ℝ)) (cutoffLoss N ε) p₂.val.1 p₂.val.2 U≤7:=by
    linarith [cutoff_le_one N ε hε]
  have hf:Supported (frozenProduct q x):=ReferenceProductEnergy.supported_product
    (fun i=>(x i).val)
    (fun i=>(first.hpn i.val _ (frozen_slot_mem first (by norm_num) u L J x hx i)).1)
  obtain ⟨ψ,hψ⟩:=exists_sharp_family τ (frozenProduct q x) hf ξ p₂.val.1 p₂.val.2 hsupp₂.1 hsupp₂.2 hCD₂ U
  have hnumeric (G:Id)(hG:G=p₂.val.1 ∨ G=p₂.val.2) := fun B hB =>
    let hg := ((hgate G hG) x hx).2 B hB
    And.intro hg.1 hg.2.2
  have hKchild : 0 < Kchild := nominal_child_positive p₁.val.1 p₁.val.2 E₁
    Kroot (sourceVolume root) Z (cutoffLoss N ε) n₁ (zero_lt_one.trans hfamilyZ.1)
  refine remove_zero_decay _ _ _ (kernelScale n₂) ?_
  exact hfamilyZ.2 (⟨k,liveIndices B₁.val⟩:FirstShape Index RootSlot)
    (fun i=>chars i.val) (fun i=>w i.val) (fun _=>33/50) (fun i=>freq i.val) t₀ tp V (fun i=>R₀ i.val)
    (fun i=>hw i.val) (fun i=>hwm i.val) (fun _=>le_rfl) (fun _=>le_rfl) hV
    (fun i=>hfreq i.val) (fun i=>hholes i.val) first hfirstCan (fun i=>hM i.val) hfirstR
    (by simp only [hfirstH,Finset.empty_subset])
    (by simp [hfirstH,MixedCompletedRows.holes])
    (by intro i P hP;simp only [hfirstH,Finset.notMem_empty] at hP)
    (by simp only [hfirstF,map_one,Nat.cast_one,Real.rpow_zero,le_rfl]) hX₁ hX₂ hY₁ hY₂
    cover₁ u L J x hx seed hseed hu p₂ hsupp₂.1 hsupp₂.2 τ ξ χ₀ U ψ hψ
    Rfreq Kchild hKchild n₂ Rdecl hpaid hdecl7 hnumeric


end
end Candidate.SilPrior.FourthPower.RepairedLargeBlock
