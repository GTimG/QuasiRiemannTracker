/- Copyright (c) 2026 Sil. Apache-2.0.
Unconditional native ordinary-row supplier for the ACTUAL avoided source
at the SAME second common label. Genuine live bounds are supplied internally.
No third Gauss generation and no whole-source Canonical assumption on avoidance.

-/
import Candidate.Feedback.FourthPower.RepairedSmallNativeFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedSmallAvoidedNative
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open MixedHeightEnergy
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
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem uniform_avoided_native
    (Holes : ℕ) (Wslot : ℝ → ℂ)
    (a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε δ lo hi : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hBrow : 0≤Brow) (hBchar : 0≤Bchar) (hε : 0<ε) (hδ : 0<δ)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι → RayQuotient.Characters M Hray)(w σ freq : ι → ℝ)(t₀ V : ℝ)
      (R₀ : ι → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
      (∀i,1≤s.M i) → (s.R.absNorm:ℝ)≤Z^BR →
      s.H⊆ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap) →
      ((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH →
      (∀i,∀P∈s.H,P.val∈R₀ i) →
      s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
    ∀cover : OriginalEnclosure s,∀(τ : Character)(n : Fin 4 → ℤ),
      1≤dyadicScale (n 1) → dyadicScale (n 1)≤Z^Brow →
      (τ.modulus.absNorm:ℝ)≤Z^Bchar →
    ∀(u G seed D : Id)(hG : Supported G),seed∣G → u∣s.R*G → Squarefree D →
      (G.absNorm:ℝ)≤Z^Bnorm → (D.absNorm:ℝ)≤Z^Bnorm → ∀v : ℝ,
      radialEnergy (heightRow (avoidSource s u) ha τ G hG seed D v)
        (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))≤
        (C*slotCost s*diagonalControl ballProfile*
          (sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (height t₀ V s.t₁ s.t₂)^degree*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)*
          Z^((3/4:ℝ)*rho+ε)*(G.absNorm:ℝ)^δ/
          (G.absNorm:ℝ)/pairNorm s.d/(D.absNorm:ℝ))*(1+‖v‖)^(2*degree) := by
  obtain ⟨degree,control,hbase⟩ := uniform_native_raw_subsets (ι:=ι) M Hray hHray
    Holes Wslot a b L Lslot Lcap Cap (BR+Bnorm) BH Bnorm Brow Bchar rho ε lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary (add_nonneg hBR hBnorm)
    hBH hBnorm hBrow hBchar hε hβ Q hQt hQ72 hQM
  obtain ⟨Cc,hCc,hcount⟩ := uniform_allocation_count (Fintype.card ι) δ hδ
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη₀
  refine ⟨Cc*C,mul_pos hCc hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ cover τ n hn hncap hτ
    u G seed D hG hseed hu hD hGcap hDcap v
  have hz : 0<Z := zero_lt_one.trans hZ.1
  let hb0 : 0≤b := zero_le_one.trans hb
  let A := C*diagonalControl ballProfile*
    (sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^degree*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)*
    Z^((3/4:ℝ)*rho+ε)/(D.absNorm:ℝ)*(1+‖v‖)^(2*degree)
  have hA : 0≤A := by
    have hd := diagonalControl_nonneg ballProfile
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    have hrow := (dyadicScale_pos (n 1)).le
    dsimp only [A]
    positivity
  have hRG : ((s.R*G).absNorm:ℝ)≤Z^(BR+Bnorm) := by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hz]
    exact mul_le_mul hR hGcap (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
  have hchild (B : actualAllocations (tuplePools s) G) :
      liveEnergy s ha hb0 cover G B D (heightCoeff τ v)
        (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))≤
      A*(sourceVolume (allocatedLiveSource s hb0 cover G B)/
        pairNorm (allocatedLiveSource s hb0 cover G B).d) := by
    let r := allocatedLiveSource s hb0 cover G B
    have hcanonical := allocated_canonical M Hray hHray Wslot Cap Lcap Z η₀
      θ w σ freq t₀ R₀ s hcan hb0 cover G B
    have hsum : (∑i : liveIndices B.val,w i.val)≤rho := by
      apply le_trans _ hsmall
      rw [Finset.sum_coe_sort]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hw i)
    have he := hZ.2 (liveIndices B.val)
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ V (fun i=>R₀ i.val) (fun i=>hw i.val) (fun i=>hwL i.val)
      (fun i=>hσ i.val) (fun i=>hσhi i.val) hV (fun i=>hfreq i.val)
      (fun i=>hholes i.val) hsum r hcanonical hRG hH hHnorm
      (fun i P hP=>hHR i.val P hP) hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτ D hD hDcap v
    exact he
  have hsector := avoided_energy_of_live_bounds s ha hb0 cover u G seed D hG hseed hu hM
    (heightCoeff τ v) (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))
    (dyadicScale_pos _) (fun z=>ballProfile_nonneg _) A hA hchild
  have hcnt := hcount (ι:=ι) le_rfl a b s G hG.1
  have hnon : 0≤slotCost s*A*(sourceVolume s/pairNorm s.d)/(G.absNorm:ℝ) := by
    have hs := slot_cost_nonneg s
    have hv := (sourceVolume_pos s).le
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    positivity
  have hraw := hsector.trans (mul_le_mul_of_nonneg_right hcnt hnon)
  rw [height_energy_exact]
  change sectorEnergy (avoidSource s u) ha G hG seed D (heightCoeff τ v)
    (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))/sourceVolume s≤_
  have hh := div_le_div_of_nonneg_right hraw (sourceVolume_pos s).le
  apply hh.trans_eq
  dsimp only [A]
  field_simp [(sourceVolume_pos s).ne',(pairNorm_pos s.hd.1 s.hd.2).ne',
    (zero_lt_one.trans_le (ideal_norm_one_le hG.1)).ne',
    (zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)).ne']
  <;> ring

end
end Candidate.Feedback.FourthPower.RepairedSmallAvoidedNative
