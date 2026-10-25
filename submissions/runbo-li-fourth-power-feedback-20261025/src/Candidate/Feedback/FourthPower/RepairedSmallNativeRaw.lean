/- Copyright (c) 2026 Sil. Apache-2.0.
Actual native ORDINARY energy with G=seed=1, ready for an already
extracted same-G2 canonical live source. No Gauss energy is substituted.

-/
import Candidate.Feedback.FourthPower.RepairedSmallRawBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedSmallNativeRaw
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentFirstSectors
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal HeckeDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedOriginalSource MixedHeightEnergy MixedNativeFloor MixedInnerExceptionalBlock MixedCommonRestriction
open MixedFirstActualNonexceptional MixedFirstProfileEnvelope MixedCanonicalSource
open RepairedSmallRowAllocation RepairedSmallRawBudget
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def rawEnergy (s : Source ι a b) (ha : 0<a) (D : Id) (τ : Character)
    (v : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  sourceRestrictedEnergy keep (sourceColumns s) (sourceCoefficient s ha D)
    (heightCoeff τ v) Φ K

theorem coefficient_seed_mask (s : Source ι a b) (ha : 0<a) (D I : Id) :
    sourceCoefficient s ha D I=(if D∣I then sourceCoefficient s ha 1 I else 0) :=
  column_seed_mask (Fintype.piFinset (tuplePools s)) (punctureProduct s.S s.H) s.R D I
    s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d

theorem unit_sector_energy (s : Source ι a b) (ha : 0<a) (D : Id)
    (τ : Character) (v : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sectorEnergy s ha 1 (by exact CenteredMomentAddedZero.supported_one_ideal) 1 D (heightCoeff τ v) keep Φ K=
      rawEnergy s ha D τ v keep Φ K := by
  have hpool : residualPool (1:Id) one_ne_zero (sourceColumns s)=sourceColumns s := by
    ext I
    simp only [mem_residualPool,one_mul]
  unfold sectorEnergy rawEnergy
  rw [hpool]
  have hc : (fun I : Id => if IsCoprime (1:Id) I ∧ D∣I then
      sourceCoefficient s ha 1 (1*I) else 0)=sourceCoefficient s ha D := by
    funext I
    simp only [isCoprime_one_left,one_mul,true_and,coefficient_seed_mask s ha D I]
  rw [hc]

theorem unit_height_energy (s : Source ι a b) (ha : 0<a) (D : Id)
    (τ : Character) (v : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (heightRow s ha τ 1 (by exact CenteredMomentAddedZero.supported_one_ideal) 1 D v) keep Φ K=
      rawEnergy s ha D τ v keep Φ K/sourceVolume s := by
  have he := height_energy_exact s ha τ 1 (by exact CenteredMomentAddedZero.supported_one_ideal) 1 D v keep Φ K
  change radialEnergy (heightRow s ha τ 1 CenteredMomentAddedZero.supported_one_ideal 1 D v) keep Φ K=
    sectorEnergy s ha 1 CenteredMomentAddedZero.supported_one_ideal 1 D (heightCoeff τ v) keep Φ K/sourceVolume s at he
  rwa [unit_sector_energy] at he

variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- A genuine analytic provider, with the complete native input called
internally. The RHS is LINEAR in the raw volume/full prefix. -/
theorem uniform_native_raw
    (Holes : ℕ) (Wslot : ℝ → ℂ)
    (a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε lo hi : ℝ)
    (hWs : Function.support Wslot⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hBrow : 0≤Brow) (hBchar : 0≤Bchar) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι → RayQuotient.Characters M Hray)(w σ freq : ι → ℝ)(t₀ V : ℝ)
      (R₀ : ι → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
      (s.R.absNorm:ℝ)≤Z^BR → s.H⊆ReferencePrimeEnclosure.enclosure (Cap*Z^Lcap) →
      ((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH →
      (∀i,∀P∈s.H,P.val∈R₀ i) →
      s.X₁≤Z^L → s.X₂≤Z^L → s.Y₁≤Z^L → s.Y₂≤Z^L →
    ∀(τ : Character)(n : Fin 4 → ℤ),1≤dyadicScale (n 1) →
      dyadicScale (n 1)≤Z^Brow → (τ.modulus.absNorm:ℝ)≤Z^Bchar →
    ∀D : Id,Squarefree D → (D.absNorm:ℝ)≤Z^Bnorm → ∀v : ℝ,
      rawEnergy s ha D τ v (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))≤
        (C*diagonalControl ballProfile*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (height t₀ V s.t₁ s.t₂)^degree*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)*
          Z^((3/4:ℝ)*rho+ε)/(D.absNorm:ℝ)*(1+‖v‖)^(2*degree))*
          (sourceVolume s/pairNorm s.d) := by
  obtain ⟨degree,control,hbase⟩ := uniform_small_width_native (ι:=ι) M Hray hHray
    Holes Wslot a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε lo hi
    hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm
    hBrow hBchar hε hβ Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hQη₀
  refine ⟨C,hC,hbase.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτ D hD hDcap v
  have hg : ((1:Id).absNorm:ℝ)≤Z^Bnorm := by
    simpa only [map_one,Nat.cast_one] using Real.one_le_rpow hZ.1.le hBnorm
  have he := hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτ
    1 (by exact CenteredMomentAddedZero.supported_one_ideal) 1 D (dvd_refl _) hD hg hDcap v
  rw [unit_height_energy] at he
  have hv := sourceVolume_pos s
  have hh := (div_le_iff₀ hv).mp he
  apply hh.trans_eq
  simp only [map_one,Nat.cast_one,div_one]
  ring

end
end Candidate.Feedback.FourthPower.RepairedSmallNativeRaw
