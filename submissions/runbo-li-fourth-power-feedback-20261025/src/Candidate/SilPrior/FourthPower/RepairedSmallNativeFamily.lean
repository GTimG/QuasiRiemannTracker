/- Copyright (c) 2026 Sil. Apache-2.0.
A single actual native ordinary envelope for every finite source subtype.
Controls and eventual events precede all moving arithmetic data.

-/
import Candidate.SilPrior.FourthPower.RepairedSmallNativeRaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedSmallNativeFamily
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentFirstSectors
open CenteredMomentLattice CenteredMomentFiniteProfileExceptional CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison CenteredMomentSecondNonexceptionalChosenBlock
open CenteredMomentSecondHeightFamily CenteredMomentUncenteredTerminal HeckeDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedOriginalSource MixedHeightEnergy MixedNativeFloor MixedInnerExceptionalBlock MixedCommonRestriction
open MixedFirstActualNonexceptional MixedFirstProfileEnvelope MixedCanonicalSource
open RepairedSmallRowAllocation RepairedSmallRawBudget
open RepairedSmallNativeRaw
open QuadraticInitialBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}


open RepairedSmallNativeRaw
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)


theorem uniform_native_raw_subsets
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
    ∀T : Finset ι,∀(θ : T → RayQuotient.Characters M Hray)(w σ freq : T → ℝ)(t₀ V : ℝ)
      (R₀ : T → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
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
          (sourceVolume s/pairNorm s.d)
 := by
  choose deg ctl hbase using fun T : Finset ι =>
    uniform_native_raw (ι:=T) M Hray hHray Holes Wslot
      a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε lo hi
      hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary hBR hBH hBnorm
      hBrow hBchar hε hβ Q hQt hQ72 hQM
  let degree := ∑T : Finset ι,deg T
  let control := (Finset.univ : Finset (Finset ι)).biUnion ctl
  have hdeg (T : Finset ι) : deg T≤degree :=
    Finset.single_le_sum (fun T _ => Nat.zero_le _) (Finset.mem_univ T)
  have hctl (T : Finset ι) : ctl T⊆control :=
    Finset.subset_biUnion_of_mem ctl (Finset.mem_univ T)
  refine ⟨degree,control,?_⟩
  intro η₀ hQη₀
  choose C hC hpoint using fun T : Finset ι => hbase T η₀ hQη₀
  let Ctotal := 1+∑T : Finset ι,C T
  have hCtotal : 0<Ctotal := by
    have hs := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset ι))) => (hC T).le)
    dsimp only [Ctotal]
    linarith
  have hCle (T : Finset ι) : C T≤Ctotal := by
    have hs := Finset.single_le_sum
      (fun U (_ : U∈(Finset.univ : Finset (Finset ι))) => (hC U).le)
      (Finset.mem_univ T)
    dsimp only [Ctotal]
    linarith
  refine ⟨Ctotal,hCtotal,(Filter.eventually_all.mpr hpoint).mono ?_⟩
  intro Z hZ
  refine ⟨(hZ ∅).1,?_⟩
  intro T θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτ D hD hDcap v
  have he := (hZ T).2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτ D hD hDcap v
  have hc₁ : sourceControl (ctl T) s.W₁≤sourceControl control s.W₁ :=
    Seminorm.le_def.mp (Finset.sup_mono (hctl T)) s.W₁
  have hc₂ : sourceControl (ctl T) s.W₂≤sourceControl control s.W₂ :=
    Seminorm.le_def.mp (Finset.sup_mono (hctl T)) s.W₂
  have hprod : (sourceControl (ctl T) s.W₁*sourceControl (ctl T) s.W₂)^2≤
      (sourceControl control s.W₁*sourceControl control s.W₂)^2 :=
    pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _))
      (mul_le_mul hc₁ hc₂ (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)) 2
  have hheight : 1≤height t₀ V s.t₁ s.t₂ := by
    unfold height
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hh := pow_le_pow_right₀ hheight (hdeg T)
  have hheight0 : 0≤height t₀ V s.t₁ s.t₂ := zero_le_one.trans hheight
  have hv := pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v))
    (Nat.mul_le_mul_left 2 (hdeg T))
  have hcoeff :
      C T*(sourceControl (ctl T) s.W₁*sourceControl (ctl T) s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^(deg T)*(1+‖v‖)^(2*deg T)≤
      Ctotal*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^degree*(1+‖v‖)^(2*degree) := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact mul_le_mul (hCle T) hprod (sq_nonneg _) hCtotal.le
      · exact hh
      · positivity
      · positivity
    · exact hv
    · positivity
    · positivity
  let rest := diagonalControl ballProfile*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)*
    Z^((3/4:ℝ)*rho+ε)/(D.absNorm:ℝ)*(sourceVolume s/pairNorm s.d)
  have hrest : 0≤rest := by
    have hd := diagonalControl_nonneg ballProfile
    have hp := (pairNorm_pos s.hd.1 s.hd.2).le
    have hs := (sourceVolume_pos s).le
    have hz : 0<Z := zero_lt_one.trans (hZ T).1
    have hh := (dyadicScale_pos (n 1)).le
    dsimp only [rest]
    positivity
  apply he.trans
  have hfinal := mul_le_mul_of_nonneg_right hcoeff hrest
  convert hfinal using 1 <;> dsimp only [rest] <;> ring

end
end Candidate.SilPrior.FourthPower.RepairedSmallNativeFamily
