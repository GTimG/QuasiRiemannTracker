/- Copyright (c) 2026 Sil. Apache-2.0.
One uniform application of ALL FOUR actual providers, with a single
degree, control and constant before moving Source/profile/character data.
Only canonical data and explicit numerical caps are hypotheses.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallOriginalScale
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallWholeGauss
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallFourShapes
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedPlainRemainders
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedInnerExceptionalLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallUniformFour
universe u
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
variable {ι : Type u} [Fintype ι]
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

theorem uniform_full_gauss
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ → ℂ)
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
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus →
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι → RayQuotient.Characters M Hray)(w σ freq : ι → ℝ)(t₀ V : ℝ)
      (R₀ : ι → Finset Id),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤V → (∀i,|freq i|≤V) → (∀i,(R₀ i).card≤Holes) → (∑i,w i)≤rho →
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s →
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
  obtain ⟨jn,un,hnative⟩ := uniform_original_scale_nonexceptional (ι:=ι) M Hray hHray
    Holes Wslot a b Mcap L Lslot Lcap Cap BR BH Bnorm rho ε δCount δPhys lo hi
    Lradius Cr εg Meta ζ hWs hW ha haUpper hb hLslot hLcap hCap hCapb hLordinary
    hBR hBH hBnorm hMcap hε hδCount hδPhys hLradius hCr hεg hζ hMready hβ Q hQt hQ72 hQM
  obtain ⟨je,ue,h00e,hkernel⟩ := MixedInnerExceptionalLedger.uniform_actual_exceptional_part
    N (3/4) Bcap a b εEx δEx Bnorm Lradius Cr εsum
    (by norm_num) (by norm_num) hBcap ha (zero_le_one.trans hb) hεEx hδEx
    (by linarith) hBnorm hLradius hCr hεsum
  obtain ⟨Ckernel,hCkernel,hexceptional⟩ := hkernel ballProfile
  obtain ⟨Aex,Csum,hAex,hCsum,hexceptional⟩ :=
    hexceptional Q (NeZero.ne Q) hQt hQ72
  obtain ⟨Czero,hCzero,hzero⟩ := uniform_plain_zero N εZero hεZero
  obtain ⟨Ctail,hCtail,htail⟩ := uniform_plain_tail_seed Btail BU ξTail saving
    (hBnorm.trans hBT) hξTail
  let J:=jn+2*je
  let U:=(un∪ue)∪{(0,0)}
  have hjn : jn≤J := by dsimp only [J];omega
  have hje : 2*je≤J := by dsimp only [J];omega
  have hun : un⊆U := (Finset.subset_union_left).trans Finset.subset_union_left
  have hue : ue⊆U := (Finset.subset_union_right).trans Finset.subset_union_left
  have h00 : (0,0)∈U := by simp only [U,Finset.mem_union,Finset.mem_singleton];tauto
  refine ⟨J,U,?_⟩
  intro η₀ hQη₀
  obtain ⟨Cs,Cp,Cg,hCs,hCp,hCg,hnative⟩ := hnative η₀ hQη₀
  let kn:=fixedNativeCost (Fintype.card ι) jn Cs Cp Cg b
  let capBound:=4*(Kslot^N)^2
  let c0:=‖paperRadialFourier ballProfile 0‖*Czero*capBound
  let c1:=kn*((Kslot^N)^2*(2:ℝ)^N)
  let c2:=Ckernel*Aex*Csum*(windowMoment je)^2*fixedQCost Q*
    ((1024:ℝ)^N*(Kslot^N)^3)^2
  let c3:=Ctail*capBound
  have hkn : 0≤kn := fixed_native_cost_nonneg _ _ _ _ _ _ hCs.le hCp.le hCg.le
  have hc0 : 0≤c0 := by dsimp only [c0,capBound];positivity
  have hc1 : 0≤c1 := by dsimp only [c1];positivity
  have hc2 : 0≤c2 := by
    have hQcost:=fixedQCost_nonneg Q
    dsimp only [c2]
    positivity
  have hc3 : 0≤c3 := by dsimp only [c3,capBound];positivity
  let C:=1+c0+c1+c2+c3
  have hC : 0<C := by dsimp only [C];linarith
  have hc0C : c0≤C := by dsimp only [C];linarith
  have hc1C : c1≤C := by dsimp only [C];linarith
  have hc2C : c2≤C := by dsimp only [C];linarith
  have hc3C : c3≤C := by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [hnative,hexceptional,htail] with Z hnZ heZ htZ
  refine ⟨hnZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap hpoolcap hFcap hPcap
    cover u seed hu0 huCap hseed hu Sco beta base Hsource η tp K Tsec hK hη hradius
    hKcap hTcap hcutoff hconductor
  let r:=avoidSource s u
  let P:=commonProfile s J U t₀ V tp
  have hz : 0<Z := zero_lt_one.trans hnZ.1
  have hprofile : 0≤P := common_profile_nonneg s J U t₀ V tp hV
  have hHs : 0<Hsource := by
    have hb0 : 0<b := zero_lt_one.trans_le hb
    have hT:=s.total_pos
    have hp:=pairNorm_pos s.hd.1 s.hd.2
    have hPpos (i:ι) : 0<s.P i := zero_lt_one.trans_le (s.hP i)
    have hprod : 0<∏i,2*s.P i :=
      Finset.prod_pos (fun i _=>mul_pos (by norm_num) (hPpos i))
    change 0<b^2*(s.T/pairNorm s.d)*(∏i,2*s.P i)
    exact mul_pos (mul_pos (sq_pos_of_pos hb0) (div_pos hT hp)) hprod
  have hTsec : 0≤Tsec := (div_pos (sq_pos_of_pos hHs) hK).le.trans hcutoff
  -- Avoidance changes only the marked coefficients, so these are literal
  -- profile and support-cap identities, not estimates.
  have hrProfile : commonProfile r J U t₀ V tp=P := rfl
  have hrNorm : sourceNormCap r.P b r.T r.d=Hsource := rfl
  have hpCap : (profileCap r)^2≤capBound*P := by
    have hh:=profile_cap_le r N J Kslot U h00 t₀ V tp hcard hKslot hM hV
    rw [hrProfile] at hh
    exact hh
  have hn0 := hnZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hholes hsmall
    s hcan s.hM hR hH hHnorm hHR hX₁ hX₂ hY₁ hY₂ hsourcecap cover u seed hseed hu
    η tp K Tsec ξTail fixedBadMask 1 hK hη fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) hradius
  rw [closed_budget_eq_simple] at hn0
  have hnative :
      ‖secondRetainedEnergy η tp Sco beta ballProfile K Tsec Z ξTail-
        partEnergy true η 1 Q fixedBadMask tp Sco beta ballProfile K Tsec Z ξTail Hsource‖≤
      c1*P*nativeShape s η seed Z (base+δPhys+εg) := by
    exact hn0.trans (native_cost_le_common s N jn J Kslot kn un U t₀ V tp Z
      (base+δPhys+εg) η seed hcard hKslot hM hkn hun hjn hV hz.le)
  have he0 := heZ.2 ι r cover hcard hFcap hPcap hpoolcap η 1 fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) seed hseed hseed.ne_zero
    tp (K/16) 1 Tsec ξTail Hsource (by positivity) (by norm_num) hTsec
    hsourcecap hradius hconductor
  have hscale : 16*(K/16)*(1:ℝ)^4=K := by ring
  simp only [hscale,div_one] at he0
  have heRaw := (div_le_iff₀ (sourceVolume_pos r)).mp he0
  have hex :
      ‖partEnergy true η 1 Q fixedBadMask tp Sco beta ballProfile K Tsec Z ξTail Hsource‖≤
      c2*P*exceptionalShape s seed K Z (2*εEx+2*Bnorm*δEx+εsum) := by
    exact heRaw.trans (exceptional_cost_le_common r N je J Kslot ue U Q seed
      Ckernel Aex Csum Z εEx δEx Bnorm εsum K t₀ V tp
      hcard hKslot hM hue hje hV hz hK hCkernel hAex.le hCsum.le)
  have hz0 := hzero ι a b r hcard ha seed η tp K Z Bnorm hseed.ne_zero hK.le hnZ.1 hsourcecap
  have hzBound :
      ‖(K:ℂ)*paperRadialFourier ballProfile 0*sourceSecondZero Sco beta η tp‖≤
      c0*P*zeroShape s seed K Z (Bnorm*εZero) := by
    let F0:=K*‖paperRadialFourier ballProfile 0‖*Czero*Hsource*Z^(Bnorm*εZero)/(seed.absNorm:ℝ)
    have hF0 : 0≤F0 := by
      have hp:=Real.rpow_nonneg hz.le (Bnorm*εZero)
      dsimp only [F0]
      positivity
    have hzExact :
        ‖(K:ℂ)*paperRadialFourier ballProfile 0*sourceSecondZero Sco beta η tp‖≤
          F0*(profileCap r)^2 := by
      have hh:=hz0
      rw [hrNorm] at hh
      convert hh using 1 <;> first | rfl | (simp only [F0]; ring)
    calc
      _≤F0*(profileCap r)^2:=hzExact
      _≤F0*(capBound*P):=mul_le_mul_of_nonneg_left hpCap hF0
      _=c0*P*zeroShape s seed K Z (Bnorm*εZero) := by
        simp only [F0,c0,zeroShape,Hsource]
        ring
  have hnormTail : Hsource≤Z^Btail :=
    hsourcecap.trans (Real.rpow_le_rpow_of_exponent_le hnZ.1.le hBT)
  have hpoolTail : poolCap r≤Z^Btail :=
    hpoolcap.trans (Real.rpow_le_rpow_of_exponent_le hnZ.1.le hBT)
  have ht0 := htZ.2 ι a b r ha (zero_le_one.trans hb) u seed η tp K Hsource Tsec
    hu0 huCap hK hHs hpoolTail le_rfl hnormTail hKcap hTcap hcutoff
  have htBound :
      ‖secondDiscardedEnergy η tp Sco beta ballProfile K Tsec Z ξTail‖≤
      c3*P*tailShape u Z saving := by
    let Ftail:=Ctail*Z^(-saving)/(u.absNorm:ℝ)
    have hF : 0≤Ftail := by
      have hp:=Real.rpow_nonneg hz.le (-saving)
      dsimp only [Ftail]
      positivity
    have htExact :
        ‖secondDiscardedEnergy η tp Sco beta ballProfile K Tsec Z ξTail‖≤
          Ftail*(profileCap r)^2 := by
      convert ht0 using 1 <;> first | rfl | (simp only [Ftail]; ring)
    calc
      _≤Ftail*(profileCap r)^2:=htExact
      _≤Ftail*(capBound*P):=mul_le_mul_of_nonneg_left hpCap hF
      _=c3*P*tailShape u Z saving := by
        simp only [Ftail,c3,tailShape]
        ring
  have h0 : c0*P*zeroShape s seed K Z (Bnorm*εZero)≤C*P*zeroShape s seed K Z (Bnorm*εZero) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc0C hprofile)
      (zero_shape_nonneg s seed K Z _ hK.le hz.le)
  have h1 : c1*P*nativeShape s η seed Z (base+δPhys+εg)≤
      C*P*nativeShape s η seed Z (base+δPhys+εg) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1C hprofile)
      (native_shape_nonneg s η seed Z _ hz.le)
  have h2 : c2*P*exceptionalShape s seed K Z (2*εEx+2*Bnorm*δEx+εsum)≤
      C*P*exceptionalShape s seed K Z (2*εEx+2*Bnorm*δEx+εsum) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2C hprofile)
      (exceptional_shape_nonneg s seed K Z _ hK.le hz.le)
  have h3 : c3*P*tailShape u Z saving≤C*P*tailShape u Z saving :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc3C hprofile)
      (tail_shape_nonneg u Z saving hz.le)
  apply (original_scale_four_parts r ha seed η 1 Q fixedBadMask tp K Tsec Z ξTail Hsource hK).trans
  have hall:=add_le_add (add_le_add (add_le_add (hzBound.trans h0) (hnative.trans h1))
    (hex.trans h2)) (htBound.trans h3)
  exact hall.trans_eq (by unfold fullShape;ring)

end
end Candidate.FourthPower.RepairedSmallUniformFour
