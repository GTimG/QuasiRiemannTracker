/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B085
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceReflection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AddedZeroUniform
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.ChildUniform; sha256 07072a36fd1d28323105b9fe32f7bfa7f4ff8f1cc7708e249424435768248e55 -/
section
                                           
                                                             

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle61FirstChildUniform
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open Cycle61FirstChild CenteredMomentEnergyReferenceLowControl
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem reflected_child_uniform_from_positive
    (a b:ℝ)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0< D ∧
    ∀(Wslot:ℝ→ℂ)(bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(C:ℝ)(_hC:0≤ C)
    (_hlow:PositiveAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (_hB:0≤ Bmask)
    (F:Finset α)(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (_hw:∀i,0≤ w i)(_hwL:∀i,w i≤ Lslot)(_hσlo:∀i,lo≤σ i)(_hσhi:∀i,σ i≤ hi)
    (_hheight:0≤ height)(_hfreq:∀i,|freq i|≤ height)
    (s:NaturalState Z Bmask bΦ)(_hQ:s.fixedModulus=internalQ Q η₀)(_hs:s.width≤ Mcap)
    (Wshort:𝓢(ℝ,ℂ))(_hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(_hX₁:0< X₁)(_hX₂:0< X₂)(_hc₁:X₁≤ Z^L)(_hc₂:X₂≤ Z^L)
    (_hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
,
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      (C*diagonalControl s.radial.profile*D*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε))*(1+‖v‖)^(2*n) :=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_child_control a b ha hlo hhi S degree
  refine ⟨n,T,D,hD,?_⟩
  intro Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q C hC hlow hB
    F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsW
    j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hh:=reflected_child_from_positive M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ Z η₀ Q degree S C hlow hB ha hlo hhi F θ w σ freq t height hw hwL
    hσlo hσhi hheight hfreq s hQ hs Wshort hsW j k v X₁ X₂ hX₁ hX₂ hc₁ hc₂
    hcapacity
  have hb:=hd Wshort hsW j k v t height hheight
  have hp:0≤ C*diagonalControl s.radial.profile:=mul_nonneg hC (by
    unfold diagonalControl
    positivity)
  have hz:0≤ Z^(s.width+ε):=(Real.rpow_pos_of_pos (zero_lt_one.trans_le s.base_ge_one) _).le
  have hmul:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hz
  apply hh.trans
  convert hmul using 1 <;> ring

end SevenEighths.Cycle61FirstChildUniform

end

end OAI

/- Adapted from OpenAI/math family003 Energy/ReferenceLowMoments.lean, Apache-2.0.
The terminal is applied only to daughters satisfying their own old capacity. -/

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.ChildUniform -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Homogeneous; sha256 c0da0bcc593cda7338fdd7c31a3a98cbbb6f662fd0d57dbefdcf381fe2441920 -/
section
                                                             

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle61FirstHomogeneous
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionProfile CenteredExceptionalProfile CenteredMomentLattice
local notation "O"=>HeckeFamily.O

open CenteredMomentEnergyReferenceReflection CenteredMomentFiniteProfileExceptional

theorem natural_reference_reflection_homogeneous (a b bΦ epsilon xi saving L:ℝ)
    (ha:0< a)(hb:0≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (B J:ℕ)(hB:2≤ B):
    ∃n:ℕ,∃S:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask:ℝ)(s:NaturalState Z Bmask bΦ)
        (Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(α:Type*)(F:Finset α)(pool:α→ Finset (Ideal O))
        (β:α→ Ideal O→ℂ)(P:α→ℝ)(u t along bshort E:ℝ),
      s.width≤ L+along → 0≤ E →
      (∀v:ℝ,∀j k:Fin 2,∀x∈Set.Icc 0 (max 0 (s.width-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
          (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (naturalCharacter s.character z) false (scaleTest Wshort k)
            (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
          ≤ E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong
          (Z^along) 0 u *
          polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
          ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖u‖)^(2*n)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)^2*(1+‖u‖)^(2*n)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort
            (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨H,C,D,hC,hD,h⟩:=CenteredMomentUniformRadialComparison.actual_original_radial_comparison
    epsilon ((fixedConductorFactor:ℝ)*bΦ) xi saving L hepsilon
    (mul_pos conductorFactor_pos hbΦ) hxi B J hB
  obtain ⟨n,T,Ct,hCt,hprofile⟩:=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha H
  let S:=T∪{(0,0)}
  have hS:(0,0)∈S:=by simp [S]
  refine ⟨n,S,C*Ct^2,D*Ct^2,by positivity,by positivity,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s Wlong Wshort hsLong hsShort α F pool β P u t along bshort E hlength hE hchildren
  by_cases hzero:sourceControl S Wlong=0
  · have hw:=sourceControl_zero S hS Wlong hzero
    subst Wlong
    simp [polynomial,summand,radialEnergy]
  have hpos:0< sourceControl S Wlong:=lt_of_le_of_ne (sourceControl_nonneg S Wlong) (Ne.symm hzero)
  let G:=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) u
  let Src:=Ct*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) Wlong)*(1+‖u‖)^n
  have hSrc:0< Src:=mul_pos (mul_pos hCt hpos) (by positivity)
  have hcontrol:sourceControl T Wlong≤ sourceControl S Wlong:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:T⊆T∪{(0,0)})) Wlong
  have hnorm:H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤ Src:=
    (hprofile Wlong hsLong u).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontrol hCt.le) (by positivity))
  obtain ⟨Pbound,hPbound,hbound⟩:=CenteredMomentCommonMaskRadialEnergy.slots_bounded F pool β P
  have hh:=hZ.2 (fun _=>G) (naturalCharacter s.character)
    (fun z=>∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
    (fun _=>t) (effectiveState s).radial.keep s.radial.profile s.radial.scale Pbound
    Wshort a b s.width along bshort E Src
    (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))
    s.radial.scale_pos s.radial.nonneg (fun z=>hbound _)
    (effective_character_nonprincipal s) hb hsShort (Wshort.smooth ⊤)
    hlength (effective_character_cap s hbΦ.le) hE hSrc (fun _ _=>hnorm)
    (le_max_left _ _) (fun z hz=>(effective_character_cap s hbΦ.le z hz).trans (le_max_right _ _))
    hchildren
  have hG:(G:ℝ→ℂ)=normPowerProfile Wlong a b ha hsLong (Wlong.smooth ⊤) u:=rfl
  simp only [hG,CenteredMomentNaturalMaskedFloor.twist_polynomial _ Wlong a b ha hsLong u] at hh
  apply hh.trans_eq
  dsimp only [Src]
  rw [show (1+‖u‖)^(2*n)=((1+‖u‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.Cycle61FirstHomogeneous

end

end OAI

/- Adapted from OpenAI/math family003 Energy/ReferenceHomogeneous.lean, Apache-2.0. Independent plain heights are retained. -/

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Homogeneous -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Reflection; sha256 e6674cdd5caa139bfda14e0ec386cd31e905ca53650e71e7477c828c728f30f6 -/
section
                                                  
                                                            
                                                 
                                                           

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle61FirstReflection
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open Cycle61FirstChildUniform CenteredMomentEnergyReferenceLowWindow
open Cycle61FirstHomogeneous CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem reference_from_positive
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Wslot:ℝ→ℂ)(bslot Bmask L Lslot lo hi Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤ Bmask →
      ∀(F:Finset α)(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤ Lreflect+along →
      max 0 (s.width-along+xi)≤ L → bshort≤ L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤ s.width →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 u *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
            ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
            (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  obtain ⟨n,T,Dchild,hDc,hchild⟩:=reflected_child_uniform_from_positive (α:=α) M H hH a b ha hlo hhi degree S
  obtain ⟨nlong,Slong,C,D,hC,hD,href⟩:=natural_reference_reflection_homogeneous
    a b bΦ epsilon xi saving Lreflect ha (by linarith) hbΦ hepsilon hxi B n hB
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity
  dsimp only
  apply hZ.2 Bmask s Wlong Wshort hsLong hsShort α F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t)
    (fun i=>Z^(w i)) u t along bshort _ hlength
  · have hz:0< Z:=zero_lt_one.trans hZ.1
    have hd:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl; positivity
    positivity
  · intro v j k x hx
    have hwindow:=reflection_window_length Z (max 0 (s.width-along+xi)) x hZ.1 (le_max_left _ _) hx
    exact hchild Wslot bslot bΦ Bmask L Lslot lo hi Mcap ε κ Z η₀ Q K hK hlow hBmask
      F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs Wshort hsShort
      j k v (Real.exp x) (Z^bshort) (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
      (hwindow.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.1.le hL))
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbshort)
      (by linarith [hwindow.1])

open Cycle61FirstReflection CenteredMomentEnergyReferenceLowError
theorem reference_from_positive_with_error
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Lreflect:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Bmask L Lslot Mcap ε κ:ℝ)
        (η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      0≤ Bmask →
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(along bshort:ℝ),s.width≤ Lreflect+along →
      max 0 (s.width-along+xi)≤ L → bshort≤ L →
      max 0 (s.width-along+xi)+length Z (Z^bshort)+6*κ*(∑i∈F,w i)≤ s.width →
      let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
        (1+|t|+height)^(degree+2*n)*Z^(s.width+ε);
      let β:=fun i I=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 u *
        polynomial (naturalCharacter s.character z) false Wshort (Z^bshort) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*
          (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^bshort)*∏i∈F,Z^(w i) :=by
  obtain ⟨Cerr,hCerr,herr⟩:=relative_slot_error Fmax Wslot aslot bslot lo hi b haslot hsSlot hcSlot
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_positive (α:=α) M H hH
    a b bΦ epsilon xi saving Lreflect ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D*Cerr,hC,mul_pos hD hCerr,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask
    F hF θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity
  dsimp only
  have hh:=hZ.2 Wslot bslot Bmask L Lslot lo hi Mcap ε κ η₀ Q K hK hlow hBmask
    F θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    Wlong Wshort hsLong hsShort along bshort hlength hL hbshort hcapacity
  dsimp only at hh
  have he:=herr F hF Wshort (fun x hx=>(hsShort hx).2)
    (naturalCharacter s.character) (fun i=>relativeCharacter M H hH η₀ (θ i))
    (fun i=>primePool M H bslot (Z^(w i))) (fun i=>Z^(w i)) σ freq t
    (Z^bshort) s.radial.scale s.radial.profile (effectiveState s).radial.keep
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) s.radial.scale_pos
    (fun i _=>Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _)
    (fun i _=>hσlo i) (fun i _=>hσhi i)
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1) s.radial.nonneg
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hcoeff:0≤ D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
      (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving):=by positivity
  apply hh.trans
  apply add_le_add le_rfl
  convert mul_le_mul_of_nonneg_left he hcoeff using 1 ; ring


end SevenEighths.Cycle61FirstReflection

end

end OAI

/- Adapted from OpenAI/math family003 Energy/ReferenceLowReflection.lean, Apache-2.0.
The terminal is applied only to daughters satisfying their own old capacity. -/

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Reflection -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Zero; sha256 f6d5bb3999fbee170702970f73a4e60c222678e0440b4b384e641ee2a9cf3640 -/
section
                                                                 
                                                           

namespace OAI.SevenEighths.Cycle61FirstZero
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

omit [DecidableEq ι] in
/-- The first zero frequency uses the actual centered equal-product coefficient,
its literal volume, masks and all Schwartz profiles. The constant precedes every
live input and profile; independent input heights are retained inside those profiles.
This is the original powerful-product zero estimate, not a count hypothesis. -/
theorem actual_first_zero_frequency (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀Z:ℝ,1≤ Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→ s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→ volume s.toData≤ Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤ K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε := by
  exact CenteredMomentSourceInputZeroUniform.first_input_zero_capped
    hi wlo whi B ε hhi hwlo hwhi hB hε

/-- The artificial smooth-ball zero remains unamplified. Its genuine mask factor
is `-s₀`; the bound is on the actual finite Gauss zero with the original coefficient.
The support and coefficient norm gates are structural finite-source gates. -/
theorem actual_unamplified_added_zero {α : Type*} (A : Finset α) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : Finset α), J ⊆ A →
      ∀ (c : O), c ≠ 0 → ∀ (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
      (R : Ideal O) (t : ℝ) (ν : α → Ideal O → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ)
      (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O), Squarefree s →
      ∀ (Bslot : α → ℝ) (B₁ B₂ : ℝ),
      (∀ j ∈ J, 0 ≤ Bslot j) → 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ j ∈ J, ∀ I, ‖ν j I‖ ≤ 1) → (∀ j ∈ J, ∀ x, ‖Wslot j x‖ ≤ Bslot j) →
      (∀ x, ‖W₁ x‖ ≤ B₁) → (∀ x, ‖W₂ x‖ ≤ B₂) →
      ∀ (S : Finset (Tuple J)) (hS : ∀ v ∈ S, Supported (finiteTupleProduct v))
      (Z a s₀ θ : ℝ), 1 < Z → Z ^ s₀ ≤ (Ideal.absNorm s : ℝ) →
      (∀ v ∈ S, (Ideal.absNorm (finiteTupleProduct v) : ℝ) ≤ Z ^ (a + θ)) →
      ‖(Real.sqrt (Z ^ a) : ℂ)⁻¹ * finiteGaussZero S hS
        (originalFiniteCoefficient c χ R t (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ b₁ b₂ s)‖ ^ 2 ≤
        C * ((∏ j ∈ J, Bslot j) * (2 * B₁ * B₂)) ^ 2 *
          Z ^ (a - s₀ + 2 * θ + ε * (a + θ))  := by
  exact CenteredMomentAddedZeroUniform.original_subset_source_energy A ε hε


omit [DecidableEq ι] in
/-- First zero terminal at the actual positive physical radius, including a
negative radius exponent. This is an actual normalized energy estimate. -/
theorem actual_first_zero_at_physical_radius (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤ hi i)(hwlo:0< wlo)(hwhi:0≤ whi)(hB:0≤ B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧ ∀Z:ℝ,1≤ Z→
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→ s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤ hi i)→ volume s.toData≤ Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(Mrow:ℝ),
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ (Z^Mrow)‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(Mrow+ε) := by
  obtain ⟨SΦ,C,hC,hb⟩ := actual_first_zero_frequency hi wlo whi B ε hhi hwlo hwhi hB hε
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ Mrow
  have hh := hb Z hZ s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ
    (Z^Mrow) (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  rw [Real.rpow_add (zero_lt_one.trans_le hZ)]
  simpa only [mul_assoc] using hh
end
end OAI.SevenEighths.Cycle61FirstZero
#print axioms OAI.SevenEighths.Cycle61FirstZero.actual_first_zero_frequency
#print axioms OAI.SevenEighths.Cycle61FirstZero.actual_unamplified_added_zero

#print axioms OAI.SevenEighths.Cycle61FirstZero.actual_first_zero_at_physical_radius

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Zero -/
