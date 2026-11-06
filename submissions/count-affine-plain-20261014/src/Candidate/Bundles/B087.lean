/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B020
import Candidate.Bundles.B063
import Candidate.Bundles.B064
import Candidate.Bundles.B085
import Candidate.Bundles.B086
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.NaturalInputMatches
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Actual; sha256 850808a7d15c052ce77d61d0c8f85887265d675cecbb98d311f2f7fac4e4a2d9 -/
section
                                                
                                            
                                              
                              
                                          

namespace OAI.SevenEighths.Cycle61FirstActual
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentAllocatedNaturalRadial CenteredMomentSectorLocalization
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open Cycle61FirstReflection Cycle61FirstGeometry
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

/-- Actual comparison energy, with two independent plain heights and an explicit
arbitrarily decaying reflection tail. The old terminal is proved and instantiated
inside this theorem only at daughters; no old parent capacity hypothesis occurs. -/
theorem actual_reflected_comparison
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hWslot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (a b bΦ epsilon xi saving Bmask L Mcap ε:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hε:0<ε)(hL:Mcap+xi≤ L)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (B:ℕ)(hB:2≤ B):
    ∃degree:ℕ,
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
      ∃K:ℝ,0< K ∧ ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Cycle25.Energy.commonMesh Mcap Bmask L ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(Mrow along bshort:ℝ),0≤ Mrow → Mrow≤ s.width → Mrow/2≤ along →
      bshort≤ Mrow/4 → (∑i∈F,w i)≤ Mrow/25 → xi≤7*Mrow/100 →
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
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^bshort)*∏i∈F,Z^(w i)  := by
  obtain ⟨degree,S,hterminal⟩ := Cycle25.Energy.terminal_positive_at (α:=α)
    M H hH Wslot aslot bslot a b bΦ Bmask L lo hi Mcap (3/4) ε
    haslot hsSlot hWslot hbslot ha hlo hhi hbΦ hmask hMcap (by norm_num)
    (by norm_num) hε hbeta hκbeta
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩ :=
    reference_from_positive_with_error (α:=α) M H hH Fmax Wslot aslot bslot lo hi
      haslot hsSlot hWslot.continuous a b bΦ epsilon xi saving L ha hlo hhi
      hbΦ hepsilon hxi B hB degree S
  refine ⟨degree,n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨K,hK,ht⟩ := hterminal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [href,ht] with Z hZ htZ
  refine ⟨hZ.1,?_⟩
  intro F hF θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs Wlong Wshort hsLong hsShort Mrow along bshort hMr hMw hlong hshort hslots hpad
  have hMrCap : Mrow≤ Mcap := hMw.trans hs
  have hAlong : 0≤ along := by linarith
  have hLnonneg : 0≤ L := by linarith
  have hlength : s.width≤ L+along := by linarith
  have hwindow : max 0 (s.width-along+xi)≤ L := max_le hLnonneg (by linarith)
  have hbshort : bshort≤ L := by linarith
  have hcapacity := reflected_daughter_capacity Z Mrow s.width along bshort
    (∑i∈F,w i) xi hZ.1 hMr hMw hlong hshort hslots hxi.le hpad
  exact hZ.2 Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L ε) Mcap ε (3/4)
    η₀ Q K hK.le htZ.2 hmask F hF θ w σ freq u t height hw hwL hσlo hσhi
    hheight hfreq s hQ hs Wlong Wshort hsLong hsShort along bshort hlength hwindow
    hbshort (by convert hcapacity using 1; norm_num)


/-- Direct comparison daughters are controlled by the genuine original terminal.
The parent is permitted to lie beyond old capacity; the actual daughter alone is
bounded by the .25/.5/.04 geometry. Both plain heights are independent. -/
theorem actual_direct_comparison
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hWslot:ContDiff ℝ ∞ Wslot)(hbslot:0≤ bslot)
    (a b bΦ Bmask L Mcap ε:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hε:0<ε)(hL:Mcap≤ L)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),
      ∀η₀:Character,∀Q:Ideal O,Q≤ M → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
      ∃C:ℝ,0< C ∧ ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(F:Finset α)(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Cycle25.Energy.commonMesh Mcap Bmask L ε) →
      (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀(Mrow X₁ X₂:ℝ),0≤ Mrow → Mrow≤ s.width → 0< X₁ → 0< X₂ →
      X₁≤ Z^(Mrow/4) → X₂≤ Z^(Mrow/2) → (∑i∈F,w i)≤ Mrow/25 →
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      W₁ X₁ 0 u*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ u t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε) := by
  obtain ⟨degree,S,hterminal⟩ := Cycle25.Energy.terminal_positive_at (α:=α)
    M H hH Wslot aslot bslot a b bΦ Bmask L lo hi Mcap (3/4) ε
    haslot hsSlot hWslot hbslot ha hlo hhi hbΦ hmask hMcap (by norm_num)
    (by norm_num) hε hbeta hκbeta
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hterminal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro F θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq s hQ hs
    W₁ W₂ hs₁ hs₂ Mrow X₁ X₂ hMr hMw hX₁ hX₂ hc₁ hc₂ hslots
  have hcap := direct_daughter_capacity Z Mrow s.width X₁ X₂ (∑i∈F,w i)
    hZ.1 hMr hMw hc₁ hc₂ hslots
  have h₁ : X₁≤ Z^L := hc₁.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have h₂ : X₂≤ Z^L := hc₂.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  exact Cycle61FirstDirect.direct_child_from_positive M H hH Wslot bslot a b bΦ
    Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε (3/4) Z η₀ Q
    degree S C hZ.2 hmask ha F θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ h₁ h₂
    (by convert hcap using 1; norm_num)


/-- Exact original-row bridge at the initial unit puncture. It preserves the
literal two-plain normalizer, character, profile heights and slots. -/
theorem actual_unit_puncture_energy
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(hpuncture:s.puncture=1)(ha:0< a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→ Finset (Ideal O))(ν:α→ Character)
    (Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0< P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*
          HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale =
    energy s.character s.mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*
        HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  rw [independent_child_ray_energy s ha W₁ W₂ hs₁ hs₂ F pool ν Wslot P σ freq
    hp hP t t₁ t₂ X₁ X₂ hX₁ hX₂]
  unfold energy
  apply tsum_congr
  intro z
  by_cases hk:s.radial.keep z <;>
    by_cases hw:s.radial.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/s.radial.scale)=0 <;>
    simp [unpuncturedState,effectiveState,effectiveRadial,NaturalState.mask,hpuncture,hk,hw]

end
end OAI.SevenEighths.Cycle61FirstActual
#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_reflected_comparison

#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_direct_comparison

#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_unit_puncture_energy


-- The old terminal is an approved, independently certified daughter input. The
-- audit stops at that exact declaration when checking which comparison geometry
-- this new proof applies. The kernel axiom checks above traverse its full proof.
set_option maxHeartbeats 0 in
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``OAI.SevenEighths.Cycle61FirstActual.actual_reflected_comparison,
      ``OAI.SevenEighths.Cycle61FirstActual.actual_direct_comparison,
      ``OAI.SevenEighths.Cycle61FirstActual.actual_unit_puncture_energy,
      ``OAI.SevenEighths.Cycle61FirstZero.actual_first_zero_at_physical_radius,
      ``OAI.SevenEighths.Cycle61FirstZero.actual_unamplified_added_zero] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["CenteredMomentEnergyOriginalHighReflectionPower",
          "balanced_reference_geometry", "balanced_reflection_margins",
          "Cycle61Moment.InitialAffineAt", "Cycle61.Assembly.Final"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      if n == ``Cycle25.Energy.terminal_positive_at then continue
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle61.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    if root == ``OAI.SevenEighths.Cycle61FirstActual.actual_reflected_comparison then
      unless seen.contains ``Cycle25.Energy.terminal_positive_at &&
          seen.contains ``OAI.SevenEighths.CenteredMomentRetainedWeightedSource.actual_retained_weighted_energy &&
          seen.contains ``OAI.SevenEighths.Cycle61FirstGeometry.reflected_daughter_capacity do
        throwError "Genuine daughter terminal, retained analysis or new geometry missing"
    logInfo m!"{root}: {seen.size} project constants outside approved old terminal; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do
      throwError "Cycle61 FirstBranches dependency audit rejected {root}"

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Actual -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.FixedComparison; sha256 576e3d7aff4f1bd817632e4c347999fa82ddc21e43c79b0277b25a58af52351b -/
section
                                            
                                  
                                                                
                                                                

namespace OAI.SevenEighths.Cycle61FirstActual
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalRowSource CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyReferenceScalarReserve CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskEnergy
open Cycle61Moment Cycle61FirstGeometry
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Explicit reserve scalars depend only on the compact physical width interval
and the requested loss, before any ray, slot dictionary or anchor data. -/
def comparisonD (Mmax ε : ℝ) : ℝ := (ε/2)/(4*((2*Mmax+1)+2))
def comparisonXi (Mmin : ℝ) : ℝ := Mmin/100
def comparisonL (Mmin Mmax : ℝ) : ℝ := (2*Mmax+1)+comparisonXi Mmin+1
def comparisonMesh (Mmin Mmax ε : ℝ) : ℝ :=
  Cycle25.Energy.commonMesh (2*Mmax+1) 0 (comparisonL Mmin Mmax) (comparisonD Mmax ε)

lemma comparisonMesh_pos (Mmin Mmax ε : ℝ) (hmin : 0< Mmin) (hmax : Mmin≤ Mmax)
    (hε : 0<ε) : 0< comparisonMesh Mmin Mmax ε := by
  have hm := hmin.trans_le hmax
  unfold comparisonMesh
  apply Cycle25.Energy.commonMesh_pos
  · positivity
  · norm_num
  · unfold comparisonD; positivity

/-- The actual fixed-parent comparison cut. Its constants and derivative set are
chosen before the live anchor, row width, plain scales, profiles and heights.
The logarithmic conductor and arbitrarily decaying reflection tail are absorbed
into the requested loss. The original terminal is used only on daughters. -/
theorem actual_fixed_parent_comparison_fixed_mesh
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    0< comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (41/100)*M≤ n₁ → (41/100)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→ RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false (p.profile 1)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) 0 u *
      polynomial (naturalCharacter s.character z) false (p.profile 0) (comparisonFirst Z M) 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0< Mmax := hMmin.trans_le hMmax
  let Mcap := 2*Mmax+1
  have hCap : 0< Mcap := by dsimp [Mcap]; positivity
  let d := comparisonD Mmax ε
  let xi := comparisonXi Mmin
  let L := comparisonL Mmin Mmax
  let saving := 2*Mcap+2*Mcap*d+1
  have hd : 0< d := by dsimp [d,comparisonD]; positivity
  have hxi : 0< xi := by dsimp [xi,comparisonXi]; positivity
  have hLpos : 0≤ L := by dsimp [L,comparisonL]; positivity
  have hxirho : xi≤ Mmin/100 := le_rfl
  have hL : Mcap+0+xi≤ L := by dsimp [L,comparisonL,Mcap]; linarith
  have hmain : d*(0+Mcap+2)≤ε/2 := by
    dsimp [d,comparisonD,Mcap]
    have hp : 0<4*(2*Mmax+1+2) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have herr : 0*d+Mcap*(2*d)-2*saving+5*Mcap/4≤ε/2 := by
    dsimp [saving]
    nlinarith [mul_nonneg hCap.le hd.le]
  obtain ⟨Cscalar,hCs,hscalar⟩ := ledger_bound Mcap 0 bΦ L d saving (ε/2)
    hCap.le (by norm_num) hLpos hd hmain herr
  obtain ⟨degree,n,T,Dchild,hDc,nlong,Slong,Cref,Dref,hCr,hDr,href⟩ :=
    actual_reflected_comparison rayM H hH Fmax Wslot aslot bslot lo hi
      haslot hsSlot hWslot hbslot a b bΦ d xi saving 0 L Mcap d
      ha hlo hhi hbΦ hd hxi (by norm_num) hCap hd (by linarith) hbeta hκbeta 2 (by norm_num)
  obtain ⟨J,S,Cprofile,hCp,hprofile⟩ := reference_envelopes a b ha ∅ T Slong
    degree n nlong Cref Dchild Dref hCr hDc hDr
  let delta := min 1 (ε/(2*Mmax))
  have hdelta : 0< delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta≤1 := min_le_left _ _
  have hdε : delta*Mmax≤ε/2 := by
    have hd' := min_le_right (1:ℝ) (ε/(2*Mmax))
    have hh := mul_le_mul_of_nonneg_right hd' hMax.le
    dsimp only [delta]
    field_simp at hh ⊢
    nlinarith
  refine ⟨comparisonMesh_pos Mmin Mmax ε hMmin hMmax hε, J,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨K,hK,ht⟩ := href η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cprofile*Cscalar*(K+1),by positivity,?_⟩
  filter_upwards [ht,fixed_anchor_width_uniform anchors Mmin delta hMmin hdelta] with Z hz hanchor
  refine ⟨hz.1,?_⟩
  intro j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ w σ freq
    u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hwanchor := hanchor.2 j M hmin
  have hs : s.width≤ Mcap := by
    have hh := mul_le_mul_of_nonneg_right hd1 hM
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤ Mcap
    dsimp only [Mcap]; linarith
  have hwidth : s.width≤ M+ε/2 := by
    have hh := mul_le_mul_of_nonneg_left hmax hdelta.le
    change M+Real.logb Z ((anchors j).modulus.absNorm:ℝ)≤ M+ε/2
    linarith
  have hMw : M≤ s.width := by
    change M≤ M+s.characterWidth
    exact le_add_of_nonneg_right s.character_nonneg
  have hpad : xi≤7*M/100 := by linarith
  obtain ⟨hsecond,hlong,_⟩ := actual_comparison_powers Z M n₁ n₂ hZ hM hn₁ hn₂ hn₁' hn₂'
  have hh := hz.2 F hF θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
    s rfl hs (p.profile 1) (p.profile 0) (p.support 1) (p.support 0)
    M (n₁+n₂-M/4) (M/4) hM hMw hlong le_rfl hslots hpad
  dsimp only at hh
  let v := |u|+|t|
  have hv : 0≤ v := by dsimp [v]; positivity
  have hp := hprofile (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) v height hheight
  dsimp only at hp
  simp only [abs_of_nonneg hv] at hp
  simp only [v,←add_assoc] at hp
  change _ ∧ _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J ∧
    _ ≤ Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J at hp
  have hu : 1+‖u‖≤1+‖v‖ := by simp only [Real.norm_eq_abs,abs_of_nonneg hv]; dsimp [v]; linarith [abs_nonneg t]
  have ht' : 1+|t|+height≤1+|v|+height := by rw [abs_of_nonneg hv]; dsimp [v]; linarith [abs_nonneg u]
  let A := Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J
  let E := (K+1)*diagonalControl Φ*A
  have hdiag : 0≤ diagonalControl Φ := by unfold diagonalControl; positivity
  have hA : 0≤ A := by dsimp [A]; positivity
  have hE : 0≤ E := by dsimp [E]; positivity
  have hmain : Cref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
        (1+|t|+height)^(degree+2*n))≤ E := by
    have hp' : Cref*Dchild*(sourceControl Slong (p.profile 1))^2*
        (sourceControl T (p.profile 0))^2*(1+‖u‖)^(2*nlong)*
        (1+|t|+height)^(degree+2*n)≤ A := by
      apply le_trans _ hp.2.1
      gcongr
      linarith [abs_nonneg u,abs_nonneg t]
    have hmul := mul_le_mul_of_nonneg_left hp' (mul_nonneg hK.le hdiag)
    have hk : K*diagonalControl Φ*A≤ E := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul_of_nonneg_right (by linarith) hdiag
    apply le_trans _ hk
    convert hmul using 1; ring
  have herr : Dref*(sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*diagonalControl Φ≤ E := by
    have hp' : Dref*(sourceControl Slong (p.profile 1))^2*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*(1+‖u‖)^(2*nlong)≤ A := by
      apply le_trans _ hp.2.2
      gcongr
    have hmul := mul_le_mul_of_nonneg_left hp' hdiag
    have hk : diagonalControl Φ*A≤ E := by
      calc
        _ = 1*diagonalControl Φ*A := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hdiag) hA
    apply le_trans _ hk
    convert hmul using 1; ring
  have hsum : (∑i : F,w i)≤ Mcap := by
    rw [Finset.sum_coe_sort]
    linarith
  have hledger := hscalar Z hZ.le s hs F (fun i => w i) hsum
  have hrad : (s.puncture.radical.absNorm:ℝ)^d=1 := by
    change (((1:Ideal O).radical).absNorm:ℝ)^d=1
    simp [Ideal.radical_top,Ideal.absNorm_top]
  rw [hrad,one_mul] at hledger
  rw [Finset.prod_coe_sort F (fun i => Z^(w i))] at hledger
  have hlog : 0≤ Real.log Z := (Real.log_pos hZ).le
  have hL0 : 0≤ L := by linarith
  have hwindow : max 0 (s.width-(n₁+n₂-M/4)+xi)≤ L := max_le hL0 (by linarith)
  have hshort : Z^(M/4)≤ Z^(s.width/4) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  let P := Z^(s.width+d)
  let Qmain := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
    (1+2*(L*Real.log Z))*P
  let Qerror := (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i∈F,Z^(w i))
  have hP : 0≤ P := by dsimp [P]; positivity
  have hQm : 0≤ Qmain := by dsimp [Qmain]; positivity
  have hQe : 0≤ Qerror := by dsimp [Qerror]; positivity
  have htotal : _ ≤ E*Qmain+E*Qerror := add_le_add
    (mul_le_mul_of_nonneg_right hmain hQm) (mul_le_mul_of_nonneg_right herr hQe)
  have hbound : E*Qmain+E*Qerror ≤ E*(P+Qmain+Qerror) := by nlinarith only [mul_nonneg hE hP]
  have hlast := mul_le_mul_of_nonneg_left hledger hE
  dsimp only
  rw [hsecond]
  change _ ≤ _ at hh
  apply hh.trans
  apply le_trans _ (le_trans htotal (le_trans hbound (hlast.trans ?_)))
  · dsimp [Qmain,Qerror,P]
    calc
      _ ≤ Cref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl Φ*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+d)) +
        Dref*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*
          (sourceControl Slong (p.profile 1))^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
          diagonalControl Φ*max 1 s.radial.scale*Z^(s.width/4)*(∏i∈F,Z^(w i)) := by
        gcongr <;> rfl
      _ = _ := by simp only [Real.norm_eq_abs,schwartzSeminormFamily]; ring
  · dsimp [E,A]
    have hzpow := Real.rpow_le_rpow_of_exponent_le hZ.le (show s.width+ε/2≤ M+ε by linarith)
    have hm := mul_le_mul_of_nonneg_left hzpow
      (show 0≤(K+1)*diagonalControl Φ*(Cprofile*(p.control S)^2*(1+|u|+|t|+height)^J)*Cscalar by positivity)
    convert hm using 1 <;> ring

theorem actual_fixed_parent_comparison
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃mesh : ℝ, 0< mesh ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (41/100)*M≤ n₁ → (41/100)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→ RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false (p.profile 1)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) 0 u *
      polynomial (naturalCharacter s.character z) false (p.profile 0) (comparisonFirst Z M) 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hm,J,S,hbound⟩ := actual_fixed_parent_comparison_fixed_mesh rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  exact ⟨comparisonMesh Mmin Mmax ε,hm,J,S,hbound⟩


/-- The same cut on the original squared row energy, with its literal mask and
normalizer. The two independent plain heights are carried by actual norm-power
profiles; slot heights are exactly t+freq. -/
theorem actual_fixed_parent_comparison_energy
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃mesh : ℝ, 0< mesh ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (41/100)*M≤ n₁ → (41/100)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→ RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀u t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    energy s.character s.mask 1 0
      ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 0)
      ((independentProfiles ha (p.profile 1) (p.profile 0) (p.support 1) (p.support 0) u t).profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (t+freq i) I)
      (fun i:F => Z^(w i)) (comparisonSecond Z M (Z^n₁) (Z^n₂))
      (comparisonFirst Z M) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|u|+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨mesh,hmesh,degree,S,hbound⟩ := actual_fixed_parent_comparison rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  refine ⟨mesh,hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ w σ freq
    u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hh := hz.2 j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ
    w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  have hX₁ : 0< comparisonSecond Z M (Z^n₁) (Z^n₂) := by
    unfold comparisonSecond comparisonFirst
    positivity
  have hX₂ : 0< comparisonFirst Z M := by unfold comparisonFirst; positivity
  have heq := actual_unit_puncture_energy s rfl ha (p.profile 1) (p.profile 0)
    (p.support 1) (p.support 0) F (fun i => primePool rayM H bslot (Z^(w i)))
    (fun i => relativeCharacter rayM H hH η₀ (θ i)) (fun _ => Wslot)
    (fun i => Z^(w i)) σ freq
    (by intro i _ I hI; exact (Finset.mem_filter.mp hI).2.1)
    (by intro i _; positivity) t u t
    (comparisonSecond Z M (Z^n₁) (Z^n₂)) (comparisonFirst Z M) hX₁ hX₂
  dsimp only at hh ⊢
  exact heq.symm.trans_le hh

end
end OAI.SevenEighths.Cycle61FirstActual
#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_comparison

#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_comparison_energy

-- The audited old terminal is permitted only as a daughter bound. Its entire
-- proof is traversed by the kernel axiom checks above.
set_option maxHeartbeats 0 in
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_comparison,
      ``OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_comparison_energy] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["CenteredMomentEnergyOriginalHighReflectionPower",
          "balanced_reference_geometry", "balanced_reflection_margins",
          "Cycle61Moment.InitialAffineAt", "Cycle61.Assembly.Final"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      if n == ``Cycle25.Energy.terminal_positive_at then continue
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle61.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    unless seen.contains ``Cycle25.Energy.terminal_positive_at &&
        seen.contains ``OAI.SevenEighths.Cycle61FirstActual.actual_reflected_comparison &&
        seen.contains ``OAI.SevenEighths.Cycle61Moment.fixed_anchor_width_uniform &&
        seen.contains ``OAI.SevenEighths.CenteredMomentRetainedWeightedSource.actual_retained_weighted_energy do
      throwError "Actual reflection, finite anchor threshold or daughter analysis missing"
    if root == ``OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_comparison_energy then
      unless seen.contains ``OAI.SevenEighths.Cycle61FirstActual.actual_unit_puncture_energy do
        throwError "Literal original energy bridge missing"
    logInfo m!"{root}: {seen.size} project constants outside approved daughter terminal; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do
      throwError "Cycle61 fixed parent comparison dependency audit rejected {root}"

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.FixedComparison -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.RawComparison; sha256 6572895a4eaded4942f52ee64f100be052c9e934f8e4ac4488b8af293c6f7aac -/
section
                                                     

namespace OAI.SevenEighths.Cycle61FirstActual
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open Filter Cycle61Moment
open CenteredMomentPrimeSlot
open QuadraticInitialBound
open CenteredMomentEnergyReferenceState
open CenteredMomentEnergyState CenteredMomentEnergyReferenceChild
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentInductionEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalMaskedFloor
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma polynomial_excluded_one (χ : Character) (W : ℝ→ℂ) (X σ t : ℝ) :
    polynomial (excluded χ 1) false W X σ t = polynomial χ false W X σ t := by
  simp only [polynomial,summand,coefficient,Bool.false_eq_true,ite_false,excluded_one_ideal]

lemma naturalSlot_excluded_one (χ : Character) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (P : ℝ) : naturalSlot (excluded χ 1) pool β P=naturalSlot χ pool β P := by
  simp only [naturalSlot,excluded_one_ideal]

/-- Exact raw-height bridge for the literal original unit-puncture energy. -/
theorem actual_raw_radial_energy {α : Type*} [Fintype α] [DecidableEq α]
    {Z bΦ a b : ℝ} (s : NaturalState Z 0 bΦ) (hs : s.puncture=1) (ha : 0< a)
    (p : Profiles a b) (pool : α→ Finset (Ideal O)) (β : α→ Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0< P i) (t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) :
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1) pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale =
    radialEnergy (fun z => polynomial (naturalCharacter s.character z) false (p.profile 0) X₁ 0 t *
      polynomial (naturalCharacter s.character z) false (p.profile 1) X₂ 0 t *
      ∏i,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale := by
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : s.radial.keep z
  · have hz := s.row_ne_zero z hk
    have he := original_positive_normalized (naturalRow s.character z hz) 1 one_ne_zero
      (p.profile 0) (p.profile 1) a b a b ha ha (p.support 0) (p.support 1)
      ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤) pool β P hP t X₁ X₂ hX₁ hX₂
    simp only [polynomial_excluded_one,naturalSlot_excluded_one,twist_polynomial] at he
    have hn := congrArg (fun c : ℂ => ‖c‖^2) he
    simp only [norm_mul,mul_pow,positive_height_phase_norm X₁ t hX₁,
      positive_height_phase_norm X₂ t hX₂,one_mul] at hn
    by_cases hw : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [effectiveState,effectiveRadial,hk,hw]
    · simp only [effectiveState,effectiveRadial,hk,true_and,ite_true,
        naturalCharacter_eq s.character z hz,NaturalState.mask,hs]
      rw [ite_eq_left (by exact hw)]
      simp only [norm_mul,mul_pow]
      exact congrArg (fun x : ℝ => x*(s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re) hn
  · simp [effectiveState,effectiveRadial,hk]

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Literal original comparison energy at the common raw plain height. -/
theorem actual_fixed_parent_raw_comparison_fixed_mesh
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    0< comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (41/100)*M≤ n₁ → (41/100)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→ RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirst Z M)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hmesh,degree,S,hbound⟩ := actual_fixed_parent_comparison_fixed_mesh rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  refine ⟨hmesh,degree,S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hbound η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C*2^degree,by positivity,?_⟩
  filter_upwards [ht] with Z hz
  refine ⟨hz.1,?_⟩
  intro j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ w σ freq
    t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  have hh := hz.2 j M n₁ n₂ hmin hmax hn₁ hn₂ hn₁' hn₂' Φ hsΦ hpΦ p F hF θ
    w σ freq t t height hw hwmesh hσlo hσhi hheight hfreq hslots hZ hM
  have hX₁ : 0< comparisonFirst Z M := by unfold comparisonFirst; positivity
  have hX₂ : 0< comparisonSecond Z M (Z^n₁) (Z^n₂) := by
    unfold comparisonSecond comparisonFirst
    positivity
  have heq := actual_raw_radial_energy s rfl ha p
    (fun i:F => primePool rayM H bslot (Z^(w i)))
    (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i:F => Z^(w i)) (by intro i; positivity) t
    (comparisonFirst Z M) (comparisonSecond Z M (Z^n₁) (Z^n₂)) hX₁ hX₂
  have hbridge : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirst Z M)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*
      (1+|t|+|t|+height)^degree*Z^(M+ε) := by
    apply heq.trans_le
    convert hh using 1
    congr 1
    funext z
    rw [Finset.prod_coe_sort F (fun i => naturalSlot (naturalCharacter s.character z)
      (primePool rayM H bslot (Z^(w i)))
      (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))]
    ring
  apply hbridge.trans
  have hp : (1+|t|+|t|+height)^degree≤(2*(1+|t|+height))^degree :=
    pow_le_pow_left₀ (by positivity) (by linarith) degree
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hdom := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show 0≤ C*diagonalControl Φ*(p.control S)^2 by positivity))
    (show 0≤ Z^(M+ε) by positivity)
  apply hdom.trans_eq
  rw [mul_pow]
  ring

theorem actual_fixed_parent_raw_comparison
    {Label : Type*} [Fintype Label] (anchors : Label → Character)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ Mmin Mmax ε : ℝ) (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b)
    (hbΦ : 0< bΦ) (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃mesh : ℝ, 0< mesh ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀M n₁ n₂ : ℝ, Mmin≤ M → M≤ Mmax →
      (41/100)*M≤ n₁ → (41/100)*M≤ n₂ → n₁≤(44/100)*M → n₂≤(44/100)*M →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b,
    ∀F : Finset α, F⊆Fmax → ∀θ : α→ RayQuotient.Characters rayM H,
    ∀w σ freq : α→ℝ, ∀t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → (∑i∈F,w i)≤ M/25 →
    ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:F => primePool rayM H bslot (Z^(w i)))
      (fun (i:F) I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
      (fun i:F => Z^(w i)) (comparisonFirst Z M)
      (comparisonSecond Z M (Z^n₁) (Z^n₂)) s.radial.keep Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨hm,J,S,hbound⟩ := actual_fixed_parent_raw_comparison_fixed_mesh rayM H hH anchors
    Fmax Wslot aslot bslot lo hi haslot hsSlot hWslot hbslot a b bΦ Mmin Mmax ε
    ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  exact ⟨comparisonMesh Mmin Mmax ε,hm,J,S,hbound⟩

end
end OAI.SevenEighths.Cycle61FirstActual
#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_raw_radial_energy

#print axioms OAI.SevenEighths.Cycle61FirstActual.actual_fixed_parent_raw_comparison

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.RawComparison -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialSourceReduction; sha256 6d49adadf25dc584a9066c8490fd220569527cb908fe37c4005b556f4f1a3b38 -/
section
                                                   
                                                             
                                                              
                                           
                                                                

namespace OAI.SevenEighths.Cycle61InitialSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyOriginalSource
open CenteredMomentCommonRadialData CenteredMomentFirstSourceReduction
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentSourceInputTailUniform CenteredMomentNaturalFixedRaySource
open Cycle61Moment Cycle61FirstActual CenteredMomentEnergyOriginalProfileControl
open CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Actual equal-product source at the physical row width M, rather than the
larger conductor width recorded by NaturalState. -/
def affineInput (η₀ : Character) (θ : ι→ RayQuotient.Characters rayM H)
    (W : ℝ→ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ) (haslot : 0< aslot)
    (hWs : Function.support W⊆Set.Icc aslot bslot)
    (w σ v : ι→ℝ) (hσ : ∀i,σ i∈Set.Icc lo hi)
    {Z bΦ a b : ℝ} (s : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0< a)
    (M t X₁ X₂ : ℝ) (hX₁ : 0< X₁) (hX₂ : 0< X₂) : Input ι :=
  CenteredMomentEnergyNaturalInputMatches.input rayM H hH η₀ θ W hW aslot bslot lo hi
    haslot hWs w σ v hσ s p ha t X₁ X₂
    (comparisonFirst Z M) (comparisonSecond Z M X₁ X₂) hX₁ hX₂
    (comparison_positive Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z M X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

omit [DecidableEq ι] in
lemma affine_volume_bound (Z M Mmax X₁ X₂ : ℝ) (w : ι→ℝ)
    (hZ : 1< Z) (hM : 0≤ M) (hmax : M≤ Mmax) (_hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hn₁ : length Z X₁≤(44/100)*M) (hn₂ : length Z X₂≤(44/100)*M)
    (hslots : (∑i,w i)≤ M/25) : X₁*X₂*(∏i,Z^(w i))≤ Z^(Mmax+1) := by
  have hz := zero_lt_one.trans hZ
  have hx (X : ℝ) : X≤ Z^(length Z X) := by
    rw [length,Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _ ≤ Z^(length Z X₁)*Z^(length Z X₂)*(∏i,Z^(w i)) := by
      gcongr
      · exact hx X₁
      · exact hx X₂
    _ = Z^(length Z X₁+length Z X₂+∑i,w i) := by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

lemma fixed_inverse_scale_bound (Z M Mmax : ℝ) (hZ : 1< Z) (hM : 0≤ M)
    (hmax : M≤ Mmax) : (Z^M)⁻¹≤ Z^(Mmax+1) := by
  have hZpow := Real.one_le_rpow hZ.le hM
  have hinv : (Z^M)⁻¹≤1 := inv_le_one_of_one_le₀ hZpow
  exact hinv.trans (Real.one_le_rpow hZ.le (by linarith))

lemma initial_scale_exact (Z X M : ℝ) (hZ : 1< Z) (hM : 0< M)
    (hlo : (41/100)*M≤ length Z X) : X=Z^(length Z X) := by
  have hx : 1< X := by
    by_contra h
    have he : length Z X=0 := by simp only [length,max_eq_left (le_of_not_gt h),Real.logb_one]
    linarith
  rw [length,max_eq_right hx.le,Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (zero_lt_one.trans hx)]

/-- One actual radial majorant and remainder constant work for every live finite
slot subset. Fixed Ψ seminorms are absorbed before any live input is chosen. -/
theorem uniform_original_reduction {α : Type*} [Fintype α] [DecidableEq α]
    (bΦ bslot a b B ε ξ saving : ℝ)
    (hbΦ : 0< bΦ) (hbslot : 0≤ bslot) (ha : 0< a) (hb : 0≤ b)
    (hB : 0≤ B) (hε : 0<ε) (hξ : 0<ξ) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃D : ℝ, 0< D ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀T : Finset α, ∀inp : Input T, ∀p : Profiles a b,
      inp.W₁=p.profile 0 → inp.W₂=p.profile 1 → (∀i,inp.hi i≤ bslot) →
    ∀R : Ideal O, ∀r : CenteredMomentRadialEligibleEnergy.Radial,
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume inp≤ Z^B → r.scale⁻¹≤ Z^B →
    energy inp.η (fixedBadMask*idealGenerator R) 1 inp.t inp.W₁ inp.W₂ inp.slots
      inp.toData.coefficient inp.P inp.X₁ inp.X₂ r.keep r.profile r.scale ≤
      2*diagonalControl r.profile*(
        physicalMass inp R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        D*(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*(Z^ε+Z^(-saving)))+
      2*energy inp.η (fixedBadMask*idealGenerator R) 1 inp.t inp.W₁ inp.W₂ inp.slots
        inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ r.keep r.profile r.scale := by
  obtain ⟨Ψ,hΨ,hΨpos,hmajor⟩ := CenteredMomentEnergyFixedRadialSource.fixed_source bΦ hbΦ
  have hred (T : Finset α) := original_first_physical_reduction (ι:=T)
    (fun _ => bslot) a b B ε ξ saving (fun _ => hbslot) ha hb hB hε hξ
  choose Sd St Cd Ct hCd hCt hred using hred
  let D := 1+∑T : Finset α,(Cd T*sourceControl (Sd T) Ψ+Ct T*sourceControl (St T) Ψ)
  have hterms (T : Finset α) : 0≤ Cd T*sourceControl (Sd T) Ψ+Ct T*sourceControl (St T) Ψ := by
    exact add_nonneg (mul_nonneg (hCd T).le (sourceControl_nonneg _ _))
      (mul_nonneg (hCt T).le (sourceControl_nonneg _ _))
  have hD : 0< D := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (fun T _ => hterms T)
    dsimp [D]; linarith
  refine ⟨Ψ,hΨ,hΨpos,D,hD,?_⟩
  filter_upwards [eventually_all.mpr hred,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro T inp p he₁ he₂ hhi R r hr hV hKi
  let : DecidableEq (T⊕Fin 2) := energyOriginalSourceDecidableSum
  have hh := (hz T).2 inp (p.profile 0) (p.profile 1) he₁ he₂ (p.support 0) (p.support 1)
    hhi fixedBadMask 1 (dvd_mul_right _ _) (dvd_mul_left _ _) R 1 Ψ r.scale r.scale_pos hV hKi
  have hdom := hmajor r.profile hr inp.η fixedBadMask 1 inp.t
    (CenteredMomentSourceMass.finiteColumns (Fintype.piFinset inp.pools))
    (CenteredMomentOriginalCommonHarmonic.coefficient inp R 1) r.scale r.scale_pos
  have hd := diagonalControl_nonneg r.profile
  have hcmp := positive_energy_comparison inp R r
  have hsum := Finset.single_le_sum (fun T _ => hterms T) (Finset.mem_univ T)
  have hCdD : Cd T*sourceControl (Sd T) Ψ≤ D := by
    dsimp [D]
    linarith [mul_nonneg (hCt T).le (sourceControl_nonneg (St T) Ψ)]
  have hCtD : Ct T*sourceControl (St T) Ψ≤ D := by
    dsimp [D]
    linarith [mul_nonneg (hCd T).le (sourceControl_nonneg (Sd T) Ψ)]
  have hbound := div_le_div_of_nonneg_right hdom
    (CenteredMomentAmplificationChildInput.volume_pos inp).le
  have hbound' := mul_le_mul_of_nonneg_left hh hd
  rw [mul_div_assoc] at hbound
  change _ ≤ diagonalControl r.profile * _ at hbound'
  apply hcmp.trans
  apply add_le_add _ le_rfl
  have hf := mul_le_mul_of_nonneg_left (hbound.trans hbound') (show (0:ℝ)≤2 by norm_num)
  simp only [mul_div_assoc]
  apply hf.trans
  have hscale := r.scale_pos
  have hZpos := zero_lt_one.trans hZ
  dsimp only [sourceControl] at hCdD hCtD
  have he : _ ≤ _ := add_le_add
    (mul_le_mul_of_nonneg_right hCdD (show 0≤(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*Z^ε by positivity))
    (mul_le_mul_of_nonneg_right hCtD (show 0≤(plainControl inp (p.profile 0) (p.profile 1))^2*r.scale*Z^(-saving) by positivity))
  have he' := mul_le_mul_of_nonneg_left (add_le_add_left he
    (physicalMass inp R 1 fixedBadMask 1 Ψ r.scale Z ξ/CenteredMomentAmplificationChildInput.volume inp))
    (show 0≤2*diagonalControl r.profile by positivity)
  simp only [CenteredMomentAmplificationChildInput.volume,
    CenteredMomentExceptionalAmplitudePair.volume] at he' ⊢
  convert he' using 1 <;> ring

/-- Extend live slot data only to use a fixed finite ambient dictionary. -/
def slotExtend {α : Type*} [DecidableEq α] {γ : Type*}
    (T : Finset α) (f : T→γ) (fallback : γ) (i : α) : γ :=
  if h : i∈T then f ⟨i,h⟩ else fallback

@[simp] lemma slotExtend_coe {α : Type*} [DecidableEq α] {γ : Type*}
    (T : Finset α) (f : T→γ) (fallback : γ) (i : T) :
    slotExtend T f fallback i=f i := by simp [slotExtend,i.property]

private lemma control_insert {a b : ℝ} (p : Profiles a b) (S : Finset (ℕ×ℕ)) :
    p.control S≤ p.control (insert (0,0) S) := by
  unfold Profiles.control
  exact mul_le_mul
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

/-- Actual initial affine energy reduced to its actual normalized physical mass.
All other terms are proved from the literal .41--.44 initial scales and the
original daughter terminal; no parent-capacity input is used. -/
theorem actual_initial_source_reduction_fixed_mesh {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (anchors : Label→ Character)
    (W : ℝ→ℂ) (aslot bslot lo hi a b bΦ Mmin Mmax ε ξ : ℝ)
    (haslot : 0< aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤ bslot) (hlohi : lo≤ hi)
    (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b) (hbΦ : 0< bΦ)
    (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε) (hξ : 0<ξ)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ 0< comparisonMesh Mmin Mmax ε ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀T : Finset α, ∀θ : T→ RayQuotient.Characters rayM H,
    ∀w σ freq : T→ℝ, ∀t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ comparisonMesh Mmin Mmax ε) → ∀hσlo : (∀i,lo≤σ i), ∀hσhi : (∀i,σ i≤ hi),
      0≤ height → (∀i,|freq i|≤ height) →
    ∀M : ℝ, Mmin≤ M → M≤ Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b, ∀X₁ X₂ : ℝ,
    ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
      (41/100)*M≤ length Z X₁ → length Z X₁≤(44/100)*M →
      (41/100)*M≤ length Z X₂ → length Z X₂≤(44/100)*M →
      (∑i,w i)≤ M/25 → ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂;
    energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp)+
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  have hMax : 0< Mmax := hMmin.trans_le hMmax
  obtain ⟨Ψ,hΨ,hΨpos,D,hD,hred⟩ := uniform_original_reduction (α:=α)
    bΦ bslot a b (Mmax+1) (ε/2) ξ 1 hbΦ hbslot ha (by linarith)
    (by linarith) (by positivity) hξ
  obtain ⟨hmesh,degree,S,hcomp⟩ := actual_fixed_parent_raw_comparison_fixed_mesh rayM H hH anchors
    (Finset.univ:Finset α) W aslot bslot lo hi haslot hWs hW hbslot
    a b bΦ Mmin Mmax ε ha hlo hhi hbΦ hMmin hMmax hε hbeta hκbeta
  let mesh := comparisonMesh Mmin Mmax ε
  let G := (CenteredMomentEnergyNaturalInputMatches.profileBound W hW.continuous
    aslot bslot lo hi haslot hWs)^(2*Fintype.card α)
  have hG : 0≤ G := pow_nonneg (zero_le_one.trans
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)) _
  refine ⟨Ψ,hΨ,hΨpos,hmesh,degree,insert (0,0) S,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,ht⟩ := hcomp η₀ Q hQM hQ0 hQt hQ72
  refine ⟨4*D*G+2*C,by positivity,?_⟩
  filter_upwards [ht,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro j T θ w σ freq t height hw hwmesh hσlo hσhi hheight hfreq M hmin hmax
    Φ hsΦ hpΦ p X₁ X₂ hX₁ hX₂ hn₁ hn₁' hn₂ hn₂' hslots hZ hM
  let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ
  let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂
  have hv : CenteredMomentAmplificationChildInput.volume inp≤ Z^(Mmax+1) :=
    affine_volume_bound Z M Mmax X₁ X₂ w hZ hM hmax hX₁ hX₂ hn₁' hn₂' hslots
  have hred' := hr.2 T inp p rfl rfl (fun _=>le_rfl) 1 s.radial hsΦ hv
    (fixed_inverse_scale_bound Z M Mmax hZ hM hmax)
  have hn₁eq := initial_scale_exact Z X₁ M hZ (hMmin.trans_le hmin) hn₁
  have hn₂eq := initial_scale_exact Z X₂ M hZ (hMmin.trans_le hmin) hn₂
  let we := slotExtend T w 0
  let se := slotExtend T σ lo
  let ve := slotExtend T freq 0
  have hew (i : α) : 0≤ we i := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hw ⟨i,h⟩
    · exact le_rfl
  have hewm (i : α) : we i≤ mesh := by
    dsimp [we,slotExtend]; split_ifs with h
    · exact hwmesh ⟨i,h⟩
    · exact hmesh.le
  have heslo (i : α) : lo≤ se i := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσlo ⟨i,h⟩
    · exact le_rfl
  have heshi (i : α) : se i≤ hi := by
    dsimp [se,slotExtend]; split_ifs with h
    · exact hσhi ⟨i,h⟩
    · exact hlohi
  have hev (i : α) : |ve i|≤ height := by
    dsimp [ve,slotExtend]; split_ifs with h
    · exact hfreq ⟨i,h⟩
    · simpa only [abs_zero] using hheight
  have hesum : (∑i∈T,we i)≤ M/25 := by
    rw [←Finset.sum_coe_sort T we]
    simpa only [we,slotExtend_coe] using hslots
  have hc := hz.2 j M (length Z X₁) (length Z X₂) hmin hmax hn₁ hn₂ hn₁' hn₂'
    Φ hsΦ hpΦ p T (Finset.subset_univ _) (slotExtend T θ 1) we se ve t height
    hew hewm heslo heshi hheight hev hesum hZ hM
  simp only [we,se,ve,slotExtend_coe,←hn₁eq,←hn₂eq] at hc
  have hplain : (plainControl inp (p.profile 0) (p.profile 1))^2≤
      G*(p.control (insert (0,0) S))^2 := plain_control_sq_le inp p S (Fintype.card α) _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW.continuous
      aslot bslot lo hi haslot hWs)
    (by simpa using Finset.card_le_univ T) (fun _=>le_rfl)
  have hpc := pow_le_pow_left₀ (p.control_nonneg S) (control_insert p S) 2
  have hdiag := diagonalControl_nonneg Φ
  have hheight1 : 1≤(1+|t|+height)^degree := one_le_pow₀ (by linarith [abs_nonneg t])
  have hpowers : (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ)))≤2*Z^(M+ε) := by
    have hterm (e : ℝ) (he : e≤ε) : Z^M*Z^e≤ Z^(M+ε) := by
      rw [←Real.rpow_add (zero_lt_one.trans hZ)]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    nlinarith [hterm (ε/2) (by linarith),hterm (-1) (by linarith)]
  have hrem : 2*diagonalControl Φ*(D*(plainControl inp (p.profile 0) (p.profile 1))^2*
      (Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))≤
      4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    calc
      _ ≤ 2*diagonalControl Φ*(D*(G*(p.control (insert (0,0) S))^2)*
          (2*Z^(M+ε))) := by
        have hh := mul_le_mul (mul_le_mul_of_nonneg_left hplain hD.le) hpowers
          (show 0≤ Z^M*(Z^(ε/2)+Z^(-(1:ℝ))) by positivity)
          (show 0≤ D*(G*(p.control (insert (0,0) S))^2) by positivity)
        have hh' := mul_le_mul_of_nonneg_left hh
          (show 0≤2*diagonalControl Φ from mul_nonneg (by norm_num) hdiag)
        convert hh' using 1; ring
      _ ≤ _ := by
        have hh := le_mul_of_one_le_right
          (show 0≤4*D*G*diagonalControl Φ*(p.control (insert (0,0) S))^2*Z^(M+ε) by positivity) hheight1
        convert hh using 1 <;> ring
  have hc' := mul_le_mul_of_nonneg_left hc (show (0:ℝ)≤2 by norm_num)
  have hcomparison : 2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M)≤
      2*C*diagonalControl Φ*(p.control (insert (0,0) S))^2*
        (1+|t|+height)^degree*Z^(M+ε) := by
    apply hc'.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpc (mul_nonneg hC.le hdiag))
        (show 0≤(1+|t|+height)^degree by positivity))
      (show 0≤ Z^(M+ε) by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤2 by norm_num)
    convert hh' using 1; ring
  change _ ≤ 2*diagonalControl Φ*(
      physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp+
      D*(plainControl inp (p.profile 0) (p.profile 1))^2*(Z^M)*(Z^(ε/2)+Z^(-(1:ℝ))))+
    2*energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots
      inp.toData.coefficient inp.P inp.Y₁ inp.Y₂ s.radial.keep Φ (Z^M) at hred'
  apply hred'.trans
  change 2*diagonalControl Φ*(_+_)+_≤ _
  rw [mul_add]
  have hh := add_le_add_left (add_le_add hrem hcomparison)
    (2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
      CenteredMomentAmplificationChildInput.volume inp))
  convert hh using 1 <;> ring

theorem actual_initial_source_reduction {α Label : Type*} [Fintype α] [DecidableEq α]
    [Fintype Label] (anchors : Label→ Character)
    (W : ℝ→ℂ) (aslot bslot lo hi a b bΦ Mmin Mmax ε ξ : ℝ)
    (haslot : 0< aslot) (hWs : Function.support W⊆Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤ bslot) (hlohi : lo≤ hi)
    (ha : 0< a) (hlo : a≤1/4) (hhi : 1≤ b) (hbΦ : 0< bΦ)
    (hMmin : 0< Mmin) (hMmax : Mmin≤ Mmax) (hε : 0<ε) (hξ : 0<ξ)
    (hbeta : (51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃Ψ : 𝓢(ℝ,ℂ), Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∃mesh : ℝ, 0< mesh ∧ ∃degree : ℕ, ∃S : Finset (ℕ×ℕ),
    ∀η₀ : Character, ∀Q : Ideal O, Q≤ rayM → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤ Ideal.span {(72:O)} →
    ∃C : ℝ, 0< C ∧ ∀ᶠ Z : ℝ in atTop, 1< Z ∧
    ∀j : Label, ∀T : Finset α, ∀θ : T→ RayQuotient.Characters rayM H,
    ∀w σ freq : T→ℝ, ∀t height : ℝ,
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → ∀hσlo : (∀i,lo≤σ i), ∀hσhi : (∀i,σ i≤ hi),
      0≤ height → (∀i,|freq i|≤ height) →
    ∀M : ℝ, Mmin≤ M → M≤ Mmax →
    ∀Φ : 𝓢(ℝ,ℂ), ∀hsΦ : Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ,
    ∀hpΦ : ∀x,0≤(Φ x).re, ∀p : Profiles a b, ∀X₁ X₂ : ℝ,
    ∀hX₁ : 0< X₁, ∀hX₂ : 0< X₂,
      (41/100)*M≤ length Z X₁ → length Z X₁≤(44/100)*M →
      (41/100)*M≤ length Z X₂ → length Z X₂≤(44/100)*M →
      (∑i,w i)≤ M/25 → ∀hZ : 1< Z, ∀hM : 0≤ M,
    let s := fixedParentState (anchors j) (internalQ Q η₀) Φ bΦ Z M hZ hM hsΦ hpΦ;
    let inp := affineInput rayM H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i => ⟨hσlo i,hσhi i⟩) s p ha M t X₁ X₂ hX₁ hX₂;
    energy (anchors j) (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep (anchors j) (internalQ Q η₀)) Φ (Z^M) ≤
      2*diagonalControl Φ*(physicalMass inp 1 1 fixedBadMask 1 Ψ (Z^M) Z ξ/
        CenteredMomentAmplificationChildInput.volume inp)+
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε) := by
  obtain ⟨Ψ,hs,hp,hm,J,S,hbound⟩ := actual_initial_source_reduction_fixed_mesh (α:=α)
    rayM H hH anchors W aslot bslot lo hi a b bΦ Mmin Mmax ε ξ haslot hWs hW hbslot
    hlohi ha hlo hhi hbΦ hMmin hMmax hε hξ hbeta hκbeta
  exact ⟨Ψ,hs,hp,comparisonMesh Mmin Mmax ε,hm,J,S,hbound⟩

end
end OAI.SevenEighths.Cycle61InitialSource

end
/- END ORIGINAL Cycle61.Physical.InitialSourceReduction -/
