import Candidate.Cycle63.Physical.FirstBranches.Reflection
import Candidate.Cycle63.Physical.FirstBranches.Direct
import Candidate.Cycle63.Physical.FirstBranches.Geometry
import Candidate.Cycle25.Energy.Endpoint
import Candidate.Cycle63.Physical.FirstBranches.Zero

namespace OAI.SevenEighths.Cycle63FirstActual
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
open Cycle63FirstReflection Cycle63FirstGeometry
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

/-- Actual comparison energy, with two independent plain heights and an explicit
arbitrarily decaying reflection tail. The old terminal is proved and instantiated
inside this theorem only at daughters; no old parent capacity hypothesis occurs. -/
theorem actual_reflected_comparison
    (Fmax:Finset α)(Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hWslot:ContDiff ℝ ∞ Wslot)(hbslot:0≤bslot)
    (a b bΦ epsilon xi saving Bmask L Mcap ε:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hε:0<ε)(hL:Mcap+xi≤L)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ))
    (B:ℕ)(hB:2≤B):
    ∃degree:ℕ,
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
      ∀η₀:Character,∀Q:Ideal O,Q≤M → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(F:Finset α),F⊆Fmax → ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Cycle25.Energy.commonMesh Mcap Bmask L ε) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(Wlong Wshort:𝓢(ℝ,ℂ)),
      Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b →
      ∀(Mrow along bshort:ℝ),0≤Mrow → Mrow≤s.width → Mrow/2≤along →
      bshort≤Mrow/4 → (∑i∈F,w i)≤Mrow/25 → xi≤7*Mrow/100 →
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
  have hMrCap : Mrow≤Mcap := hMw.trans hs
  have hAlong : 0≤along := by linarith
  have hLnonneg : 0≤L := by linarith
  have hlength : s.width≤L+along := by linarith
  have hwindow : max 0 (s.width-along+xi)≤L := max_le hLnonneg (by linarith)
  have hbshort : bshort≤L := by linarith
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
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)
    (hWslot:ContDiff ℝ ∞ Wslot)(hbslot:0≤bslot)
    (a b bΦ Bmask L Mcap ε:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hε:0<ε)(hL:Mcap≤L)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤(3/4:ℝ)) :
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),
      ∀η₀:Character,∀Q:Ideal O,Q≤M → internalQ Q η₀≠0 →
      internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      ∃C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Cycle25.Energy.commonMesh Mcap Bmask L ε) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀(Mrow X₁ X₂:ℝ),0≤Mrow → Mrow≤s.width → 0<X₁ → 0<X₂ →
      X₁≤Z^(Mrow/4) → X₂≤Z^(Mrow/2) → (∑i∈F,w i)≤Mrow/25 →
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
  have h₁ : X₁≤Z^L := hc₁.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have h₂ : X₂≤Z^L := hc₂.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  exact Cycle63FirstDirect.direct_child_from_positive M H hH Wslot bslot a b bΦ
    Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε (3/4) Z η₀ Q
    degree S C hZ.2 hmask ha F θ w σ freq u t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ h₁ h₂
    (by convert hcap using 1; norm_num)


/-- Exact original-row bridge at the initial unit puncture. It preserves the
literal two-plain normalizer, character, profile heights and slots. -/
theorem actual_unit_puncture_energy
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(hpuncture:s.puncture=1)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)
    (Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
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
end OAI.SevenEighths.Cycle63FirstActual
#print axioms OAI.SevenEighths.Cycle63FirstActual.actual_reflected_comparison

#print axioms OAI.SevenEighths.Cycle63FirstActual.actual_direct_comparison

#print axioms OAI.SevenEighths.Cycle63FirstActual.actual_unit_puncture_energy


-- The old terminal is an approved, independently certified daughter input. The
-- audit stops at that exact declaration when checking which comparison geometry
-- this new proof applies. The kernel axiom checks above traverse its full proof.
set_option maxHeartbeats 0 in
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``OAI.SevenEighths.Cycle63FirstActual.actual_reflected_comparison,
      ``OAI.SevenEighths.Cycle63FirstActual.actual_direct_comparison,
      ``OAI.SevenEighths.Cycle63FirstActual.actual_unit_puncture_energy,
      ``OAI.SevenEighths.Cycle63FirstZero.actual_first_zero_at_physical_radius,
      ``OAI.SevenEighths.Cycle63FirstZero.actual_unamplified_added_zero] do
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
          "Cycle63Moment.InitialAffineAt", "Cycle63.Assembly.Final"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      if n == ``Cycle25.Energy.terminal_positive_at then continue
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle63.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle63.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    if root == ``OAI.SevenEighths.Cycle63FirstActual.actual_reflected_comparison then
      unless seen.contains ``Cycle25.Energy.terminal_positive_at &&
          seen.contains ``OAI.SevenEighths.CenteredMomentRetainedWeightedSource.actual_retained_weighted_energy &&
          seen.contains ``OAI.SevenEighths.Cycle63FirstGeometry.reflected_daughter_capacity do
        throwError "Genuine daughter terminal, retained analysis or new geometry missing"
    logInfo m!"{root}: {seen.size} project constants outside approved old terminal; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do
      throwError "Cycle63 FirstBranches dependency audit rejected {root}"
