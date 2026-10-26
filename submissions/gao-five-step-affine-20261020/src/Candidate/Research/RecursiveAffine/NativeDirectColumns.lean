/- The actual narrow physical daughter through the native Common/Column operator.
Copyright (c)2026 Zhongpai Gao. Native analytic estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeDirectPhysicalSource
import Candidate.Research.RecursiveAffine.NativeUniformColumnForest
import Candidate.Research.RecursiveAffine.NativeCommonMap

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily HeckePrimeAnnular CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentAllocatedRayDictionary CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentInductionEnergy CenteredMomentDivisorAllocation CenteredMomentCanonicalFirst
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural Cycle153SourceReturn
open Cycle63InitialMass Cycle63Moment Cycle153ActualColumn Cycle63FinalCapacity
open CenteredMomentCommonPairedSource
attribute [local irreducible] physicalDaughterEnergy finalPositiveEnergy normalizedColumn

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

def DirectColumnsAt [Cycle63.AffineLedger]
    (W : ℝ → ℂ) (Bmask L Mcap εold : ℝ)
    (hWs : Function.support W ⊆ Icc 1 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0  ≤  Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100  ≤  HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d q : ℝ)
    (hRw : 0  ≤  Rwidth) (hdmax : 0  ≤  dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0  ≤  η)
    (hbudget : 8*e*Rwidth+κ  ≤  ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin  ≤  d) (hdm : d  ≤  dmax)
    (hq₀ : 0  ≤  q) (hq₁ : q  ≤  1)
    (inputBound epsShell : ℝ)(hShell : 0<epsShell) (degree : ℕ)(S : Finset (ℕ×ℕ))(η₀ : Character)(Qfixed : Ideal O)
    (C C₀ C₁ Kcol Z : ℝ) : Prop :=
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)
      (w σ freq : α→ℝ)(t height mesh a : ℝ)(i : ℕ),
    Matches M H hH s η₀ θ w σ freq W 2 Z→
    (∀j,0 ≤ w j)→(∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)→
    0 ≤ mesh→(∀j,w j ≤ mesh)→(∀j,w j/d ≤ Rwidth)→
    (∀j,(33/50:ℝ) ≤ σ j)→(∀j,σ j ≤ (33/50:ℝ))→0 ≤ height→(∀j,|freq j| ≤ height)→
    51/100 ≤ a→a ≤ (1+q)/2→|t|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ→
    (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η→
    ∀(ch : Chain s)(Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax leastWidth : ℝ)
      (budget : ℕ)(g : LiveMainGeometry s ch Z Mrow amp omega xi bs budget)
      (ray : RayFourExpansion.RayCharacter)(Q : Ideal O)(hP : ch.R₂*ch.E₂≠0)
      (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Z^Bmask),
    let chi:=g.datum.τ ray
    let st:=retainedState Z Bmask hZ chi Q (ch.R₂*ch.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let firstInput:=withHeight ch.first chi t
    let nominal:=secondNominal 1 Z amp omega ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
    st.fixedModulus=internalQ Qfixed η₀→st.width ≤ Mcap→
    ∀(p : Profiles (1/4) (9/4)),s.W₁=(p.profile 0:ℝ→ℂ)→s.W₂=(p.profile 1:ℝ→ℂ)→
    1 ≤ bs→s.upper ≤ bs→
    (Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)→
    length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.B→
    Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+epsWidth/2→
    Real.logb Z CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(budget:ℝ)*Real.logb Z bs+Real.logb Z 1+
      Real.logb Z (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ)) ≤ epsWidth/2→
    0 ≤ epsWidth→0 ≤ xi→0 ≤ omega→0 ≤ epsPad→
    supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z ≤ epsPad→
    omega ≤ omegaMax→epsWidth+xi/2 ≤ deltaMax→q/(6*Cycle63.Optimization.slotPrice) ≤ 1/2→
    Cycle63.AffineLedger.lowReserve ≤ amp→nominal+(epsWidth+xi/2)<leastWidth→
    (q/(6*Cycle63.Optimization.slotPrice)*
      (Cycle63.AffineLedger.g (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))+6*amp)-amp)+
      Cycle63.AffineLedger.lowReserve+q/(6*Cycle63.Optimization.slotPrice)*(deltaMax+epsPad)+
      2*(q/(6*Cycle63.Optimization.slotPrice))*omegaMax ≤
        q/(6*Cycle63.Optimization.slotPrice)*(1-6*amp-2*leastWidth)→
    ∀(hQM : st.fixedModulus ≤ M)(hQeta : st.fixedModulus ≤ η₀.modulus),
    let low:=ActualLow M H hH st η₀ hQM hQeta a e (3*(i+1:ℕ)*Z^τ)
    ∀(Ds : Finset (Ideal O))(zs : Finset O)(rowWeight : O→ℝ)(T pad : ℝ)
      (seed : Ideal O)(hOwn : Supported ch.E₂)(hseed : seed∣ch.E₂),
    firstInput.upper ≤ inputBound→1 ≤ T→
    (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T)→
    (∀z,st.radial.keep z ∧ low z→0 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re)→
    (∀z∈zs,0 ≤ rowWeight z)→(∀z∈zs,st.radial.keep z ∧ low z)→
    (∀z∈zs,rowWeight z ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re)→
    (∀B : actualAllocations firstInput.pools ch.E₂,commonScalar firstInput ch.E₂ ch.R₂ B≠0→
      (commonData firstInput ch.E₂ ch.R₂ B).toSource.allowance Z ≤ pad)→
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun daughter : Daughter=>commonData firstInput ch.E₂ ch.R₂ daughter.1
    (∀daughter : Daughter,rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 0 ≤ Z^L)→
    (∀daughter : Daughter,rawDaughterScale (src daughter) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 1 ≤ Z^L)→
    let Old : ℝ :=nominal+(epsWidth+xi/2)+amp-Cycle63.AffineLedger.lowReserve+
      lowAllowance Z ch.C₁ g.D₁ g.datum.C g.datum.D ch.E₂+
      εold+2*ε*d*(Fintype.card α:ℝ)+q/(6*Cycle63.Optimization.slotPrice)*(omega+epsPad)+q*mesh
    let Env : ℝ :=C^(Fintype.card α)*((C₀+C₁)*QuadraticInitialBound.diagonalControl st.radial.profile*
      (p.control S)^2*(1+|t|+height)^degree)
    (∑D∈Ds,∑z∈zs,rowWeight z*‖normalizedColumn firstInput ch.E₂ hOwn ch.R₂ seed D z‖^2) ≤
      Kcol*firstInput.toData.profileFactor*(∏j : liveIndices ch.B₁.val,firstInput.M j)^2*
        (Env*Z^Old)*(ch.E₂.absNorm:ℝ)^(epsShell-1)*(2*T)^(3*epsShell)*Z^pad

attribute [local irreducible] DirectColumnsAt

theorem eventual_actual_direct_columns [Cycle63.AffineLedger]
    (W : ℝ → ℂ) (Bmask L Mcap εold : ℝ)
    (hWs : Function.support W ⊆ Icc 1 2) (hW : ContDiff ℝ ∞ W)
    (hBmask : 0  ≤  Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100  ≤  HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d q : ℝ)
    (hRw : 0  ≤  Rwidth) (hdmax : 0  ≤  dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0  ≤  η)
    (hbudget : 8*e*Rwidth+κ  ≤  ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin  ≤  d) (hdm : d  ≤  dmax)
    (hq₀ : 0  ≤  q) (hq₁ : q  ≤  1)
    (inputBound epsShell : ℝ)(hShell : 0<epsShell) : ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∀(η₀ : Character)(Qfixed : Ideal O),Qfixed ≤ M→
      internalQ Qfixed η₀≠0→internalQ Qfixed η₀≠⊤→internalQ Qfixed η₀ ≤ Ideal.span {(72:O)}→
    ∃C C₀ C₁ Kcol : ℝ,1≤C ∧ 0<C₀ ∧ 0<C₁ ∧ 0<Kcol ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧ DirectColumnsAt (α:=α)
      M H hH W Bmask L Mcap εold hWs hW hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d q hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm hq₀ hq₁
      inputBound epsShell hShell degree S η₀ Qfixed C C₀ C₁ Kcol Z := by
  obtain ⟨degree,S,hnative⟩:=actual_live_direct_physical_daughter (α:=α) M H hH
    W Bmask L Mcap εold hWs hW hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d q hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm hq₀ hq₁
  obtain ⟨Kcol,hKcol,hcolumns⟩:=actual_uniform_low_columns_returned_forest (alpha:=α) inputBound epsShell hShell
  refine ⟨degree,S,?_⟩
  intro η₀ Qfixed hQfixedM hQ0 hQt hQ72
  obtain ⟨C,C₀,C₁,hC,hC₀,hC₁,hsource⟩:=hnative η₀ Qfixed hQfixedM hQ0 hQt hQ72
  refine ⟨C,C₀,C₁,Kcol,hC,hC₀,hC₁,hKcol,?_⟩
  filter_upwards [hsource] with Z hz
  refine ⟨hz.1,?_⟩
  unfold DirectColumnsAt
  intro hZ s θ w σ freq t height mesh a i hm hw hwL hmesh hwm hwr hσlo hσhi hheight hfreq
    ha ha' hfreqbin hhigh ch Mrow amp omega xi bs epsWidth epsPad omegaMax deltaMax leastWidth
    budget g ray Q hP hPN chi st firstInput nominal hfixed hMcapNow p hp1 hp2 hb hs hslots haff
    hfit hconstants hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate hreserve hnarrow
    hcert hQM hQeta low Ds zs rowWeight T pad seed hOwn hseed hInput hT hDs hPhi hrow0 hkeep hrow hallow
    Daughter src hX1 hX2 Old Env
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hEnv : 0 ≤ Env := by
    have hC0 : 0 ≤ C:=zero_le_one.trans hC
    have hdiag:=QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
    dsimp only [Env];positivity
  have hD : ∀daughter : Daughter,commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0→
      physicalDaughterEnergy firstInput ch.E₂ ch.R₂ Ds (fun z=>st.radial.keep z ∧ low z)
        st.radial.profile st.radial.scale daughter ≤ Env*Z^Old := by
    intro daughter hn
    by_cases hlive : ∃z,Cycle63.Physical.sourcePositiveRow (src daughter).toSource
      daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 z≠0
    · obtain ⟨row,hne⟩:=hlive
      let qchain:=commonContinuationChain s ch chi t daughter.1
      let geometry:=commonContinuationGeometry g chi t daughter.1 hn
      have hE:=hz.2 hZ s θ w σ freq t height mesh a i hm hw hwL hmesh hwm hwr hσlo hσhi
        hheight hfreq ha ha' hfreqbin hhigh qchain Mrow amp omega xi bs epsWidth epsPad omegaMax
        deltaMax leastWidth budget geometry ray Q hP hPN daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1
        hfixed hMcapNow p hp1 hp2 (hX1 daughter) (hX2 daughter) hb hs hslots haff hfit hconstants
        hepsWidth hxi homega hepsPad hpad homegaMax hdeltaMax hrate hreserve hnarrow hcert row hne hQM hQeta
      rw [physicalDaughterEnergy_eq_native]
      change finalPositiveEnergy (qchain.final chi t) daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1
        (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale ≤ _
      exact hE
    · have hzrow : ∀z,Cycle63.Physical.sourcePositiveRow (src daughter).toSource
          daughter.2.2.2 daughter.2.1.1 daughter.2.2.1.1 z=0 := by
        simpa only [not_exists,not_not] using hlive
      rw [physicalDaughterEnergy_eq_native,zero_low_energy _ _ _ _ _ _ _ hzrow]
      exact mul_nonneg hEnv (Real.rpow_nonneg hZ0.le _)
  let junction : Empty→ℝ:=fun _=>0
  let Base : Empty→Type:=fun _=>Unit
  let dict : (d : Empty)→Character→Base d→Character:=fun _ eta _=>eta
  let Family:=DepthReturnedFamily M H hH junction Base dict η₀ Z 0 0 1
  have hsourceD : ∀daughter : Daughter,commonScalar firstInput ch.E₂ ch.R₂ daughter.1≠0→
      ∃F : Family,True ∧ physicalDaughterEnergy firstInput ch.E₂ ch.R₂ Ds
        (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale daughter ≤
        Env*(Z^Old+(0:ℝ)*F.value) := by
    intro daughter hn
    refine ⟨emptyReturnedForest,True.intro,?_⟩
    simpa only [zero_mul,add_zero] using hD daughter hn
  obtain ⟨Fout,_,hbound⟩:=hcolumns (liveIndices ch.B₁.val) M H hH Empty junction Base dict η₀ 0 0 1
    firstInput hInput ch.E₂ ch.R₂ seed hOwn hseed Ds zs rowWeight T Z pad hT hZ hDs
    (fun z=>st.radial.keep z ∧ low z) st.radial.profile st.radial.scale st.radial.scale_pos
    hPhi hrow0 hkeep hrow hallow Env (Z^Old) hEnv (Real.rpow_nonneg hZ0.le _)
    (fun _=>0) (fun _=>le_rfl) (fun _ _=>True) hsourceD
  have hv : Fout.value=0 := by simp only [DepthReturnedFamily.value,Fintype.sum_empty]
  simpa only [hv,add_zero] using hbound

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_direct_columns
