/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual normalized first physical reduction for a finite tuple modifier.
The correction cap pays diagonal/tail losses; retained coefficients remain literal. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstZero
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstTail
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstPhysical
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentFirstSectorTransform CenteredMomentFirstSectors CenteredMomentFirstEnergy
open CenteredMomentActiveSource CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledFirstRemainderDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def physicalMass (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)
    (m A:O)(Φ:𝓢(ℝ,ℂ))(K Z ξ:ℝ):ℝ :=
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s modifier R seed
  let T:=activeSource S β
  ∑p:commonLabels (supportedColumns T) (supportedColumns T),
    sectorMass s modifier R seed m A s.t S p.val.1 p.val.2
      (commonLabels_supported T p).1 (commonLabels_supported T p).2 Φ K
      (volume s.toData) Z ξ

omit [DecidableEq ι] in
theorem original_first_remainder (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s modifier R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*((factor*plainControl s W₁ W₂))^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*((factor*plainControl s W₁ W₂))^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Cdiag,hCdiag,hdiag⟩:=first_input_zero_capped hi wlo whi B ε hhi hwlo hwhi hB hε
  obtain ⟨Stail,Ctail,hCtail,htail⟩:=local_input_tail hi wlo whi B ξ saving hhi hwlo hwhi hB hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hd:=hdiag Z hZ.1.le s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi hVcap m A R seed Φ K hK.le
  have ht:=hZ.2 s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hVcap hKi
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    s.η m A s.t hml hm2 (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s modifier R seed) Φ K (volume s.toData) Z ξ hK]
  rw [show ∀a b c:ℂ,a+b+c-b=a+c by intros;ring]
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos s).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd ht)

 theorem original_first_physical_reduction (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s modifier R seed) Φ K‖/volume s.toData≤
      physicalMass s modifier R seed m A Φ K Z ξ/volume s.toData+
      Cdiag*((factor*plainControl s W₁ W₂))^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*((factor*plainControl s W₁ W₂))^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,hrem⟩:=
    original_first_remainder hi wlo whi B ε ξ saving hhi hwlo hwhi hB hε hξ
  refine ⟨Sdiag,Stail,Cdiag,Ctail,hCdiag,hCtail,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have hz (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hr:=original_retained_full_sectorMass s modifier R seed (he₁.symm ▸ hz W₁ hs₁) (he₂.symm ▸ hz W₂ hs₂)
    m A s.t (finiteColumns (Fintype.piFinset s.pools)) Φ K (volume s.toData) Z ξ hK
  change ‖CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
    (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed) Φ K
      (volume s.toData) Z ξ‖≤physicalMass s modifier R seed m A Φ K Z ξ at hr
  have he:=hZ.2 s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A hml hm2 R seed Φ K hK hVcap hKi
  have htri:=norm_le_norm_sub_add
    (finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed) Φ K)
    (CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
      (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed) Φ K (volume s.toData) Z ξ)
  have hdiv:=div_le_div_of_nonneg_right htri (volume_pos s).le
  rw [add_div] at hdiv
  have hrdiv:=div_le_div_of_nonneg_right hr (volume_pos s).le
  linarith


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_first_remainder
#print axioms QRH.Record1252270103Source.High.CoupledFirst.original_first_physical_reduction
