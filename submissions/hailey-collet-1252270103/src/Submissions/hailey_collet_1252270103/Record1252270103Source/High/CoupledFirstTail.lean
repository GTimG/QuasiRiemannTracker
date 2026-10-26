/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Arbitrarily saving first discarded remainder with the literal tuple modifier. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.CoupledFirstBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailNatural
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
open CenteredMomentSourceInputFirstTailUniform CenteredMomentAddedZeroUniform
open CenteredMomentSourceInputFirstSectorTail
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledFirstTailDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _
omit [DecidableEq ι] in
theorem local_input_tail_arbitrary_saving (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K Tsec:ℝ),
      0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s modifier R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*((factor*plainControl s W₁ W₂))^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):=by
  obtain ⟨Adec,hdecay⟩:=choose_first_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=local_discarded_energy_bound Adec 1 zero_lt_one
  let Cmass:=1+2*128^(Fintype.card ι+2)*(∏i,hi i)*whi^2
  have hprodhi:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((∏i,hi i)*whi^2))
  have hexp:(∏i,hi i)*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K Tsec hK hVcap hTcap hnom
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=input_mass hi whi hhi hwhi s modifier factor hfactor hmod W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed
  have hcontrol:=mul_nonneg hfactor (plainControl_nonneg s W₁ W₂)
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s modifier R seed I‖)≤
      Cmass*(factor*plainControl s W₁ W₂)*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s modifier R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (input_column_bound hi whi s modifier W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η m A s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn
    hnom (by simpa using hZ.2)
  simp only [Real.rpow_one] at ht
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*(factor*plainControl s W₁ W₂)*V)^2*K*(Real.exp HN*V)*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsquare (mul_nonneg (Real.exp_pos HN).le hV.le)) hK.le).trans_eq
        (by ring)
    _=(Cmass^2*Ctail*(Real.exp HN)*((factor*plainControl s W₁ W₂))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^2*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)*((factor*plainControl s W₁ W₂))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring

omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s modifier R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*((factor*plainControl s W₁ W₂))^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨S,C,hC,htail⟩ := local_input_tail_arbitrary_saving hi wlo whi (3*B) ξ saving
    hhi hwlo hwhi (by positivity) hξ
  refine ⟨S,C,hC,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hV hKi
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hV0 : 0<volume s.toData := volume_pos s
  have hVcap : volume s.toData≤Z^(3*B) := hV.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hTcap : (volume s.toData)^2/K≤Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV0.le hV 2) hKi (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  exact hZ.2 s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K _ hK hVcap hTcap le_rfl


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.local_input_tail
