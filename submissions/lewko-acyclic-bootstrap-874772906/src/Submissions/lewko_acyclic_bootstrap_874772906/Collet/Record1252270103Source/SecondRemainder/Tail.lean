/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Adapted from the pinned OpenAI/Hailey Collet SourceInputTailUniform proof;
the corrected tuple mass and its exact coefficient replace the ordinary mass. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.SecondRemainder.SupportedTuple
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputTailSeed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>ActualEisensteinCubic.O
local notation "coefficient"=>High.CoupledFirst.coefficient
local instance tailTupleDecidable {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

theorem second_tail (N : ℕ) (hiMax wlo whi B ξ saving : ℝ)
    (hhi : 0≤hiMax) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B) (hξ : 0<ξ) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→∀(s : Input ι)(modifier : Tuple ι→ℂ)(factor : ℝ)(R seed : Ideal O)(W₁ W₂ : 𝓢(ℝ,ℂ)),
    0≤factor→(∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor)→
    s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hiMax)→
    ∀(Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),0<K→volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/K≤Tsec→
    ‖secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed) Φ K Tsec Z ξ‖/volume s.toData≤
    C*(factor*plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by

  obtain ⟨Adec,hdecay⟩:=choose_tail_order B ξ saving hB hξ
  obtain ⟨SΦ,Ctail,hCtail,htail⟩:=second_discarded_energy_bound Adec
  let Cmass:=1+2*128^(N+2)*(max 1 hiMax)^N*whi^2
  have hCmass:0<Cmass:=by dsimp [Cmass];positivity
  let HN:=Real.log (max 1 ((max 1 hiMax)^N*whi^2))
  have hexpBound:(max 1 hiMax)^N*whi^2≤Real.exp HN:=by
    dsimp [HN]
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  let C:=Cmass^2*Ctail*(Real.exp HN)^2*(1+Real.exp (2*HN))^2
  refine ⟨SΦ,C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_tail_threshold HN ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ hcard s modifier factor R seed W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi Φ K Tsec hK hVcap hTcap hnom
  have hprod : (∏_i : ι,hiMax)≤(max 1 hiMax)^N := by
    simp only [Finset.prod_const,Finset.card_univ]
    exact (pow_le_pow_left₀ hhi (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hcard)
  have h128 : (128:ℝ)^(Fintype.card ι+2)≤128^(N+2) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hcard 2)
  have hexp : (∏_i : ι,hiMax)*whi^2≤Real.exp HN :=
    (mul_le_mul_of_nonneg_right hprod (sq_nonneg _)).trans hexpBound
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  have hT:0<Tsec:=(div_pos (sq_pos_of_pos hV) hK).trans_le hnom
  have hmass:=supported_input_mass (fun _=>hiMax) whi (fun _=>hhi) hwhi s modifier factor hfactor R seed hmod W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi
  have hcontrol:=mul_nonneg hfactor (plainControl_nonneg s W₁ W₂)
  have hm:(∑I∈finiteColumns (Fintype.piFinset s.pools),‖coefficient s modifier R seed I‖)≤
      Cmass*(factor*plainControl s W₁ W₂)*V:=by
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ hV.le
    apply mul_le_mul_of_nonneg_right _ hcontrol
    have hh : 2*128^(Fintype.card ι+2)*(∏_i : ι,hiMax)*whi^2≤
        2*128^(N+2)*(max 1 hiMax)^N*whi^2 := by gcongr
    dsimp [Cmass]
    linarith
  have hn (I:Ideal O)(_hI:I∈finiteColumns (Fintype.piFinset s.pools))
      (hI:coefficient s modifier R seed I≠0):(Ideal.absNorm I:ℝ)≤Real.exp HN*V:=
    (High.CoupledFirst.input_column_bound (fun _=>hiMax) whi s modifier W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hshi R seed I hI).trans
      (mul_le_mul_of_nonneg_right hexp hV.le)
  have ht:=htail s.η s.t (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R seed)
    Φ K V HN Tsec Z 1 ξ hK hV hZ.1 le_rfl hn hnom (by simpa using hZ.2)
  have hsquare:=pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) hm 2
  have hp:0<min 1 (kernelReference Tsec HN):=lt_min zero_lt_one (kernelReference_pos _ _ hT)
  have hzpos:0<Z:=zero_lt_one.trans hZ.1
  have hzpower:0<Z^(ξ/4):=Real.rpow_pos_of_pos hzpos _
  have hden:0<(min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec:=by positivity
  have hb:=hdecay HN Z V Tsec hZ.1.le hV hVcap hT hTcap
  calc
    _≤((Cmass*(factor*plainControl s W₁ W₂)*V)^2*K*(Real.exp HN*V)^2*
        (Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec))/V:=by
      apply div_le_div_of_nonneg_right _ hV.le
      apply ht.trans
      apply div_le_div_of_nonneg_right _ hden.le
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hsquare hK.le
    _=(Cmass^2*Ctail*(Real.exp HN)^2*((factor*plainControl s W₁ W₂))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        (V^3*((min 1 (kernelReference Tsec HN))^2)⁻¹*((1+Z^(ξ/4))^Adec)⁻¹):=by
      field_simp [ne_of_gt hV,ne_of_gt hp]
    _≤(Cmass^2*Ctail*(Real.exp HN)^2*((factor*plainControl s W₁ W₂))^2*
        SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K)*
        ((1+Real.exp (2*HN))^2*Z^(-saving)):=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _=_:=by dsimp [C];ring


lemma parent_normalization (z : ℂ) (V T A : ℝ) (hV : 0<V) (hT : 0<T)
    (hbound : ‖z‖/V≤A) : ‖(T:ℂ)⁻¹*z‖≤A*(V/T) := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  calc
    _=(‖z‖/V)*(V/T) := by field_simp [hV.ne',hT.ne']
    _≤_ := mul_le_mul_of_nonneg_right hbound (div_nonneg hV.le hT.le)

theorem normalized_second_tail_seed (N : ℕ) (hiMax wlo whi B Bseed ξ saving : ℝ)
    (hhi : 0≤hiMax) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B) (hξ : 0<ξ) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→∀(s : Input ι)(modifier : Tuple ι→ℂ)(factor : ℝ)(R seed : Ideal O)(W₁ W₂ : 𝓢(ℝ,ℂ)),
    0≤factor→(∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor)→
    s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hiMax)→
    seed≠0→(seed.absNorm:ℝ)≤Z^Bseed→
    ∀(Φ : 𝓢(ℝ,ℂ))(H Tsec T : ℝ),0<H→0<T→
    volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/H≤Tsec→
    ‖(T:ℂ)⁻¹*secondDiscardedEnergy s.η s.t (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R seed) Φ H Tsec Z ξ‖≤
    C*(factor*plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*
      H*(volume s.toData/T)*Z^(-saving)/(seed.absNorm:ℝ) := by
  obtain ⟨SΦ,C,hC,htail⟩:=second_tail N hiMax wlo whi B ξ (saving+Bseed) hhi hwlo hwhi hB hξ
  refine ⟨SΦ,C,hC,?_⟩
  filter_upwards [htail] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ hcard s modifier factor R seed W₁ W₂ hf hmod he₁ he₂ hs₁ hs₂ hshi hseed hseedcap
    Φ H Tsec T hH hT hV hTsec hnom
  have hsn : (0:ℝ)<seed.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hseed)
  have hv : 0<volume s.toData := volume_pos s
  have hb:=hz.2 hcard s modifier factor R seed W₁ W₂ hf hmod he₁ he₂ hs₁ hs₂ hshi Φ H Tsec hH hV hTsec hnom
  apply (parent_normalization _ (volume s.toData) T _ hv hT hb).trans
  calc
    _=(C*(factor*plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*
        H*(volume s.toData/T))*Z^(-(saving+Bseed)) := by ring
    _≤_ := CenteredMomentSourceInputTailSeed.paid_seed_term Z Bseed saving (seed.absNorm:ℝ) _
      (zero_lt_one.trans hz.1) hsn hseedcap (by positivity)
end
end QRH.Record1252270103Source.SecondRemainder
#print axioms QRH.Record1252270103Source.SecondRemainder.second_tail

#print axioms QRH.Record1252270103Source.SecondRemainder.normalized_second_tail_seed
