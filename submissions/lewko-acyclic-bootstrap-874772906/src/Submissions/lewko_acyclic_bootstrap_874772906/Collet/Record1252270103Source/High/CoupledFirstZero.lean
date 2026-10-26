/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Diagonal remainder for the actual finite tuple modifier, via tuple counting. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.CoupledFirst
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass CenteredMomentSourceInputTailUniform
open CenteredMomentFirstLocalization EisensteinSchwartzPoisson
open CenteredMomentExceptionalAmplitudePair CenteredMomentAddedZeroUniform
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance coupledFirstZeroDecidable : DecidableEq (ι⊕Fin 2):=Classical.decEq _
omit [DecidableEq ι] in
theorem first_input_zero_bound (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(_hwhi:0≤whi)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s modifier R seed) Φ K‖/volume s.toData≤
      C*((factor*plainControl s W₁ W₂))^2*K*‖paperRadialFourier Φ 0‖*(volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hbound⟩:=active_tuple_zero_energy_bound (Fintype.card ι) ε hε
  let L:=1+(∏i,hi i)*whi^2
  have hprod:0≤∏i,hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hL:0<L:=by dsimp [L];positivity
  refine ⟨4*C₀*L^(1+ε),by positivity,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  let V:=volume s.toData
  have hV:0<V:=volume_pos s
  let β:=fun v : Tuple ι=>modifier v*profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  have hc:coefficient s modifier R seed=finiteColumnCoefficient (Fintype.piFinset s.pools) β:=by
    unfold coefficient tupleCoefficient;rw [he₁,he₂]
  have hcontrol:=plainControl_nonneg s W₁ W₂
  have hβ (v:Tuple ι)(hv:v∈Fintype.piFinset s.pools):‖β v‖≤2*(factor*plainControl s W₁ W₂):=by
    have hb:=profileCoefficient_norm_le R s.ν s.ν_bound s.W s.P s.M W₁ W₂
      (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
      (fun i=>zero_le_one.trans (s.M_ge_one i)) (apply_nonneg _ _) (apply_nonneg _ _)
      s.W_bound (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
    have hb' : ‖profileCoefficient R s.ν s.W s.P W₁ W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v‖≤
        2*plainControl s W₁ W₂ := hb.trans_eq (by dsimp [plainControl];ring)
    dsimp only [β]
    rw [norm_mul]
    exact (mul_le_mul (hmod v hv) hb' (norm_nonneg _) hfactor).trans_eq (by ring)
  have hz (i:ι):s.W i 0=0:=by
    by_contra hn
    exact (not_le_of_gt (s.lo_pos i)) (s.support i hn).1
  have hzW (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc wlo whi):W 0=0:=by
    by_contra hn
    exact (not_le_of_gt hwlo) (hs hn).1
  have hN (v:Tuple ι)(hv:β v≠0):finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*V:=by
    have hv := (mul_ne_zero_iff.mp hv).2
    have hp:=profileCoefficient_product_bound R s.ν s.W s.P hi W₁ W₂ whi whi
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) 1 1 seed
      s.P_pos s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos one_ne_zero one_ne_zero rfl s.same_product
      hz (hzW W₁ hs₁) (hzW W₂ hs₂) (fun i x hx=>((s.support i hx).2).trans (hshi i))
      (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) v hv
    refine ⟨hp.1,hp.2.trans ?_⟩
    simp only [map_one,Nat.cast_one,one_mul,div_one]
    change (∏i,hi i)*whi*whi*(s.X₁*s.X₂)*(∏i,s.P i)≤_
    have hh:0≤V:=hV.le
    dsimp [L,V,volume] at *
    nlinarith
  rw [hc]
  by_cases hsmall:L*V<1
  · rw [zeroEnergy_eq_zero_of_subunit s.η m A s.t (Fintype.piFinset s.pools) β Φ K
      (L*V) hsmall (fun v _ hv=>hN v hv),norm_zero,zero_div]
    positivity
  have hb:=hbound (le_refl (Fintype.card ι)) s.η m A s.t (Fintype.piFinset s.pools) β Φ
    (L*V) K (2*(factor*plainControl s W₁ W₂)) (le_of_not_gt hsmall) hK (by positivity)
    (fun v hv _=>hβ v hv) (fun I _ hI=>by
      obtain ⟨v,hv,hn,he⟩:=finiteColumnCoefficient_witness _ _ I hI
      rw [←he];exact (hN v hn).2)
  apply (div_le_div_of_nonneg_right hb hV.le).trans_eq
  have hp:(L*V)^(1+ε)/V=L^(1+ε)*V^ε:=by
    rw [Real.mul_rpow hL.le hV.le,Real.rpow_add hV,Real.rpow_one]
    field_simp
  change C₀*K*(2*(factor*plainControl s W₁ W₂))^2*‖paperRadialFourier Φ 0‖*(L*V)^(1+ε)/V=_
  calc
    _=4*C₀*((factor*plainControl s W₁ W₂))^2*K*‖paperRadialFourier Φ 0‖*((L*V)^(1+ε)/V):=by ring
    _=_:=by rw [hp];ring

omit [DecidableEq ι] in
theorem first_input_zero_uniform (hi:ι→ℝ)(wlo whi ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s modifier R seed) Φ K‖/volume s.toData≤
      C*((factor*plainControl s W₁ W₂))^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*
        (volume s.toData)^ε:=by
  obtain ⟨C₀,hC₀,hb⟩:=first_input_zero_bound hi wlo whi ε hhi hwlo hwhi hε
  obtain ⟨SΦ,D,hD,hd⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK
  have hf:‖paperRadialFourier Φ 0‖≤D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hd Φ 0 le_rfl 0 le_rfl
  have hVp:0≤(volume s.toData)^ε:=Real.rpow_nonneg (volume_pos s).le _
  apply (hb s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
  calc
    _≤C₀*((factor*plainControl s W₁ W₂))^2*K*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        (volume s.toData)^ε:=by gcongr
    _=_:=by ring

omit [DecidableEq ι] in
theorem first_input_zero_capped (hi:ι→ℝ)(wlo whi B ε:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀Z:ℝ,1≤Z→
      ∀(s:Input ι)(modifier:Tuple ι→ℂ)(factor:ℝ)(W₁ W₂:𝓢(ℝ,ℂ)),
      0≤factor→(∀v∈Fintype.piFinset s.pools,‖modifier v‖≤factor)→s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→volume s.toData≤Z^B→
      ∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0≤K→
      ‖zeroEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s modifier R seed) Φ K‖/volume s.toData≤
      C*((factor*plainControl s W₁ W₂))^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε:=by
  let δ:=ε/(B+1)
  have hδ:0<δ:=div_pos hε (by linarith)
  obtain ⟨SΦ,C,hC,hb⟩:=first_input_zero_uniform hi wlo whi δ hhi hwlo hwhi hδ
  refine ⟨SΦ,C,hC,?_⟩
  intro Z hZ s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi hV m A R seed Φ K hK
  have hp:(volume s.toData)^δ≤Z^ε:=by
    calc
      _≤(Z^B)^δ:=Real.rpow_le_rpow (volume_pos s).le hV hδ.le
      _=Z^(B*δ):=(Real.rpow_mul (zero_le_one.trans hZ) B δ).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ (by
        have hh:δ*(B+1)=ε:=by dsimp [δ];field_simp
        nlinarith)
  exact (hb s modifier factor W₁ W₂ hfactor hmod he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))


end
end QRH.Record1252270103Source.High.CoupledFirst
#print axioms QRH.Record1252270103Source.High.CoupledFirst.first_input_zero_capped
