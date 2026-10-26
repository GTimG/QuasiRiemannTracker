/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.SupportedTuple
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondRemainder
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceInputTailUniform CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson
local notation "O"=>ActualEisensteinCubic.O
local instance zeroTupleDecidable {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

theorem normalized_second_zero (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→
    ∀(s : Input ι)(modifier : Tuple ι→ℂ)(R seed : Ideal O)(factor : ℝ)(W₁ W₂ : 𝓢(ℝ,ℂ)),
    0≤factor→(∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor)→
    s.W₁=W₁→s.W₂=W₂→s.W₁ 0=0→s.W₂ 0=0→seed≠0→
    ∀Λ T : ℝ,0<Λ→0<T→sourceRadius s≤Λ*T→
    (Λ*T<1→sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
      (High.CoupledFirst.coefficient s modifier R seed) s.η s.t=0) ∧
    ∀κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns (Fintype.piFinset s.pools))
      (High.CoupledFirst.coefficient s modifier R seed) s.η s.t‖≤
      C*‖κ‖*(2*(factor*plainControl s W₁ W₂))^2*Λ^(1+ε)*T^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hcard s modifier R seed factor W₁ W₂ hf hmod he₁ he₂ hz₁ hz₂ hseed Λ T hΛ hT hsource
  exact hbound hcard (Fintype.piFinset s.pools)
    (High.CoupledFirst.tupleCoefficient s modifier R seed) s.η s.t
    (2*(factor*plainControl s W₁ W₂)) Λ T
    (mul_nonneg (by norm_num) (mul_nonneg hf (plainControl_nonneg s W₁ W₂))) hΛ hT
    (fun v hv _=>tuple_norm_cap s modifier R seed factor hf W₁ W₂ he₁ he₂ hmod v hv)
    seed hseed
    (fun v _ hn=>profileCoefficient_dvd R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂
      1 1 seed v (High.CoupledFirst.tuple_nonzero s modifier R seed v hn))
    (fun v _ hn=>(tuple_radius s modifier R seed hz₁ hz₂ v hn).2.trans hsource)

theorem normalized_second_zero_radial (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃SΦ : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type*}[Fintype ι],Fintype.card ι≤N→
    ∀(s : Input ι)(modifier : Tuple ι→ℂ)(R seed : Ideal O)(factor : ℝ)(W₁ W₂ : 𝓢(ℝ,ℂ)),
    0≤factor→(∀v∈Fintype.piFinset s.pools,
      High.CoupledFirst.tupleCoefficient s modifier R seed v≠0→‖modifier v‖≤factor)→
    s.W₁=W₁→s.W₂=W₂→s.W₁ 0=0→s.W₂ 0=0→seed≠0→
    ∀Λ T : ℝ,0<Λ→0<T→sourceRadius s≤Λ*T→∀(W : 𝓢(ℝ,ℂ))(H : ℝ),0≤H→
    ‖(((H:ℂ)*paperRadialFourier W 0)/(T:ℂ))*sourceSecondZero
      (finiteColumns (Fintype.piFinset s.pools))
      (High.CoupledFirst.coefficient s modifier R seed) s.η s.t‖≤
      C*(2*(factor*plainControl s W₁ W₂))^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        H*Λ^(1+ε)*T^ε/(seed.absNorm:ℝ) := by
  obtain ⟨C₀,hC₀,hzero⟩:=normalized_second_zero N ε hε
  obtain ⟨SΦ,D,hD,hfourier⟩:=paperRadialFourier_euler_source_weighted_bound 0 0
  refine ⟨SΦ,C₀*D,mul_pos hC₀ hD,?_⟩
  intro ι _ hcard s modifier R seed factor W₁ W₂ hf hmod he₁ he₂ hz₁ hz₂ hseed Λ T hΛ hT hsource W H hH
  have hfour : ‖paperRadialFourier W 0‖≤D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    simpa only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,pow_zero,one_mul,zero_mul] using
      hfourier W 0 le_rfl 0 le_rfl
  have hh:=(hzero hcard s modifier R seed factor W₁ W₂ hf hmod he₁ he₂ hz₁ hz₂ hseed
    Λ T hΛ hT hsource).2 ((H:ℂ)*paperRadialFourier W 0)
  have hk : ‖(H:ℂ)*paperRadialFourier W 0‖=H*‖paperRadialFourier W 0‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hH]
  rw [hk] at hh
  apply hh.trans
  calc
    _≤C₀*(H*(D*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))*
        (2*(factor*plainControl s W₁ W₂))^2*Λ^(1+ε)*T^ε/(seed.absNorm:ℝ) := by gcongr
    _=_ := by ring
end
end QRH.Record1252270103Source.SecondRemainder
#print axioms QRH.Record1252270103Source.SecondRemainder.normalized_second_zero

#print axioms QRH.Record1252270103Source.SecondRemainder.normalized_second_zero_radial
