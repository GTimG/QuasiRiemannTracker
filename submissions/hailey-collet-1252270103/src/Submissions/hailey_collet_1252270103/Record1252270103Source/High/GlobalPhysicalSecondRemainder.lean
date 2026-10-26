/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The corrected second transform with its zero and discarded tail paid.
The remaining finite sum is the literal physical block sum, with its
original complete-zero filter and both complementary row sectors. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSecondSectors
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Zero
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Tail
import Submissions.hailey_collet_1252270103.Record1252270103Source.SecondRemainder.Correction
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy
open CenteredMomentSecondLocalization CenteredMomentSourceSecondZeroEnergy CenteredMomentSecondTail
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open Record1252270103Second SecondRemainder
local notation "O" => ActualEisensteinCubic.O
local instance secondRemainderSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma parent_inverse_norm (T : ℝ) (hT : 0<T) (x : ℂ) :
    ‖(T:ℂ)⁻¹*x‖=‖x‖/T := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  ring

def secondSectorMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (H Tsec Z ξ T : ℝ)
    (keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop) : ℝ :=
  (∑q∈(Finset.univ:Finset (BlockIndex s modifier R seed H Tsec Z ξ)).filter
    (fun q=>Record1252270103Second.originalBlock s modifier R seed W H Tsec Z ξ q≠0),
    ‖blockWeight s modifier R seed H Tsec Z ξ q‖*
      (‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (keep q)‖+
        ‖selectedSecondBlock s modifier R seed W H Tsec Z ξ q (fun z=>¬keep q z)‖))/T

/-- Uniform remainder constants precede the slot type and every moving
parameter. The correction cap two is proved on actual contributing tuples
from the prime pool and original source-radius bound. -/
theorem actual_corrected_second_reduction
    (N : ℕ) (hiMax wlo whi B Bseed ξ saving ε : ℝ)
    (hhi : 0≤hiMax) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B)
    (hξ : 0<ξ) (hε : 0<ε) :
    ∃S₀ S₁ : Finset (ℕ×ℕ),∃C₀ C₁ : ℝ,0<C₀ ∧ 0<C₁ ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{ι : Type*}[Fintype ι][DecidableEq ι],Fintype.card ι≤N→
    ∀(s : Input ι)(A₁ A₂ D K R seed : Ideal O)(P : Finset (Ideal O)),
    P.Nonempty→(∀p∈P,Prime p)→
    ∀ell Bcap : ℝ,0<ell→(∀p∈P,Z^ell≤(p.absNorm:ℝ))→
    2*(Bcap/ell)≤(P.card:ℝ)→sourceRadius s≤Z^Bcap→
    ∀W₁ W₂ : 𝓢(ℝ,ℂ),s.W₁=W₁→s.W₂=W₂→s.W₁ 0=0→s.W₂ 0=0→
    Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
    Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hiMax)→
    seed≠0→(seed.absNorm:ℝ)≤Z^Bseed→
    ∀Λ T : ℝ,0<Λ→0<T→sourceRadius s≤Λ*T→
    ∀(W : 𝓢(ℝ,ℂ))(H Tsec : ℝ),0<H→
    volume s.toData≤Z^B→Tsec≤Z^B→(volume s.toData)^2/H≤Tsec→
    let modifier:=correctedModifier P A₁ A₂ D K (fun _=>1)
    ∀keep : BlockIndex s modifier R seed H Tsec Z ξ→O→Prop,
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=CoupledFirst.coefficient s modifier R seed
    (gaussEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I:supportedColumns S=>β I*((Real.sqrt T:ℂ)⁻¹*
        rowWeight s.η fixedBadMask 1 1 s.t I)) W H).re≤
      C₀*(4*plainControl s W₁ W₂)^2*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        H*Λ^(1+ε)*T^ε/(seed.absNorm:ℝ)+
      secondSectorMass s modifier R seed W H Tsec Z ξ T keep+
      C₁*(2*plainControl s W₁ W₂)^2*S₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        H*(volume s.toData/T)*Z^(-saving)/(seed.absNorm:ℝ) := by
  obtain ⟨S₀,C₀,hC₀,hzero⟩:=normalized_second_zero_radial N ε hε
  obtain ⟨S₁,C₁,hC₁,htail⟩:=normalized_second_tail_seed N hiMax wlo whi B Bseed ξ saving
    hhi hwlo hwhi hB hξ
  refine ⟨S₀,S₁,C₀,C₁,hC₀,hC₁,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ _ hcard s A₁ A₂ D K R seed P hP hp ell Bcap hell hlower hsize hsource
    W₁ W₂ he₁ he₂ hz₁ hz₂ hs₁ hs₂ hshi hseed hseedcap Λ T hΛ hT hsourceT
    W H Tsec hH hV hTsec hnom modifier keep S β
  have hmod:=corrected_one_modifier_bound s A₁ A₂ D K R seed P hP hp Z ell Bcap
    hZ.1 hell hlower hsize hz₁ hz₂ hsource
  have hz:=hzero hcard s modifier R seed 2 W₁ W₂ (by norm_num) hmod
    he₁ he₂ hz₁ hz₂ hseed Λ T hΛ hT hsourceT W H hH.le
  have ht:=hZ.2 hcard s modifier 2 R seed W₁ W₂ (by norm_num) hmod
    he₁ he₂ hs₁ hs₂ hshi hseed hseedcap W H Tsec T hH hT hV hTsec hnom
  have hz' : ‖((H:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t‖/T≤
      C₀*(4*plainControl s W₁ W₂)^2*S₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        H*Λ^(1+ε)*T^ε/(seed.absNorm:ℝ) := by
    have he : (((H:ℂ)*paperRadialFourier W 0)/(T:ℂ))*sourceSecondZero S β s.η s.t=
        (T:ℂ)⁻¹*(((H:ℂ)*paperRadialFourier W 0)*sourceSecondZero S β s.η s.t) := by ring
    rw [he,parent_inverse_norm T hT] at hz
    convert hz using 1 <;> ring
  rw [parent_inverse_norm T hT] at ht
  have he:=actual_second_energy_sector_bound s modifier R seed hz₁ hz₂ T hT W H Tsec Z ξ hH keep
  dsimp only at he
  rw [add_div,add_div] at he
  exact he.trans (add_le_add (add_le_add hz' le_rfl) ht)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.parent_inverse_norm
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_corrected_second_reduction
