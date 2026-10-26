/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The absolute mass of the actual finite modified coefficient, with constants
uniform over all descendants of the original finite slot type. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstBounds
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.MarkedMainRemainderAllocation
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceInputTailUniform
open CenteredMomentExceptionalAmplitudePair
local notation "O" => HeckeFamily.O
local instance absoluteMassDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def massConstant (N : ℕ) (Cs hi whi : ℝ) : ℝ :=
  4*128^(N+2)*hi^N*whi^2*Cs^N

theorem massConstant_nonneg (N : ℕ) (Cs hi whi : ℝ) (hCs : 0≤Cs) (hhi : 0≤hi) :
    0≤massConstant N Cs hi whi := by unfold massConstant;positivity

/-- The bounded modifier is retained inside the exact tuple-to-column mass
estimate. No masked-column energy is compared with an unmasked one. -/
theorem modified_coefficient_mass {ι : Type*}[Fintype ι]
    (N : ℕ) (Cs hi whi wlo : ℝ) (hCs : 1≤Cs) (hhi : 1≤hi)
    (hwhi : 0≤whi) (hwlo : 0<wlo)
    (s : Input ι) (modifier : Tuple ι→ℂ) (R seed : Ideal O)
    (hN : Fintype.card ι≤N) (hM : ∀i,s.M i≤Cs) (hslot : ∀i,s.hi i≤hi)
    (hmod : ∀v∈Fintype.piFinset s.pools,‖modifier v‖≤2)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (he₁ : s.W₁=W₁) (he₂ : s.W₂=W₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi) :
    (∑I∈finiteColumns (Fintype.piFinset s.pools),‖High.CoupledFirst.coefficient s modifier R seed I‖)≤
      massConstant N Cs hi whi*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
        volume s.toData := by
  have hh:=High.CoupledFirst.input_mass (fun _ : ι=>hi) whi (fun _=>zero_le_one.trans hhi)
    hwhi s modifier 2 (by norm_num) hmod W₁ W₂ wlo hwlo he₁ he₂ hs₁ hs₂ hslot R seed
  have h128:=pow_le_pow_right₀ (by norm_num : (1:ℝ)≤128) (Nat.add_le_add_right hN 2)
  have hhip:=pow_le_pow_right₀ hhi hN
  have hMp:=MarkedMainRemainder.slot_control_product s N Cs hN hCs hM
  have hV : 0≤volume s.toData:=(volume_pos s.toData).le
  have hMP0 : 0≤∏i,s.M i:=Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))
  simp only [Finset.prod_const,Finset.card_univ,plainControl] at hh
  apply hh.trans
  calc
    _=(4*128^(Fintype.card ι+2)*hi^Fintype.card ι*whi^2*(∏i,s.M i))*
        (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*volume s.toData:=by ring
    _≤massConstant N Cs hi whi*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
        volume s.toData := by
      unfold massConstant
      gcongr

end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.massConstant_nonneg
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.modified_coefficient_mass
