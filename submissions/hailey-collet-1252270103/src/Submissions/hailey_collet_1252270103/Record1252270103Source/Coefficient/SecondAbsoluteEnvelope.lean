/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A polynomial envelope for the actual joint second normalized sums at every
Mellin height. All hypotheses are finite support, profile or scalar caps. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteEnvelopeMass
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.SecondAbsoluteEnvelopeRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.SecondAbsoluteEnvelope
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve Cycle61InitialMass RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization QuadraticInitialBound
open QRH.Record1252270103Source.High.GlobalPhysical
local notation "O"=>HeckeFamily.O
local instance absoluteEnvelopeDecidable {ι : Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

def envelopeConstant (N : ℕ) (Cs hi whi : ℝ) : ℝ :=
  128*(Fintype.card RayCharacter:ℝ)^2*diagonalControl ballProfile*(massConstant N Cs hi whi)^2

theorem envelopeConstant_nonneg (N : ℕ) (Cs hi whi : ℝ) :
    0≤envelopeConstant N Cs hi whi := by
  unfold envelopeConstant
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (diagonalControl_nonneg _)) (sq_nonneg _)

variable {α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]

/-- The original volume squared remains in the scalar weight sum. This
retains its cancellation against the actual physical normalization. -/
theorem absolute_finite_envelope (N : ℕ) (Cs hi whi wlo X Y : ℝ)
    (hCs : 1≤Cs) (hhi : 1≤hi) (hwhi : 0≤whi) (hwlo : 0<wlo)
    (hX : 1≤X) (hY : 0≤Y) (hN : Fintype.card α≤N)
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ)
    (W₁ W₂ : 𝓢(ℝ,ℂ))
    (hM : ∀l i,(d l).input.M i≤Cs) (hslot : ∀l i,(d l).input.hi i≤hi)
    (hmod : ∀l,∀v∈Fintype.piFinset (d l).input.pools,‖modifier l v‖≤2)
    (he₁ : ∀l,(d l).input.W₁=W₁) (he₂ : ∀l,(d l).input.W₂=W₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hrows : ∀l,∀z∈(d l).rows,normValue z≤X)
    (hpool : ∀l,∀I∈finiteColumns (Fintype.piFinset (d l).input.pools),(I.absNorm:ℝ)≤Y) :
    secondAbsoluteBudget d modifier w≤envelopeConstant N Cs hi whi*
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*(X*Y)*
      (∑l,‖w l‖*(d l).block.outside*(volume (d l).input.toData)^2) := by
  let C:=massConstant N Cs hi whi
  let P:=SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂
  let f:=fun l=>‖w l‖*(d l).block.outside*(volume (d l).input.toData)^2
  have hC:0≤C:=massConstant_nonneg N Cs hi whi (zero_le_one.trans hCs) (zero_le_one.trans hhi)
  have hP:0≤P:=by dsimp only [P];positivity
  have hf:∀l,0≤f l:=fun l=>mul_nonneg
    (mul_nonneg (norm_nonneg _) (second_outside_pos _).le) (sq_nonneg _)
  have hm (l:Label):
      (∑I∈finiteColumns (Fintype.piFinset (d l).input.pools),
        ‖High.CoupledFirst.coefficient (d l).input (modifier l) (d l).R (d l).seed I‖)≤
      C*P*volume (d l).input.toData := by
    have hn:Fintype.card (d l).slots≤N:=by
      simpa only [Fintype.card_coe] using (Finset.card_le_univ (d l).slots).trans hN
    exact modified_coefficient_mass N Cs hi whi wlo hCs hhi hwhi hwlo
      (d l).input (modifier l) (d l).R (d l).seed hn (hM l) (hslot l) (hmod l)
      W₁ W₂ (he₁ l) (he₂ l) hs₁ hs₂
  have hpoint (r:SecondRow (fun l=>modifiedDatumBlock (d l) (modifier l))):
      ‖w r.1‖*(d r.1).block.outside*
        ((secondResidualIdeals (fun l=>modifiedDatumBlock (d l) (modifier l)) r).card:ℝ)*
        (∑I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),
          ‖High.CoupledFirst.coefficient (d r.1).input (modifier r.1) (d r.1).R (d r.1).seed I‖)^2≤
      (128*C^2*P^2*Y)*f r.1 := by
    have hr:=second_residual_card d modifier r Y hY (hpool r.1)
    have hv:0≤volume (d r.1).input.toData:=(volume_pos _).le
    have ho:0≤(d r.1).block.outside:=(second_outside_pos _).le
    have hmass0:0≤∑I∈finiteColumns (Fintype.piFinset (d r.1).input.pools),
        ‖High.CoupledFirst.coefficient (d r.1).input (modifier r.1) (d r.1).R (d r.1).seed I‖:=
      Finset.sum_nonneg (fun I _=>norm_nonneg _)
    calc
      _≤‖w r.1‖*(d r.1).block.outside*(128*Y)*(C*P*volume (d r.1).input.toData)^2:=by gcongr;exact hm r.1
      _=_:=by dsimp only [f];ring
  unfold secondAbsoluteBudget
  calc
    _≤∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),(128*C^2*P^2*Y)*f r.1:=
      Finset.sum_le_sum (fun r _=>hpoint r)
    _=(128*C^2*P^2*Y)*(∑r∈secondLiveRows (fun l=>modifiedDatumBlock (d l) (modifier l)),f r.1):=
      (Finset.mul_sum _ _ _).symm
    _≤(128*C^2*P^2*Y)*((Fintype.card RayCharacter:ℝ)^2*diagonalControl ballProfile*X*(∑l,f l)):=
      mul_le_mul_of_nonneg_left (second_live_weighted_rows d modifier f hf X hX hrows) (by positivity)
    _=_:=by dsimp only [envelopeConstant,C,P,f];ring

/-- The scalar caps bound the literal absolute budget. The result therefore
holds at all two-dimensional Mellin heights, not just in a detector window. -/
theorem polynomial_second_envelope (N : ℕ) (Cs hi whi wlo Cl Cw Bpool Brows Bl Bw Z : ℝ)
    (hCs : 1≤Cs) (hhi : 1≤hi) (hwhi : 0≤whi) (hwlo : 0<wlo)
    (hCl : 0≤Cl) (hCw : 0≤Cw) (hBrows : 0≤Brows) (hZ : 1<Z)
    (hN : Fintype.card α≤N) (hlabels : (Fintype.card Label:ℝ)≤Cl*Z^Bl)
    (d : Label→SecondInputDatum α) (modifier : ∀l,Tuple (d l).slots→ℂ) (w : Label→ℂ)
    (W₁ W₂ : 𝓢(ℝ,ℂ))
    (hM : ∀l i,(d l).input.M i≤Cs) (hslot : ∀l i,(d l).input.hi i≤hi)
    (hmod : ∀l,∀v∈Fintype.piFinset (d l).input.pools,‖modifier l v‖≤2)
    (he₁ : ∀l,(d l).input.W₁=W₁) (he₂ : ∀l,(d l).input.W₂=W₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi)
    (hrows : ∀l,∀z∈(d l).rows,normValue z≤Z^Brows)
    (hpool : ∀l,∀I∈finiteColumns (Fintype.piFinset (d l).input.pools),(I.absNorm:ℝ)≤Z^Bpool)
    (hweight : ∀l,‖w l‖*(d l).block.outside*(volume (d l).input.toData)^2≤Cw*Z^Bw) :
    let bound:=envelopeConstant N Cs hi whi*Cl*Cw*
      (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
      Z^(Brows+Bpool+Bl+Bw)
    secondAbsoluteBudget d modifier w≤bound ∧
      ∀(reflected:Bool)(t u:ℝ),modifiedSecondNormalizedSum reflected d modifier w t u≤bound := by
  have hz:=zero_lt_one.trans hZ
  have hsum:(∑l,‖w l‖*(d l).block.outside*(volume (d l).input.toData)^2)≤Cl*Cw*Z^(Bl+Bw) := by
    calc
      _≤∑l:Label,Cw*Z^Bw:=Finset.sum_le_sum (fun l _=>hweight l)
      _=(Fintype.card Label:ℝ)*(Cw*Z^Bw):=by simp
      _≤(Cl*Z^Bl)*(Cw*Z^Bw):=mul_le_mul_of_nonneg_right hlabels (by positivity)
      _=_:=by rw [Real.rpow_add hz];ring
  have henv:=absolute_finite_envelope N Cs hi whi wlo (Z^Brows) (Z^Bpool)
    hCs hhi hwhi hwlo (Real.one_le_rpow hZ.le hBrows) (Real.rpow_nonneg hz.le _)
    hN d modifier w W₁ W₂ hM hslot hmod he₁ he₂ hs₁ hs₂ hrows hpool
  have hc:=envelopeConstant_nonneg N Cs hi whi
  have hb:secondAbsoluteBudget d modifier w≤
      envelopeConstant N Cs hi whi*Cl*Cw*
        (SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
        Z^(Brows+Bpool+Bl+Bw) := by
    apply henv.trans
    calc
      _≤envelopeConstant N Cs hi whi*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
          (Z^Brows*Z^Bpool)*(Cl*Cw*Z^(Bl+Bw)):=mul_le_mul_of_nonneg_left hsum (by positivity)
      _=_:=by simp only [Real.rpow_add hz];ring
  exact ⟨hb,fun reflected t u=>(modified_second_normalized_absolute reflected d modifier w t u).trans hb⟩
end
end QRH.Record1252270103Source.SecondAbsoluteEnvelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.envelopeConstant_nonneg
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.absolute_finite_envelope
#print axioms QRH.Record1252270103Source.SecondAbsoluteEnvelope.polynomial_second_envelope
