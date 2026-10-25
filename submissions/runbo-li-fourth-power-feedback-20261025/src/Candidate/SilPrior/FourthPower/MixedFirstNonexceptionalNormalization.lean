/- Copyright (c) 2026 Sil. Apache-2.0.
Sharp normalization of the actual genuine-allocation nonexceptional cost.
FullBudget.nonexceptionalCost unfolds to the literal numerator below.
All fixed, profile and height factors are retained, as are the ordinary
prefix and artificial divisor. No analytical estimate is a premise.
-/
import Candidate.SilPrior.FourthPower.MixedFirstNonexceptionalAllocation
import Candidate.SilPrior.FourthPower.MixedFirstExceptionalNormalization
import Candidate.SilPrior.FourthPower.GlobalSlotSelection

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.MixedFirstNonexceptionalNormalization
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSecondWindowBudget CenteredMomentSecondRadicalBudget
open CenteredMomentFirstMixedAllowance
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedInnerExceptionalBlock
open MixedFirstNonexceptionalAllocation MixedFirstExceptionalNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Every fixed factor of fullCost except Z, the common norm, W, the
artificial divisor and the original prefix. It retains 2^N times 4^N. -/
def profileFactor (s : Source ι a b) (degree : ℕ) (Cp Cg A tp : ℝ) : ℝ :=
  4*(fixedFactor:ℝ)*Cp*Cg*A*b^2*
    heightEnvelope tp^(2*degree)*profileMoment degree^2*
    (2:ℝ)^Fintype.card ι*(∏i,s.M i)^2*((2:ℝ)^Fintype.card ι)^2

theorem profileFactor_nonneg (s : Source ι a b) (degree : ℕ) (Cp Cg A tp : ℝ)
    (hCp : 0≤Cp) (hCg : 0≤Cg) (hA : 0≤A) : 0≤profileFactor s degree Cp Cg A tp := by
  have ht : 0≤heightEnvelope tp := by unfold heightEnvelope;positivity
  unfold profileFactor
  positivity

/-- Exact cancellation of N(tau), V^2 and N(G)^(-2). In particular
neither an inactive-conductor overestimate nor a bound on V is needed. -/
theorem full_cost_reference (s : Source ι a b) (τ : Character) (G Gopp Dart : Id)
    (hG : G≠0) (hDart : Dart≠0) (degree : ℕ)
    (Ccount Cp Cg Z exponent A tp W δ : ℝ) (hZ : 0<Z) (hW : 0<W) :
    (Ccount*(G.absNorm:ℝ)^δ*
      fullCost s.P s.M degree Cp Cg Z exponent A b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2)/reference τ G Gopp (sourceVolume s) Z=
    (Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
      (G.absNorm:ℝ)^δ*Z^(exponent-allowance G Gopp Z)/W := by
  have hg : 0<(G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG)
  have hd : 0<(Dart.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDart)
  have hτ : 0<(τ.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hp := pairNorm_pos s.hd.1 s.hd.2
  have hv := sourceVolume_pos s
  have hpow : 0<Z^(allowance G Gopp Z) := Real.rpow_pos_of_pos hZ _
  have hvolume : s.T*(∏i,s.P i)=sourceVolume s := by
    rw [←s.hpX]
    rfl
  unfold fullCost fixedBudget reference profileFactor
  rw [hvolume,Real.rpow_sub hZ]
  field_simp [hg.ne',hd.ne',hτ.ne',hp.ne',hv.ne',hW.ne',hpow.ne']
  <;> ring

/-- The full actual cost as one exponent, before paying any common
subpower or discarding the nonnegative first allowance. -/
theorem full_cost_reference_power (s : Source ι a b) (τ : Character) (G Gopp Dart : Id)
    (hG : G≠0) (hDart : Dart≠0) (degree : ℕ)
    (Ccount Cp Cg Z exponent A tp W δ : ℝ) (hZ : 1<Z) (hW : 0<W) :
    (Ccount*(G.absNorm:ℝ)^δ*
      fullCost s.P s.M degree Cp Cg Z exponent A b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2)/reference τ G Gopp (sourceVolume s) Z=
    (Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
      Z^(exponent+δ*Real.logb Z (G.absNorm:ℝ)-Real.logb Z W-allowance G Gopp Z) := by
  have hz := zero_lt_one.trans hZ
  have hg : 0<(G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG)
  have hGpow : (G.absNorm:ℝ)^δ=Z^(δ*Real.logb Z (G.absNorm:ℝ)) := by
    rw [mul_comm δ,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hg]
  rw [full_cost_reference s τ G Gopp Dart hG hDart degree Ccount Cp Cg Z exponent A tp W δ hz hW]
  calc
    _=(Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
        Z^(δ*Real.logb Z (G.absNorm:ℝ)+exponent-allowance G Gopp Z)/W := by
      rw [hGpow,mul_assoc,←Real.rpow_add hz,
        show δ*Real.logb Z (G.absNorm:ℝ)+(exponent-allowance G Gopp Z)=
          δ*Real.logb Z (G.absNorm:ℝ)+exponent-allowance G Gopp Z by ring]
    _=(Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
        Z^(δ*Real.logb Z (G.absNorm:ℝ)+exponent-allowance G Gopp Z)/Z^(Real.logb Z W) := by
      rw [Real.rpow_logb hz hZ.ne' hW]
    _=_ := by
      rw [show exponent+δ*Real.logb Z (G.absNorm:ℝ)-Real.logb Z W-allowance G Gopp Z=
        (δ*Real.logb Z (G.absNorm:ℝ)+exponent-allowance G Gopp Z)-Real.logb Z W by ring]
      simp only [Real.rpow_sub hz]
      ring

/-- The common subpower is paid using the FULL ideal norm cap. This
is precisely the actual native slot-deletion exponent at each first side. -/
theorem native_cost_power (s : Source ι a b) (τ : Character) (G Gopp Dart : Id)
    (hG : G≠0) (hDart : Dart≠0) (degree : ℕ) (w : ι→ℝ)
    (Ccount Cp Cg Z A tp W ε δ BG d : ℝ) (hZ : 1<Z) (hW : 0<W)
    (hcount : 0≤Ccount) (hCp : 0≤Cp) (hCg : 0≤Cg) (hA : 0≤A) (hδ : 0≤δ)
    (hGcap : (G.absNorm:ℝ)≤Z^BG) (hWlower : Z^d≤W) :
    (Ccount*(G.absNorm:ℝ)^δ*
      fullCost s.P s.M degree Cp Cg Z ((3/4:ℝ)*(∑i,w i)+2*ε+δ) A b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2)/reference τ G Gopp (sourceVolume s) Z≤
    (Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
      Z^((3/4:ℝ)*(∑i,w i)-d+2*ε+(BG+1)*δ) := by
  have hz := zero_lt_one.trans hZ
  have hg : 0<(G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG)
  have hglog := Real.logb_le_logb_of_le hZ hg hGcap
  rw [Real.logb_rpow hz hZ.ne'] at hglog
  have hwlog := Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz d) hWlower
  rw [Real.logb_rpow hz hZ.ne'] at hwlog
  have hdelta := mul_le_mul_of_nonneg_left hglog hδ
  have hallow := allowance_nonneg G Gopp Z
  rw [full_cost_reference_power s τ G Gopp Dart hG hDart degree Ccount Cp Cg Z
    ((3/4:ℝ)*(∑i,w i)+2*ε+δ) A tp W δ hZ hW]
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) ?_
  · nlinarith
  · exact div_nonneg
      (mul_nonneg hcount (profileFactor_nonneg s degree Cp Cg A tp hCp hCg hA))
      (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- Actual finite slot selection supplies a strict reserve for its
literal complement; all small analytic losses enter only the one total. -/
theorem selected_native_exponent {α : Type*} (J selected : Finset α) (w : α→ℝ)
    (rho mesh ε δ BG : ℝ) (hrho : 0<rho)
    (hspec : GlobalSlotSelection.Specification J w rho mesh selected)
    (hlarge : rho<(∑i∈J,w i)) (hloss : 2*ε+(BG+1)*δ≤rho/800) :
    (3/4:ℝ)*(∑i : ↥(J\selected),w i.val)-(∑i∈selected,w i)+2*ε+(BG+1)*δ≤-rho/800 := by
  classical
  obtain ⟨_,_,_,_,hreserve,_⟩ :=
    GlobalSlotSelection.large_branch J selected w rho mesh hrho hspec hlarge
  rw [Finset.sum_coe_sort (J\selected) w]
  linarith

/-- A source on the actual unselected slots has the required strict
native saving. The only size hypotheses concern N(G) and the actual
selected scale W; no statement about its source energy is assumed. -/
theorem selected_native_cost {α : Type u} (J selected : Finset α) (w : α→ℝ)
    (rho mesh : ℝ) (hrho : 0<rho)
    (hspec : GlobalSlotSelection.Specification J w rho mesh selected)
    (hlarge : rho<(∑i∈J,w i)) (s : Source ↥(J\selected) a b)
    (τ : Character) (G Gopp Dart : Id) (hG : G≠0) (hDart : Dart≠0) (degree : ℕ)
    (Ccount Cp Cg Z A tp W ε δ BG : ℝ) (hZ : 1<Z) (hW : 0<W)
    (hcount : 0≤Ccount) (hCp : 0≤Cp) (hCg : 0≤Cg) (hA : 0≤A) (hδ : 0≤δ)
    (hGcap : (G.absNorm:ℝ)≤Z^BG) (hWlower : Z^(∑i∈selected,w i)≤W)
    (hloss : 2*ε+(BG+1)*δ≤rho/800) :
    (Ccount*(G.absNorm:ℝ)^δ*
      fullCost s.P s.M degree Cp Cg Z
        ((3/4:ℝ)*(∑i : ↥(J\selected),w i.val)+2*ε+δ) A b s.T tp W Dart s.d*
      (τ.modulus.absNorm:ℝ)/(G.absNorm:ℝ)^2)/reference τ G Gopp (sourceVolume s) Z≤
    (Ccount*profileFactor s degree Cp Cg A tp/(pairNorm s.d^2*(Dart.absNorm:ℝ)))*
      Z^(-rho/800) := by
  have hcost := native_cost_power s τ G Gopp Dart hG hDart degree
    (fun i : ↥(J\selected)=>w i.val) Ccount Cp Cg Z A tp W ε δ BG (∑i∈selected,w i)
    hZ hW hcount hCp hCg hA hδ hGcap hWlower
  apply hcost.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ.le
      (selected_native_exponent J selected w rho mesh ε δ BG hrho hspec hlarge hloss))
  exact div_nonneg (mul_nonneg hcount (profileFactor_nonneg s degree Cp Cg A tp hCp hCg hA))
    (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

end
end Candidate.SilPrior.FourthPower.MixedFirstNonexceptionalNormalization
