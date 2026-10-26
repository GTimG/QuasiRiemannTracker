/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform polynomial domination of the literal first balanced budget at all
Mellin heights, from actual finite geometry and coefficient bounds. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudget
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudgetCaps
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.FirstAbsoluteBudgetCard
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.FirstAbsoluteBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open Cycle61InitialMass CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentOriginalCommonHarmonic CenteredMomentLogDyadic
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair QuadraticInitialBound
open CenteredMomentFirstAmplificationChoice
open QRH.Record1252270103Source.High.CoupledFirst
open QRH.Record1252270103Source.SecondAbsoluteEnvelope
local notation "O"=>HeckeFamily.O
local instance firstAbsoluteBudgetUniformDecidable {ι:Type*} : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem eventually_balanced_live_budget_absolute
    (N:ℕ)(Cs hi whi wlo lo A D B L ξ:ℝ)
    (hCs:1≤Cs)(hhi:1≤hi)(hwhi:0≤whi)(hwlo:0<wlo)(hlo:0<lo)
    (hA:0≤A)(hD:0≤D)(hB:0≤B)(hL:0≤L)(hξ:0≤ξ) :
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{ι:Type}[Fintype ι][DecidableEq ι]
      (s:Input ι)(modifier:Tuple ι→ℂ)(R seed:Ideal O)(W W₁ W₂:𝓢(ℝ,ℂ))
      (M:ℝ)(hK:0<Z^M),
      Fintype.card ι≤N→(∀i,s.M i≤Cs)→(∀i,1≤s.hi i)→(∀i,s.hi i≤hi)→(∀i,1≤s.P i)→
      0≤s.b₁→0≤s.b₂→lo≤s.lower→
      s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀v,‖modifier v‖≤2)→Squarefree seed→seed≠0→
      0<sourceRadius s→sourceRadius s≤Z^B→volume s≤Z^A→(Z^M)⁻¹≤Z^D→
      |Real.logb Z (volume s)|≤B→
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^L)→
      ∀(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))(t:ℝ),
      balancedLiveBudget reflected s modifier R seed (Z^M) Z ξ M (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^M) Z ξ q)) t≤
      C*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*
        volume s*Z^(10*B+L+2+3*max A D+ξ/2) := by
  obtain ⟨Cl,hCl,hcard⟩:=eventually_full_first_card A D B L ξ hA hD hB hL hξ
  obtain ⟨Ca,hCa,halloc⟩:=allocation_card_cap N
  let S:=2*((geometrySupportConstant N lo wlo wlo)^2+1)
  let E:=3*max A D+ξ/2
  let C₀:=Cl*S*7*Ca*(Cs^N)^2*diagonalControl ballProfile*32*(massConstant N Cs hi whi)^2
  have hS:0<S := by dsimp [S];positivity
  have hE:0≤E := by dsimp [E];positivity
  refine ⟨max 1 C₀,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  filter_upwards [hcard] with Z hcard
  refine ⟨hcard.1,?_⟩
  intro ι instι instDec s modifier R seed W W₁ W₂ M hK hN hM hslot0 hslot hP hb₁ hb₂ hlower
    he₁ he₂ hs₁ hs₂ hmod hs hs0 hpos hsource hV hKi hlog hpool reflected bin t
  have hZ0:0<Z:=zero_lt_one.trans hcard.1
  have hz₁:s.W₁ 0=0:=by
    rw [he₁]
    by_contra hn
    have hh:0∈Function.support (W₁:ℝ→ℂ):=hn
    have :=(hs₁ hh).1
    linarith
  have hz₂:s.W₂ 0=0:=by
    rw [he₂]
    by_contra hn
    have hh:0∈Function.support (W₂:ℝ→ℂ):=hn
    have :=(hs₂ hh).1
    linarith
  have hs₁' (x:ℝ)(hx:s.W₁ x≠0):wlo≤x:=
    (hs₁ (by change W₁ x≠0;simpa only [he₁] using hx)).1
  have hs₂' (x:ℝ)(hx:s.W₂ x≠0):wlo≤x:=
    (hs₂ (by change W₂ x≠0;simpa only [he₂] using hx)).1
  have hbandX:1≤32*Z^E := by
    have hh:=Real.one_le_rpow hcard.1.le hE
    linarith
  have hbound:=balanced_live_budget_finite N Cs hi whi wlo (32*Z^E) (Z^B)
    (S*Z^(7*B)) (Ca*Z^B) (Cl*Z^(B+L+2)) hCs hhi hwhi hwlo hbandX
    (Real.rpow_nonneg hZ0.le _) (mul_nonneg hS.le (Real.rpow_nonneg hZ0.le _))
    (mul_nonneg hCa.le (Real.rpow_nonneg hZ0.le _))
    (mul_nonneg hCl.le (Real.rpow_nonneg hZ0.le _)) s modifier hN hM hslot0 hslot hP
    hb₁ hb₂ hsource hmod W₁ W₂ he₁ he₂ hs₁ hs₂ reflected R seed (Z^M) Z ξ M
    (Real.logb Z (volume s)) hK bin
    (fun q=>normPhase (coordinateBlock s modifier R seed W (Z^M) Z ξ q))
    (fun j _=>canonical_scalar_sq reflected N lo wlo hlo hwlo s modifier R seed W M Z ξ B
      hcard.1 hK hB hN hlower hs hz₁ hz₂ hsource hs₁' hs₂' hlog bin j)
    (fun j _=>halloc s modifier R seed (Z^M) Z ξ B hK hN hs hz₁ hz₂ hsource reflected bin j)
    (hcard.2 s modifier R seed (Z^M) hK bin hs hs0 hz₁ hz₂ hpos hsource hV hKi hpool)
    (fun j _ n hn=>actual_band_scale s modifier R seed (Z^M) Z ξ A D B hK hcard.1.le
      hB hA hD hξ hs hz₁ hz₂ hpos hsource hV hKi bin j n hn) t
  have hprod:Z^(B+L+2)*Z^(7*B)*Z^B*Z^E*Z^B=Z^(10*B+L+2+3*max A D+ξ/2):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    dsimp [E]
    congr 1
    ring
  apply hbound.trans
  calc
    _=C₀*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s*
        (Z^(B+L+2)*Z^(7*B)*Z^B*Z^E*Z^B) := by dsimp [C₀];ring
    _=C₀*(SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)^2*volume s*
        Z^(10*B+L+2+3*max A D+ξ/2) := by rw [hprod]
    _≤_:=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ0.le _)
      apply mul_le_mul_of_nonneg_right _ (volume_pos s).le
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

end
end QRH.Record1252270103Source.FirstAbsoluteBudget
#print axioms QRH.Record1252270103Source.FirstAbsoluteBudget.eventually_balanced_live_budget_absolute
