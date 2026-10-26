/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite-cardinality uniformity of the genuine masked ordinary-parent transport. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyParent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyControl
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialReferenceScales
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.SourceLift
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record1252270103Source QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

theorem unit_projected_of_ordinary (B lam cap mesh ε δ : ℝ)
    (hB : B≤1) (hlam : 0≤lam) (hδ : 0<δ)
    (hsource : UnitFaceSource (globalFace B lam cap) mesh ε) :
    ProjectedUnitFaceSource (globalFace B lam cap) mesh (ε+2*δ) := by
  intro α _ _ rayM _ H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72 R₀ hR₀
  have hs (T : Finset α):=hsource T rayM H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72
  choose dj Sj Cj hCj hj using hs
  have hp (T : Finset α):=canonical_projected_parent (α:=T) rayM H hH W hsW hW δ hδ
  choose Aj hAj hp using hp
  let D:=∑T : Finset α,dj T
  let S:=Finset.univ.biUnion Sj
  let a:=fun T : Finset α=>Aj T*(R₀.radical.absNorm:ℝ)^δ*Cj T
  have ha (T : Finset α) : 0≤a T:=
    mul_nonneg (mul_nonneg (hAj T).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hCj T).le
  let C:=1+∑T : Finset α,a T*2^(dj T)
  have hC : 0<C:=by
    have hsum:=Finset.sum_nonneg (s:=Finset.univ)
      (fun T _=>mul_nonneg (ha T) (by positivity : 0≤(2:ℝ)^(dj T)))
    dsimp [C];linarith
  have hd (T : Finset α) : dj T≤D:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hS (T : Finset α) : Sj T⊆S:=fun _ hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hCC (T : Finset α) : a T*2^(dj T)≤C := by
    have hh:=Finset.single_le_sum (fun U _=>mul_nonneg (ha U) (by positivity : 0≤(2:ℝ)^(dj U)))
      (Finset.mem_univ T)
    dsimp [C];linarith
  refine ⟨D,S,C,hC,?_⟩
  have hall : ∀ᶠZ : ℝ in atTop,∀T : Finset α,_:=Filter.eventually_all.mpr hj
  filter_upwards [hall,eventually_ge_atTop (6:ℝ)] with Z hsrc hZ6
  intro T θ w σ v t height hw hmesh hσlo hσhi hh hv M hMlo hMhi Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ hadm
  have hM : M=1:=by linarith
  subst M
  have hσ : σ=(fun _=>33/50):=funext (fun i=>le_antisymm (hσhi i) (hσlo i))
  subst σ
  have hZ : 1<Z:=by linarith
  have hw0 : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hcap : (∑i,w i)≤cap:=by simpa [globalFace] using hadm.2.2.2.2.2.1
  have hbudget : length Z X₁+length Z X₂+lam*(∑i,w i)≤B:=by
    simpa [globalFace] using hadm.2.2.2.2.2.2
  have hcut : (9/4:ℝ)^2*X₁*X₂≤Z^(2:ℝ) := by
    have h:=global_reference_cutoff B lam cap Z X₁ X₂ (∑i,w i) 0 hZ6 hX₁ hX₂ hlam hw0 hB hadm
    simpa only [Real.rpow_zero,div_one,mul_one,mul_assoc] using h
  have hparent:=hp T B lam cap (1/4) (9/4) bΦ mesh ε Z hlam (by norm_num) (by norm_num) hZ
    η η₀ Q (dj T) (Sj T) (Cj T) (hCj T).le (hsrc T) θ w v t height hw hmesh hh hv
    hcap p X₁ X₂ hX₁ hX₂ hbudget hcut Φ hsΦ hΦ R₀ hR₀
  have hpow : (Z^δ)^2*Z^(1+ε)=Z^(1+(ε+2*δ)) := by
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le δ 2,
      ←Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    norm_num
    ring
  dsimp only
  intro rows J _ f
  simp only [Real.rpow_one]
  refine (hparent rows J f).trans ?_
  calc
    _=a T*diagonalControl Φ*(p.control (Sj T))^2*(1+|t|+height)^(dj T)*Z^(1+(ε+2*δ)) := by
      rw [←hpow]
      dsimp [a]
      ring
    _≤a T*diagonalControl Φ*(p.control (Sj T))^2*(1+|t|+|t|+height)^(dj T)*Z^(1+(ε+2*δ)) := by
      have hh0 : 0≤1+|t|+height:=by positivity
      have hh1 : 1+|t|+height≤1+|t|+|t|+height:=by linarith [abs_nonneg t]
      have hdiag:=diagonalControl_nonneg Φ
      have haT:=ha T
      gcongr
    _≤_:=source_control_promote p Φ (Sj T) S (hS T) (dj T) D (hd T) (a T) C t height Z
      (1+(ε+2*δ)) (ha T) (hCC T) hh (zero_lt_one.trans hZ).le

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.unit_projected_of_ordinary
