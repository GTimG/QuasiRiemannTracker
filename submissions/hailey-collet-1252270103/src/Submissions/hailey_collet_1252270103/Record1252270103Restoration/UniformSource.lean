/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.LengthGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
open Record1252270103KernelMass QRH.Record1252270103Source
local notation "O" => HeckeFamily.O

def restorationConstant (δ B : ℝ) : ℝ := ordinaryPrimeMassBound smallPrimes *
  (eulerBound 5 (1/2+δ/(B+2))+eulerBound 432 (1/2+δ/(B+2)))

theorem restorationConstant_pos (δ B : ℝ) : 0<restorationConstant δ B :=
  mul_pos (ordinaryPrimeMassBound_pos _) (add_pos (eulerBound_pos _ _) (eulerBound_pos _ _))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

theorem initialAffineAt_of_squarefree (B lam cap mesh ε Z bΦ : ℝ)
    (hB : 0≤B) (hlam : 0≤lam) (hε : 0<ε) (hZ : 6≤Z)
    (W : ℝ→ℂ) (η η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (controls : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0<C)
    (hsource : SquarefreeInitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 (ε/2) Z η η₀ Q 1 degree controls C) :
    InitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W
      2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls
        (C*(restorationConstant (ε/4) B)^2) := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos
    p X₁ X₂ hX₁ hX₂ hadm
  have hM : M=1 := le_antisymm hMhi hMlo
  subst M
  have hz : 1<Z := by linarith
  have hz0 : 0<Z := zero_lt_one.trans hz
  have hs : 0≤∑i,w i := Finset.sum_nonneg (fun i _=>hw i)
  let V := C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*(1+|t|+height)^degree
  have hV : 0≤V := by
    dsimp [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le (QuadraticInitialBound.diagonalControl_nonneg _))
      (sq_nonneg _)) (pow_nonneg (by positivity) _)
  have h := restoration_energy_transfer η (fixedBadMask*idealGenerator 1) 1
    (p.profile 0) (p.profile 1) (9/4)
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2)
    (fun i=>primePool rayM H 2 (Z^(w i)))
    (fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i=>Z^(w i)) (fun i=>Real.rpow_pos_of_pos hz0 _) t X₁ X₂ hX₁ hX₂
    (initialKeep η (internalQ Q η₀)) Φ (Z^1) (Real.rpow_pos_of_pos hz0 _) hΦpos
    (V*Z^(1+ε/2)) (mul_nonneg hV (Real.rpow_nonneg hz0.le _))
    (ε/4) (B+1) Z (by positivity) (by linarith) hz.le
    (global_raw_product_bound hz hZ hX₁ hX₂ hlam hs hadm) ?_
  · apply h.trans_eq
    have hp : (Z^(ε/4))^2*Z^(1+ε/2)=Z^(1+ε) := by
      rw [←Real.rpow_mul_natCast hz0.le,←Real.rpow_add hz0]
      congr 1
      ring
    have hmass : restorationMassBound (ε/4) (B+1) Z = restorationConstant (ε/4) B*Z^(ε/4) := by
      unfold restorationMassBound restorationConstant
      rw [show B+1+1=B+2 by ring]
      ring
    rw [hmass,mul_pow]
    dsimp [V]
    calc
      _ = (C*(restorationConstant (ε/4) B)^2)*QuadraticInitialBound.diagonalControl Φ*
        (p.control controls)^2*(1+|t|+height)^degree*((Z^(ε/4))^2*Z^(1+ε/2)) := by ring
      _ = _ := by rw [hp]
  intro Y₁ Y₂ hY₁ hY₂ hYX₁ hYX₂
  apply hsource T θ w σ v t height hw hwm hσlo hσhi hh hv 1 le_rfl le_rfl Φ hΦ hΦpos
    p Y₁ Y₂ hY₁ hY₂
  exact globalFace_downward hlam (length_nonneg Z X₁ hz) (length_nonneg Z X₂ hz) hs hadm
    (length_nonneg Z Y₁ hz) (length_nonneg Z Y₂ hz) hs
    (length_mono_raw hz hYX₁) (length_mono_raw hz hYX₂) le_rfl

theorem globalSource_of_squarefree (B lam cap : ℝ) (hB : 0≤B) (hlam : 0≤lam)
    (hsource : UniformSquarefreeUnitFaceSource B lam cap) : GlobalSource B lam cap := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsource⟩ := hsource (ε/2) (by positivity)
  refine ⟨mesh,hmesh,?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q
    hQray hQ0 hQt hQ72 1 one_ne_zero
  refine ⟨degree,controls,C*(restorationConstant (ε/4) B)^2,
    mul_pos hC (sq_pos_of_pos (restorationConstant_pos _ _)),?_⟩
  filter_upwards [hsource,Filter.eventually_ge_atTop (6:ℝ)] with Z hsource hZ
  exact initialAffineAt_of_squarefree rayM H hH B lam cap mesh ε Z bΦ hB hlam hε hZ
    W η η₀ Q degree controls C hC hsource

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.globalSource_of_squarefree
