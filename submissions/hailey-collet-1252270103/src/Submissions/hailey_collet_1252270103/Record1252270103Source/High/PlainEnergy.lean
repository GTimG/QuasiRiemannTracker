/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.PlainField
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentPositiveSummability CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentHeckeTwist CenteredMomentDetectorDictionary
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainProfileControl
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ConcreteTraceCRT QuadraticInitialBound Cycle61MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ordinary_plain_field {Row : Type*}
    (W : ℝ→ℂ) (bslot bΦ Lslot lo hi ε U m B lam h : ℝ) (hlam : 0≤lam)
    (η η₀ : Character) (Q : Ideal O) (degree J : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (A Cp : ℝ)
    (hinput : InitialAffineAt (α:=α) M H hH ⟨B,lam,0,B,0,h⟩ W bslot (1/4) (9/4) bΦ Lslot lo hi
      1 1 ε U η η₀ Q degree seminorms A)
    (hcontrol : ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      (detectorProfiles false j k σ t).control seminorms ^2≤Cp*(1+‖t‖)^J)
    (hA : 0≤A) (hCp : 0≤Cp) (hU : 1<U)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hm : 0≤m) (hmmax : m≤1)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
    (hwidth : (∑s,w s)≤h) (hcap : 2*m+lam*(∑s,w s)≤B)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
        1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hnorm : ∀u∈rows,‖eisEmbedding (row u)‖^2≤U)
    (j k : ℕ) (hjk : j+k≤2) (σd td : ℝ)
    (hσd : σd∈Icc (0:ℝ) 1) (htd : |td|≤height) :
    (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
      ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
        (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2)≤
      (A*diagonalControl radialMajorant*Cp)*(1+height)^(J+degree)*U^(1+ε) := by
  have hUp : 0<U := zero_lt_one.trans hU
  have hscale : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hlen : length U (U^m)=m := by
    rw [length,max_eq_right (Real.one_le_rpow hU.le hm)]
    exact Real.logb_rpow hUp hU.ne'
  have hpc (n : ℕ) : (detectorSchwartz false n σd td : ℝ→ℂ)=
      twistProfile ((logProfile^[n]) positiveAnnular) σd td := by
    funext y
    simpa [HeckeDetectorCoefficientTransfer.orientedProfile,
      HeckeDetectorCoefficientTransfer.orientedFrequency] using detectorSchwartz_apply false n σd td y
  have hp₁ : ((detectorProfiles false j k σd td).profile 0 : ℝ→ℂ)=
      twistProfile ((logProfile^[j]) positiveAnnular) σd td := by
    simpa only [detectorProfiles,Fin.zero_eta,ite_true] using hpc j
  have hp₂ : ((detectorProfiles false j k σd td).profile 1 : ℝ→ℂ)=
      twistProfile ((logProfile^[k]) positiveAnnular) σd td := by
    simpa only [detectorProfiles,show ¬((1:Fin 2)=0) by decide,ite_false] using hpc k
  have hsum : 0≤∑s,w s := Finset.sum_nonneg (fun s _=>hw s)
  have hmB : m≤B := by nlinarith [mul_nonneg hlam hsum]
  have hadmit : (SourceFace.mk B lam 0 B 0 h).Admissible
      (length U (U^m)) (length U (U^m)) (∑s,w s) 1 := by
    simp only [SourceFace.Admissible,hlen,zero_mul,mul_one]
    exact ⟨hm,hmB,hm,hmB,hsum,hwidth,by linarith⟩
  have hs := initialAffineAt_finite_polynomials M H hH W bslot (1/4) (9/4)
    bΦ Lslot lo hi ε U hUp ⟨B,lam,0,B,0,h⟩ η η₀ Q degree seminorms A hinput
    slots θ w σ v height hw hwm hσlo hσhi hheight hv
    (detectorProfiles false j k σd td) (U^m) (U^m) σd td
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular) hp₁ hp₂
    hscale hscale hadmit radialMajorant hrad rows row hinj χ hrow hkeep radialMajorant_nonneg
    (fun u hu=>radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hUp.le,
      (div_le_one hUp).mpr (hnorm u hu)⟩)
  have hp : (detectorProfiles false j k σd td).control seminorms ^2≤Cp*(1+height)^J :=
    (hcontrol j k hjk σd hσd td).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by simpa only [Real.norm_eq_abs] using add_le_add le_rfl htd) J) hCp)
  apply hs.trans
  change A*diagonalControl radialMajorant*(_)^2*(1+height)^degree*U^(1+ε)≤_
  calc
    _≤A*diagonalControl radialMajorant*(Cp*(1+height)^J)*(1+height)^degree*U^(1+ε) := by
      gcongr
      exact mul_nonneg hA (diagonalControl_nonneg _)
    _=_ := by rw [pow_add];ring

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.ordinary_plain_field
