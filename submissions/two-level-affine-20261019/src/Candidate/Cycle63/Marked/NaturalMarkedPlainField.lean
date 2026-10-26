import Candidate.Cycle63.Marked.NaturalMarkedPlain
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance naturalMarkedPlainFieldFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [Fintype α] in
/-- Fixed-scale actual marked plain field, with the literal row presentation.
The scalar capacity is exactly the marked detector capacity; the fixed base
character consumes only its arbitrarily small conductor allowance `δ`. -/
theorem finite_marked_plain_field {Row : Type*}
    (W : ℝ→ℂ) (bslot bΦ Lslot lo hi ε κ U δ m : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree J : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (A Cp : ℝ)
    (hinput : PositiveAt (α:=α) M H hH W bslot (1/4) (9/4) bΦ 0 1 Lslot lo hi
      2 ε κ U η₀ Q degree seminorms A)
    (hcontrol : ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      (detectorProfiles false j k σ t).control seminorms ^2≤Cp*(1+‖t‖)^J)
    (hA : 0≤A) (hCp : 0≤Cp) (hU : 1<U) (hδ : 0≤δ) (hδmax : δ≤1)
    (hη : (η.modulus.absNorm:ℝ)≤U^δ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hm : 0≤ m) (hmmax : m≤1)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
    (hcap : 2*m+6*κ*(∑s,w s)≤1)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→ Character)
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
      (A*diagonalControl radialMajorant*Cp)*(1+height)^(J+degree)*U^(1+δ+ε) := by
  let st := initialState η (internalQ Q η₀) radialMajorant bΦ U δ hU.le hδ hrad
    radialMajorant_nonneg hη
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
  have hs := actual_finite_marked_polynomials_of_injective M H hH W bslot (1/4) (9/4)
    bΦ 0 1 Lslot lo hi 2 ε κ U η₀ Q degree seminorms A hinput slots θ w σ v height
    hw hwm hσlo hσhi hheight hv st rfl (by change 1+δ≤2;linarith)
    (detectorProfiles false j k σd td) (U^m) (U^m) σd td
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular) hp₁ hp₂
    hscale hscale (Real.rpow_le_rpow_of_exponent_le hU.le hmmax)
    (Real.rpow_le_rpow_of_exponent_le hU.le hmmax)
    (by rw [hlen];change m+m+6*κ*(∑s,w s)≤1+δ;linarith)
    rows row hinj χ hrow hkeep radialMajorant_nonneg
    (fun u hu=>radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hUp.le,
      (div_le_one hUp).mpr (hnorm u hu)⟩)
  have hp : (detectorProfiles false j k σd td).control seminorms ^2≤Cp*(1+height)^J :=
    (hcontrol j k hjk σd hσd td).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by simpa only [Real.norm_eq_abs] using add_le_add le_rfl htd) J) hCp)
  apply hs.trans
  change A*diagonalControl radialMajorant*(_)^2*(1+height)^degree*U^(1+δ+ε)≤_
  calc
    _≤A*diagonalControl radialMajorant*(Cp*(1+height)^J)*(1+height)^degree*U^(1+δ+ε) := by
      gcongr
      exact mul_nonneg hA (diagonalControl_nonneg _)
    _=_ := by rw [pow_add];ring

end
end OAI.SevenEighths.Cycle63MarkedPlain
