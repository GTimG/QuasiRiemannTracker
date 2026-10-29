/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PlainSource
import Candidate.Cycle63.Marked.FinitePositiveEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl

/-! The actual ordinary detector moment from the proved parent source.
Unlike the native marked estimate, the budget here is `2m + Lz ≤ B`. -/
namespace Qrh.JointDetector.RepeatedMarks.ParentMarkedPlain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record12518109Source QRH.Record1252270103Source
open QuadraticInitialBound ConcreteTraceCRT ActualEisensteinCubic ConcretePrimeRowBridge
open Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Literal detector polynomial pair and natural-slot product, with an
injective actual row parametrization, from one parent initial moment. -/
theorem finite_polynomials_of_initial {Row : Type*}
    (B L c U mesh ε bΦ : ℝ) (η η₀ : Character) (Q : Ideal O)
    (W : ℝ→ℂ) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : InitialAffineAt (α:=α) M H hH (globalFace B L c) W 2
      (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε U η η₀ Q degree controls C)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤mesh)
    (hσlo : ∀s,(33/50:ℝ)≤σ s) (hσhi : ∀s,σ s≤33/50)
    (hh : 0≤height) (hv : ∀s,|v s|≤height)
    (Φ : 𝓢(ℝ,ℂ)) (hΦ : Function.support (Φ:ℝ→ℂ)⊆Iic bΦ)
    (hΦp : ∀x,0≤(Φ x).re) (hU : 0<U)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ σd td : ℝ) (V₁ V₂ : ℝ→ℂ)
    (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hadm : (globalFace B L c).Admissible (length U X₁) (length U X₂) (∑s,w s) 1)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η) (fixedBadMask*idealGenerator 1) 1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hone : ∀u∈rows,Φ (‖eisEmbedding (row u)‖^2/U)=1) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2) ≤
      C*diagonalControl Φ*(p.control controls)^2*(1+height)^degree*U^(1+ε) := by
  have he := PlainSource.finite_moment_of_initial M H hH B L c U mesh ε bΦ η η₀ Q W
    degree controls C hinput slots θ w σ v 0 height hw hwm hσlo hσhi hh hv
    Φ hΦ hΦp hU p X₁ X₂ hX₁ hX₂ hadm (rows.image row)
    (fun u hu=>by obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hu;exact hkeep r hr)
    (fun u hu=>by obtain ⟨r,hr,rfl⟩:=Finset.mem_image.mp hu;rw [hone r hr];simp)
  simp only [abs_zero,add_zero] at he
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product η (χ u) (fixedBadMask*idealGenerator 1) 1 (row u)
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=>Real.rpow_pos_of_pos hU _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row η (χ u) (fixedBadMask*idealGenerator 1) 1 (row u) (hrow u hu) _ _ _

/-- The actual plain raw moment supplied by a parent source. The mesh was
chosen by `GlobalSource` before this arbitrary finite copied slot type. All
ordinary Sobolev profiles, independent frequencies and row subsets are uniform. -/
theorem plain_energy_of_unit_source
    (B L c mesh εm : ℝ) (hL : 0≤L)
    (hsource : QRH.Record12518109Existence.UnitFaceSource (globalFace B L c) mesh εm)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (bΦ : ℝ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom η) (fixedBadMask*idealGenerator 1) 1 (1*row u) n) →
      (∀u∈rows,initialKeep η (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2≤U) →
      ∀m : ℝ,0≤m → ∀slots : Finset α,∀θ : slots→RayQuotient.Characters M H,
      ∀w σ v : slots→ℝ,∀height : ℝ,
      (∀s,0≤w s) → (∀s,w s≤mesh) →
      (∀s,(33/50:ℝ)≤σ s) → (∀s,σ s≤33/50) →
      0≤height → (∀s,|v s|≤height) →
      (∑s,w s)≤c → 2*m+L*(∑s,w s)≤B →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  obtain ⟨degree,controls,A,hA,hinput⟩ := hsource α M H hH W hW hWs
    (max 2 bΦ) (le_max_left _ _) η η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨J,Cp,hCp,hprofiles⟩ := paired_control controls
  let C : ℝ := A*(1+diagonalControl radialMajorant)*Cp
  have hdiag : 0≤diagonalControl radialMajorant := diagonalControl_nonneg _
  have hC : 0<C := mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A*diagonalControl radialMajorant*Cp≤C := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA.le) hCp.le
  refine ⟨J+degree,C,hC,?_⟩
  filter_upwards [hinput,eventually_gt_atTop (1:ℝ)] with U hinput hU
  refine ⟨hU,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm slots θ w σ v height hw hwm
    hσlo hσhi hh hv hcap hbudget j k hjk σd hσd td htd
  have hUp : 0<U := zero_lt_one.trans hU
  have hscale : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hlen : length U (U^m)=m := by
    rw [length,max_eq_right (Real.one_le_rpow hU.le hm)]
    exact Real.logb_rpow hUp hU.ne'
  have hadm : (globalFace B L c).Admissible (length U (U^m)) (length U (U^m)) (∑s,w s) 1 := by
    rw [hlen,globalFace_admissible_iff hm hm (Finset.sum_nonneg (fun s _=>hw s)) hL]
    simpa only [mul_one] using And.intro hcap (show m+m+L*(∑s,w s)≤B by linarith)
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
  have he := finite_polynomials_of_initial M H hH B L c U mesh εm (max 2 bΦ) η η₀ Q W
    degree controls A hinput slots θ w σ v height hw hwm hσlo hσhi hh hv
    radialMajorant (hrad.trans (Iic_subset_Iic.mpr (le_max_right _ _))) radialMajorant_nonneg
    hUp (detectorProfiles false j k σd td) (U^m) (U^m) σd td
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular) hp₁ hp₂
    hscale hscale hadm rows row hinj χ hrow hkeep
    (fun u hu=>radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hUp.le,
      (div_le_one hUp).mpr (hnorm u hu)⟩)
  have hp : (detectorProfiles false j k σd td).control controls ^2≤Cp*(1+height)^J :=
    (hprofiles false j k hjk σd hσd td).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by simpa only [Real.norm_eq_abs] using add_le_add le_rfl htd) J) hCp.le)
  apply he.trans
  calc
    _ ≤ (A*diagonalControl radialMajorant*Cp)*(1+height)^(J+degree)*U^(1+εm) := by
      rw [pow_add]
      have hhpow : 0≤(1+height)^degree := pow_nonneg (by linarith) _
      have hZpow : 0≤U^(1+εm) := Real.rpow_nonneg hUp.le _
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
          (mul_nonneg hA.le hdiag)) hhpow) hZpow
      convert hb using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' (by positivity)) (Real.rpow_nonneg hUp.le _)

end
end Qrh.JointDetector.RepeatedMarks.ParentMarkedPlain

#print axioms Qrh.JointDetector.RepeatedMarks.ParentMarkedPlain.plain_energy_of_unit_source
