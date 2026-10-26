import Candidate.Uneven.AuxiliaryInitialContract
import Candidate.Cycle63.Marked.NaturalMarkedPlainField
import Candidate.Uneven.MixedAuxiliaryFixedInitialSupplier
import Candidate.Cycle63.Marked.ActualMarkedPlainProfiles
import Candidate.Cycle63.Marked.NaturalSlotHeight

/- Original module: Candidate.Uneven.AuxiliaryPlainTransport. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonMaskExpansion
open CenteredMomentPrimeSlot CenteredMomentHeckeSlots CenteredMomentHeckeTwist
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The auxiliary initial energy controls the literal finite detector sum.
The initial-energy theorem remains an explicit input to this transport. -/
theorem finite_marked_polynomials_of_initial {Row : Type*}
    (W : ℝ→ℂ) (bslot a b bΦ mesh lo hi ε U : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W bslot a b bΦ
      mesh lo hi 1 1 ε U η η₀ Q degree seminorms C)
    (hU : 1< U)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0 ≤ w s) (hwm : ∀s,w s ≤ mesh)
    (hσlo : ∀s,lo ≤ σ s) (hσhi : ∀s,σ s ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀s,|v s| ≤ height)
    (p : Profiles a b) (X₁ X₂ σd td : ℝ) (V₁ V₂ : ℝ→ℂ)
    (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0< X₁) (hX₂ : 0< X₂)
    (hl₁ : AuxiliaryInitial.plainLower ≤ length U X₁)
    (hu₁ : length U X₁ ≤ AuxiliaryInitial.plainUpper)
    (hl₂ : AuxiliaryInitial.plainLower ≤ length U X₂)
    (hu₂ : length U X₂ ≤ AuxiliaryInitial.plainUpper)
    (hwl : Sil.Uneven.AuxiliarySource.widthLo ≤ ∑s,w s)
    (hwu : (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi)
    (hcap : length U X₁+length U X₂+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s)
       ≤ Sil.Uneven.AuxiliarySource.B)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
        1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hnorm : ∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2) ≤ 
      C*diagonalControl radialMajorant*(p.control seminorms)^2*
        (1+height)^degree*U^(1+ε) := by
  let mask := CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1
  have hUp : 0< U := zero_lt_one.trans hU
  have he := finite_positive_energy (Slot:=slots) (rows.image row) η mask 1 0
    (p.profile 0) (p.profile 1) b b X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2)
    hX₁ hX₂ (fun s=> primePool M H bslot (U^(w s)))
    (fun s I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
    (fun s=> U^(w s)) (initialKeep η (internalQ Q η₀)) radialMajorant U hUp
    (fun u hu=> by obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu; exact hkeep v hv)
    radialMajorant_nonneg
    (fun u hu=> by
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
      exact radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hUp.le,
        (div_le_one hUp).mpr (hnorm v hv)⟩)
  have hi := hinput slots θ w σ v 0 height hw hwm hσlo hσhi hheight hv
    1 le_rfl le_rfl radialMajorant hrad radialMajorant_nonneg p X₁ X₂ hX₁ hX₂
    (by simpa only [mul_one] using hl₁) (by simpa only [mul_one] using hu₁)
    (by simpa only [mul_one] using hl₂) (by simpa only [mul_one] using hu₂)
    (by simpa only [mul_one] using hwl) (by simpa only [mul_one] using hwu)
    (by simpa only [mul_one] using hcap)
  simp only [Real.rpow_one,abs_zero,add_zero] at hi
  have he := he.trans hi
  rw [Finset.sum_image (fun x _ y _ h=> hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product η (χ u) mask 1 (row u)
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=> Real.rpow_pos_of_pos hUp _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row η (χ u) mask 1 (row u) (hrow u hu) _ _ _

/-- Polynomial profile control gives the precise two-plain moment required
by the seventh counting face, with the same selected-width interval. -/
theorem finite_marked_plain_field {Row : Type*}
    (W : ℝ→ℂ) (bslot bΦ mesh lo hi ε U m : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree J : ℕ)
    (seminorms : Finset (ℕ×ℕ)) (A Cp : ℝ)
    (hinput : AuxiliaryInitial.InitialAffineAt (α:=α) M H hH W bslot (1/4) (9/4)
      bΦ mesh lo hi 1 1 ε U η η₀ Q degree seminorms A)
    (hcontrol : ∀j k : ℕ,j+k ≤ 2 → ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      (detectorProfiles false j k σ t).control seminorms ^2 ≤ Cp*(1+‖t‖)^J)
    (hA : 0 ≤ A) (hCp : 0 ≤ Cp) (hU : 1< U)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hm : AuxiliaryInitial.plainLower ≤ m) (hmmax : m ≤ AuxiliaryInitial.plainUpper)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0 ≤ w s) (hwm : ∀s,w s ≤ mesh)
    (hσlo : ∀s,lo ≤ σ s) (hσhi : ∀s,σ s ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀s,|v s| ≤ height)
    (hwl : Sil.Uneven.AuxiliarySource.widthLo ≤ ∑s,w s)
    (hwu : (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi)
    (hcap : 2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom η)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
        1 (1*row u) n)
    (hkeep : ∀u∈rows,initialKeep η (internalQ Q η₀) (row u))
    (hnorm : ∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U)
    (j k : ℕ) (hjk : j+k ≤ 2) (σd td : ℝ)
    (hσd : σd∈Icc (0:ℝ) 1) (htd : |td| ≤ height) :
    (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
      polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2) ≤ 
      (A*diagonalControl radialMajorant*Cp)*(1+height)^(J+degree)*U^(1+ε) := by
  have hUp : 0< U := zero_lt_one.trans hU
  have hm0 : 0 ≤ m := (by norm_num [AuxiliaryInitial.plainLower] : (0:ℝ) ≤ AuxiliaryInitial.plainLower).trans hm
  have hscale : 0< U^m := Real.rpow_pos_of_pos hUp _
  have hlen : length U (U^m)=m := by
    rw [length,max_eq_right (Real.one_le_rpow hU.le hm0)]
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
  have hs := finite_marked_polynomials_of_initial M H hH W bslot (1/4) (9/4)
    bΦ mesh lo hi ε U η η₀ Q degree seminorms A hinput hU slots θ w σ v height
    hw hwm hσlo hσhi hheight hv (detectorProfiles false j k σd td) (U^m) (U^m) σd td
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular) hp₁ hp₂ hscale hscale
    (by simpa only [hlen] using hm) (by simpa only [hlen] using hmmax)
    (by simpa only [hlen] using hm) (by simpa only [hlen] using hmmax)
    hwl hwu (by rw [hlen]; linarith only [hcap]) rows row hinj χ hrow hkeep hnorm hrad
  have hp : (detectorProfiles false j k σd td).control seminorms ^2 ≤ Cp*(1+height)^J :=
    (hcontrol j k hjk σd hσd td).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by simpa only [Real.norm_eq_abs] using add_le_add le_rfl htd) J) hCp)
  apply hs.trans
  calc
    _ ≤ A*diagonalControl radialMajorant*(Cp*(1+height)^J)*(1+height)^degree*U^(1+ε) := by
      gcongr
      exact mul_nonneg hA (diagonalControl_nonneg _)
    _=_ := by rw [pow_add];ring

end
end OAI.SevenEighths.AuxiliaryPlainTransport
end

/- Original module: Candidate.Uneven.MixedAuxiliaryActualPlain. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual auxiliary two-plain moment for a fixed natural seed.
The profile constant, height degree and threshold precede all selected slots
and finite rows. The small mesh is fixed by the requested error alone. -/
theorem actual_marked_plain_energy_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ εm mesh : ℝ) (hbΦ : 2 ≤ bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,1< U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom (excluded F₀.character R₀))
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep (excluded F₀.character R₀) (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U) →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)(height : ℝ),
      (∀s,0 ≤ w s) → (∀s,w s ≤ mesh) →
      (∀s,(33/50:ℝ) ≤ σ s) → (∀s,σ s ≤ (33/50:ℝ)) →
      0 ≤ height → (∀s,|v s| ≤ height) →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s,w s) →
      (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td| ≤ height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  obtain ⟨degree,seminorms,A,hA,hinput⟩:=AuxiliaryAssembly.fixed_natural_initial_affine_mixed_anchor (α:=α)
    M H hH Sbad hbad W hW hWs hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72
    εm mesh bΦ hεm hmesh0 hmesh hbΦ
  obtain ⟨J,Cp,hCp,hprofiles⟩:=paired_control seminorms
  let C : ℝ := A*(1+diagonalControl radialMajorant)*Cp
  have hdiag : 0 ≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC : 0< C:=mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A*diagonalControl radialMajorant*Cp ≤ C := by
    dsimp [C]
    gcongr
    linarith
  refine ⟨J+degree,C,hC,?_⟩
  filter_upwards [hinput,eventually_gt_atTop (1:ℝ)] with U hinput hU
  refine ⟨hU,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have he:=finite_marked_plain_field M H hH W 2 bΦ mesh (33/50) (33/50) εm U m
    (excluded F₀.character R₀) η₀ Q degree J seminorms A Cp hinput (hprofiles false)
    hA.le hCp.le hU hrad hm hmmax slots θ w σ v height hw hwm hσlo hσhi hheight hv
    hwl hwu hcap rows row hinj χ hrow hkeep hnorm j k hjk σd td hσd htd
  exact he.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC' (by positivity))
    (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end
end OAI.SevenEighths.AuxiliaryPlainTransport
end

/- Original module: Candidate.Uneven.MixedAuxiliaryPlainCommonProfiles. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_common_profiles_marked_plain_energy_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ εm mesh : ℝ) (hbΦ : 2 ≤ bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (N : ℕ) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,1< U ∧ ∀node : Fin (N+1),
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom (excluded F₀.character R₀))
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep (excluded F₀.character R₀) (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U) →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)(height : ℝ),
      (∀s,0 ≤ w s) → (∀s,w s ≤ mesh) →
      (∀s,(33/50:ℝ) ≤ σ s) → (∀s,σ s ≤ (33/50:ℝ)) →
      0 ≤ height → (∀s,|v s| ≤ height) →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s,w s) →
      (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td| ≤ height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val) (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  have hnode (node : Fin (N+1)) := actual_marked_plain_energy_mixed_anchor (α:=α) M H hH Sbad hbad
    (Cycle63MarkedHeight.commonProfile W node.val)
    ((Cycle63MarkedHeight.commonProfile_support W node.val).trans hWs)
    (Cycle63MarkedHeight.commonProfile_smooth W 1 2 (by norm_num) hWs hW node.val)
    bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72
  choose J C hC hb using hnode
  have hne : (Finset.univ : Finset (Fin (N+1))).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hC₀ : 0<∑node,C node := Finset.sum_pos (fun node _=> hC node) hne
  refine ⟨∑node,J node,∑node,C node,hC₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb] with U hU
  refine ⟨(hU ⟨0,by omega⟩).1,?_⟩
  intro node Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have he := (hU node).2 rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwl hwu hcap j k hjk σd hσd td htd
  have hc : C node ≤ ∑node,C node := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
  have hj : J node ≤ ∑node,J node := Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ node)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans (hU node).1).le _)
  exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hj) (by positivity) hC₀.le

end
end OAI.SevenEighths.AuxiliaryPlainTransport
end

/- Original module: Candidate.Uneven.MixedAuxiliaryPlainRowwise. -/
section
/- Independent coarse seed and relative anchor; no extra analytic premise. -/
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.AuxiliaryPlainTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainProfileControl CenteredMomentDetectorDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open QuadraticInitialBound ConcreteTraceCRT Cycle63MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_rowwise_marked_plain_energy_mixed_anchor
    (Sbad : Finset (Ideal O)) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (bΦ εm mesh : ℝ) (hbΦ : 2 ≤ bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hεm : 0<εm) (hmesh0 : 0< mesh) (hmesh : mesh ≤ AuxiliaryAssembly.sourceMesh εm)
    (hβlo : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ηcoarse η₀ : Character) (u₀ : O) (F₀ : NaturalRow ηcoarse u₀) (R₀ : Ideal O) (hu₀ : u₀≠0)
    (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀≠0)
    (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) :
    ∃J : ℕ,∃C : ℝ,0< C ∧ ∀ᶠU : ℝ in atTop,1< U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom (excluded F₀.character R₀))
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep (excluded F₀.character R₀) (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2 ≤ U) →
      ∀m : ℝ,AuxiliaryInitial.plainLower ≤ m → m ≤ AuxiliaryInitial.plainUpper →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)(height : ℝ)(choice : Row→ℝ),
      (∀s,0 ≤ w s) → (∀s,w s ≤ mesh) →
      (∀s,(33/50:ℝ) ≤ σ s) → (∀s,σ s ≤ (33/50:ℝ)) →
      0 ≤ height → (∀s,|v s| ≤ height) → (∀u∈rows,|choice u| ≤ height) →
      Sil.Uneven.AuxiliarySource.widthLo ≤ (∑s,w s) →
      (∑s,w s) ≤ Sil.Uneven.AuxiliarySource.widthHi →
      2*m+Sil.Uneven.AuxiliarySource.lambda*(∑s,w s) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀j k : ℕ,j+k ≤ 2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td| ≤ height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,naturalSlot (χ u) (primePool M H 2 (U^(w s)))
          (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (choice u+v s) I)
          (U^(w s))‖^2) ≤ C*(1+height)^J*U^(1+εm) := by
  let N := Fintype.card α
  obtain ⟨J,C,hC,hfield⟩ := actual_common_profiles_marked_plain_energy_mixed_anchor (α:=α) M H hH
    Sbad hbad W hWs hW bΦ εm mesh hbΦ hrad hεm hmesh0 hmesh hβlo hβhi
    ηcoarse η₀ u₀ F₀ R₀ hu₀ Q hQM hQ0 hQt hQ72 N
  let K := Cycle63MarkedHeight.commonProfileCost N
  have hK : 0< K := zero_lt_one.trans_le (Cycle63MarkedHeight.commonProfileCost_ge_one N)
  refine ⟨J+1,4*K*C*2^J,by positivity,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height choice
    hw hwm hσlo hσhi hheight hv hchoice hwl hwu hcap j k hjk σd hσd td htd
  have hUp : 0< U := zero_lt_one.trans hU.1
  let factor := fun u=> polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
    polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td
  let E := C*(1+2*height)^J*U^(1+εm)
  have hE : 0≤ E := by dsimp [E];positivity
  have hcard : (Finset.univ : Finset slots).card≤ N := by
    simpa only [Finset.card_univ,Fintype.card_coe] using Finset.card_le_univ slots
  have hmoment (node : Fin (N+1)) (t : ℝ)(ht : t∈Icc (-height) height) :
      (∑u∈rows,‖factor u*(∏s : slots,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
        (CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
        (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val)
            (U^(w s)) (σ s) (t+v s) I) (U^(w s)))‖^2)≤ E := by
    apply (hU.2 node) rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ
      (fun s=> t+v s) (2*height) hw hwm hσlo hσhi (by positivity)
    · intro s
      exact (abs_add_le t (v s)).trans (by linarith [abs_le.mpr ht,hv s])
    · exact hwl
    · exact hwu
    · exact hcap
    · exact hjk
    · exact hσd
    · linarith
  have he := Cycle63MarkedHeight.naturalSlot_rowwise_energy rows (Finset.univ : Finset slots)
    N hcard χ (fun s=> CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
    (fun s _ I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun s I=> idealCoeff (relativeCharacter M H hH η₀ (θ s)) I) W
    (fun s=> U^(w s)) σ v
    (fun s _=> Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) factor
    (-height) height E (by linarith) hE choice
    (fun u hu=> abs_le.mp (hchoice u hu)) hmoment
  apply he.trans
  have hheight' : 1+2*(height- -height)≤4*(1+height) := by linarith
  have hpow : (1+2*height)^J≤2^J*(1+height)^J := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  change (1+2*(height- -height))*K*(C*(1+2*height)^J*U^(1+εm))≤ _
  calc
    _≤(4*(1+height))*K*(C*(2^J*(1+height)^J)*U^(1+εm)) := by
      gcongr
    _=_ := by rw [pow_succ];ring

end
end OAI.SevenEighths.AuxiliaryPlainTransport
end
