/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual finite attaining-descriptor subclasses of the original source rows.
The width floor precedes scale and arrays. No lower slot event is assumed. -/
import Candidate.C092.transport.SourceInverseP6Finite

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentPrimeSlot CenteredMomentHeckeSlots
open QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6CloseDescriptors_bdea6cde0b2e27ea_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

def descriptor (η η₀ : Character) (W : ℝ→ℂ) (Z : ℝ)
    (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ)
    (u : FreeRow) (j : Slot) : ℂ :=
  annularMark M H hH η η₀ W Z (θ j) (w j) (v j) (fun _=>t) u

def measured (η η₀ : Character) (W : ℝ→ℂ) (Z pay : ℝ)
    (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ) (u : FreeRow) : ℝ :=
  response Z pay w (fun j=>‖descriptor M H hH η η₀ W Z θ w v t u j‖^2)

def descriptorRows (rows : Finset FreeRow) (η η₀ : Character) (W : ℝ→ℂ)
    (Z pay b : ℝ) (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ)
    (t : ℝ) (j : Slot) : Finset FreeRow :=
  rows.filter (fun u=>b<w j ∧
    ‖descriptor M H hH η η₀ W Z θ w v t u j‖^2=
      pay*Z^(measured M H hH η η₀ W Z pay θ w v t u*w j))

/-- One fixed constant controls every original descriptor, even at zero width. -/
theorem original_descriptor_bound (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    ∃ F : ℝ,0<F ∧ ∀ Z : ℝ,1<Z → ∀ (η η₀ : Character)
      (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t : ℝ),
      (∀ j,0≤w j) → ∀ (u : FreeRow) j,
        ‖descriptor M H hH η η₀ W Z θ w v t u j‖^2≤F*Z^(w j) := by
  obtain ⟨B,hB,hcoeff⟩ := QRH.Cycle092.TinyCore.original_slot_coefficient_bound W hW hWs
  refine ⟨(256*B)^2,by positivity,?_⟩
  intro Z hZ η η₀ θ w v t hw u j
  have hZp := zero_lt_one.trans hZ
  let P := Z^(w j)
  have hP : 0<P := Real.rpow_pos_of_pos hZp _
  let S := originalPools M H 2 Z w j
  let c := originalCoefficients M H hH η₀ θ W Z w (fun _=>(33/50:ℝ)) v j
  have hh := rowSlot_bound η fixedBadMask 1 u.val S c t (2*P) B (by positivity) hB.le
    (fun I _=>hcoeff _ _ _ _ I hP (by norm_num))
    (fun I _ hI=>QRH.Cycle092.TinyCore.original_slot_norm_cap W hWs _ _ _ _ I hP hI)
  change ‖(Real.sqrt P:ℂ)⁻¹*rowSlot η fixedBadMask 1 u.val S c t‖^2≤(256*B)^2*P
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hP]
  apply (div_le_iff₀ hP).mpr
  nlinarith only [pow_le_pow_left₀ (norm_nonneg _) hh 2]

/-- The actual positive-response rows are covered by finitely many literal
attaining-slot subclasses. Their spike follows from the measured maximum. -/
theorem actual_descriptor_cover (W : ℝ→ℂ) (hW : Continuous W)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) :
    ∃ F : ℝ,0<F ∧ ∀ Z pay b : ℝ,1<Z → 1≤pay → 0<b → F*Z^b≤pay →
    ∀ (η η₀ : Character) (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ)
      (t : ℝ) (rows : Finset FreeRow), (∀ j,0≤w j) →
      (∀ u∈rows,0 < measured M H hH η η₀ W Z pay θ w v t u) →
      (∀ u∈rows,∃ j,u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v t j) ∧
      (∀ (j : Slot) (e : ℝ),
        (∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v t j,
          e ≤ measured M H hH η η₀ W Z pay θ w v t u) →
        ∀ u∈descriptorRows M H hH rows η η₀ W Z pay b θ w v t j,
          b<w j ∧ Z^(e*w j)≤‖descriptor M H hH η η₀ W Z θ w v t u j‖^2) := by
  obtain ⟨F,hF,hbound⟩ := original_descriptor_bound (Slot:=Slot) M H hH W hW hWs
  refine ⟨F,hF,?_⟩
  intro Z pay b hZ hpay hb hcal η η₀ θ w v t rows hw hpositive
  constructor
  · intro u hu
    obtain ⟨j,hj,hattain⟩ := QRH.Cycle092.AttainingMark.maximum_attained Z pay b F w
      (fun j=>‖descriptor M H hH η η₀ W Z θ w v t u j‖^2) hZ (by linarith) hb.le hF.le hw
      (fun _=>sq_nonneg _) (hbound Z hZ η η₀ θ w v t hw u) hcal (hpositive u hu)
    exact ⟨j,Finset.mem_filter.mpr ⟨hu,hj,hattain⟩⟩
  · intro j e he u hu
    obtain ⟨_,hwidth,heq⟩ := Finset.mem_filter.mp hu
    refine ⟨hwidth,?_⟩
    rw [heq]
    apply (Real.rpow_le_rpow_of_exponent_le hZ.le
      (mul_le_mul_of_nonneg_right (he u hu) (hw j))).trans
    exact le_mul_of_one_le_left (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hpay

/-- Response upper windows pay the full original surviving mark product;
zero-width descriptors use the same original coefficient bound. -/
theorem actual_product_upper
    {Z pay F b e : ℝ} (hZ : 1<Z) (hpay : 0<pay) (hb : 0≤b) (hF : 0≤F)
    (hcal : F*Z^b≤pay) (he : 0≤e)
    (η η₀ : Character) (W : ℝ→ℂ) (θ : Slot→RayQuotient.Characters M H)
    (w v : Slot→ℝ) (t : ℝ) (u : FreeRow) (hw : ∀ j,0≤w j)
    (hbound : ∀ j,‖descriptor M H hH η η₀ W Z θ w v t u j‖^2≤F*Z^(w j))
    (hresponse : measured M H hH η η₀ W Z pay θ w v t u≤e) :
    ‖∏ j,descriptor M H hH η η₀ W Z θ w v t u j‖^2≤
      pay^(Fintype.card Slot)*Z^(e*∑ j,w j) := by
  have hzero (j : Slot) (hj : w j=0) :
      ‖descriptor M H hH η η₀ W Z θ w v t u j‖^2≤pay := by
    have h := hbound j
    simp only [hj,Real.rpow_zero,mul_one] at h
    exact h.trans ((le_mul_of_one_le_right hF (Real.one_le_rpow hZ.le hb)).trans hcal)
  have hslots := (response_le_iff_amplitudes w _ hZ hpay hw (fun _=>sq_nonneg _) hzero he).mp hresponse
  calc
    _ = ∏ j,‖descriptor M H hH η η₀ W Z θ w v t u j‖^2 := by rw [norm_prod,Finset.prod_pow]
    _ ≤ ∏ j,pay*Z^(e*w j) := Finset.prod_le_prod₀ (fun _ _=>sq_nonneg _) (fun j _=>hslots j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,←Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]; congr 2; rw [Finset.mul_sum]

#print axioms actual_descriptor_cover
#print axioms actual_product_upper
end
end QRH.Cycle092.SourceInverseP6
