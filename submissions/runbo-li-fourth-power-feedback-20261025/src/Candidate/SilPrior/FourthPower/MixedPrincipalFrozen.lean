/- Copyright (c) 2026 Sil. Apache-2.0.
Actual frozen source amplitude for the inner fixed-inducing branch.
No estimate of the source is assumed: the live row is the proved principal
centered row. The full extracted norm and the actual shortened prefix remain.
-/
import Candidate.SilPrior.FourthPower.MixedPrincipalPositivePart
import Candidate.SilPrior.FourthPower.MixedAllocationSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedPrincipalFrozen
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentLattice CenteredMomentTwist CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentSecondHeightFamily
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentSourceLiveColumn
open CenteredMomentSlotNormalization CenteredMomentAllocationCost
open MixedPrincipalCentered MixedPrincipalPositivePart MixedCenteredEnergy
open MixedLiveRows MixedLiveNormalization MixedFrozenSource MixedAllocationSource
open NativeInjectiveEnergy MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem normalization_norm {ι : Type*} [Fintype ι]
    (T : ℝ) (hT : 0≤T) (P : ι→ℝ) (hP : ∀i,0≤P i) :
    ‖normalization T P‖=(Real.sqrt (T*∏i,P i))⁻¹ := by
  rw [normalization,sqrt_product_normalizer T P hT hP,norm_inv,
    Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Exact amplitude version of frozen_live_identity, prior to any bound. -/
theorem frozen_live_norm {ι : Type*} [Fintype ι]
    (B : Tuple ι) (T : ℝ) (hT : 0≤T) (P : ι→ℝ) (hP : ∀i,0≤P i) (c f : ℂ) :
    ‖normalization T P*(c*f)‖=
      (‖c‖/Real.sqrt (∏i,frozenScale B P i))*
        ‖normalization T (fun i : liveIndices B=>P i.val)*f‖ := by
  have hF : 0≤∏i,frozenScale B P i := by
    apply Finset.prod_nonneg
    intro i hi
    unfold frozenScale
    split_ifs
    · exact zero_le_one
    · exact hP i
  have hs : Real.sqrt (T*∏i,P i)=
      Real.sqrt (∏i,frozenScale B P i)*Real.sqrt (T*∏i : liveIndices B,P i.val) := by
    rw [←slot_scale_split B P]
    rw [show T*((∏i,frozenScale B P i)*(∏i : liveIndices B,P i.val))=
      (∏i,frozenScale B P i)*(T*∏i : liveIndices B,P i.val) by ring,
      Real.sqrt_mul hF]
  rw [norm_mul,norm_mul,normalization_norm T hT P hP,
    norm_mul,normalization_norm T hT (fun i : liveIndices B=>P i.val) (fun i=>hP i.val),hs]
  ring

/-- The two square roots and the original prefix yield the full linear
reciprocal rawReduction, rather than a square-root reciprocal. -/
theorem frozen_volume_scalar {ι : Type*} [Fintype ι]
    (B : Tuple ι) (hB : ∀j,B j≠0) (d : Id×Id) (hd : d.1≠0∧d.2≠0)
    (T : ℝ) (hT : 0≤T) (P : ι→ℝ) (hP : ∀i,0<P i) (c : ℂ) :
    (‖c‖/Real.sqrt (∏i,frozenScale B P i))*
      (Real.sqrt (T*∏i : liveIndices B,P i.val)/
        pairNorm (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)))=
      (Real.sqrt (T*∏i,P i)/pairNorm d)*(‖c‖/rawReduction B P) := by
  have hF := Finset.prod_pos (fun i (_ : i∈Finset.univ)=>frozenScale_pos B P hP i)
  have hs : Real.sqrt (T*∏i,P i)=
      Real.sqrt (∏i,frozenScale B P i)*Real.sqrt (T*∏i : liveIndices B,P i.val) := by
    rw [←slot_scale_split B P]
    rw [show T*((∏i,frozenScale B P i)*(∏i : liveIndices B,P i.val))=
      (∏i,frozenScale B P i)*(T*∏i : liveIndices B,P i.val) by ring,
      Real.sqrt_mul hF.le]
  rw [extracted_pair_norm,hs,rawReduction]
  have hFs := (Real.sqrt_pos.mpr hF).ne'
  have hn := (pairNorm_pos hd.1 hd.2).ne'
  have hb := (plainNorm_pos B hB).ne'
  field_simp [hFs,hn,hb,hF.ne']
  ring_nf
  rw [Real.sq_sqrt hF.le]

/-- Linear analogue of frozen_normalized_cost, using the same actual
support argument, independent of any Input-specialized source estimate. -/
theorem frozen_linear_cost {ι : Type*} [Fintype ι]
    (B : Tuple ι) (hB : ∀j,B j≠0) (G R : Id) (hG : G≠0)
    (hprod : finiteTupleProduct B=G) (ν : ι→Id→ℂ)
    (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ) (hP : ∀i,0<P i)
    (hν : ∀i I,‖ν i I‖≤1) (hWnorm : ∀i x,‖Wslot i x‖≤M i)
    (hM : ∀i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hW : ∀i,Function.support (Wslot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B G R ν Wslot P‖/rawReduction B P≤
      ((∏i,M i)*(max 1 b)^Fintype.card ι)/(G.absNorm:ℝ) := by
  have hN : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hraw := rawReduction_pos B hB P hP
  by_cases hz : frozenCoefficient B G R ν Wslot P=0
  · rw [hz,norm_zero,zero_div]
    exact div_nonneg (mul_nonneg
      (Finset.prod_nonneg (fun i _=>zero_le_one.trans (hM i)))
      (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hN.le
  · have hc := frozenCoefficient_norm B G R ν Wslot P M hν hWnorm hM
    have hr := (actual_reduction_norm B hB G R hprod ν Wslot P hP a b ha hW hz).2
    have hi : (1:ℝ)/rawReduction B P≤(max 1 b)^Fintype.card ι/(G.absNorm:ℝ) :=
      (div_le_div_iff₀ hraw hN).mpr (by simpa only [one_mul] using hr)
    calc
      _ ≤ (∏i,M i)/rawReduction B P := div_le_div_of_nonneg_right hc hraw.le
      _ = (∏i,M i)*(1/rawReduction B P) := by ring
      _ ≤ (∏i,M i)*((max 1 b)^Fintype.card ι/(G.absNorm:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (Finset.prod_nonneg (fun i _=>zero_le_one.trans (hM i)))
      _ = _ := by ring

/-- A literal frozen row, with the exact common puncture and original
ordinary prefixes. Constants precede the live index type and profiles.
Only numeric conductor/support conditions and actual inducing remain. -/
theorem uniform_frozen_principal (α Bcap a b ε : ℝ) (hα : 0≤α) (hα4 : α<4/5)
    (hBcap : 0≤Bcap) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧ ∀W₁ W₂ : 𝓢(ℝ,ℂ),
      ∀hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀Z : ℝ,1≤Z→∀Fhole F R : Id,Fhole≠0→(Fhole.absNorm:ℝ)≤Z^Bcap→F≠0→R≠0→
      ∀S H : Finset PrimeIdeal,(∀P∈S,Supported P.val)→(∀P∈H,P.val∣Fhole)→
      ∀(η : Character)(z : O),z≠0→
      (HeckeRowClosure.rowConductorBound η (fixedBadMask*idealGenerator (R*F)) 1 z:ℝ)≤Z^Bcap→
      CenteredExceptionalProfile.FixedInducingRow η Q fixedBadMask 1 z→
      ∀(ι : Type*) [Fintype ι],∀(pool : ι→Finset Id)(ν : ι→Id→ℂ)
        (Wslot : ι→ℝ→ℂ)(P M : ι→ℝ),
      (∀i,0<P i)→(∀i,1≤M i)→(∀i,pool i⊆primeValues S)→
      (∀i I,I∈pool i→Supported I∧(I.absNorm:ℝ)≤2*P i)→
      (∀i I,‖ν i I‖≤1)→(∀i x,‖Wslot i x‖≤M i)→
      (∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2)→
      ∀(B : Tuple ι)(hB : ∀j,B j≠0),(∏i : liveIndices B,2*P i.val)≤Z^Bcap→
      ∀(d : Id×Id)(hd : d.1≠0∧d.2≠0),
      ∀t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L : ℝ,0<L→
      L≤X₁→L≤X₂→L≤Y₁→L≤Y₂→X₁≤U₁→X₂≤U₂→Y₁≤U₁→Y₂≤U₂→
      X₁*X₂=T→Y₁*Y₂=T→
      (∀I,Supported I→((I.absNorm:ℝ)≤b*(U₁/(d.1*B (Sum.inr 0)).absNorm)∨
        (I.absNorm:ℝ)≤b*(U₂/(d.2*B (Sum.inr 1)).absNorm))→primeSupport I⊆primeValues S)→
      ‖frozenRow (naturalCharacter η z) S H pool d hd B hB F R ν Wslot P
          (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
          (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂) b X₁ X₂ Y₁ Y₂‖≤
        (C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
          (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B,256*M i.val)*
          Real.sqrt (T*∏i,P i)/pairNorm d)*
        (((∏i,M i)*2^Fintype.card ι)/(finiteTupleProduct B).absNorm)*
        (max 1 (L/prefixNormMax (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))))^(-α) := by
  obtain ⟨J,control,h00,hbound⟩ := uniform_centered_positive α Bcap a b ε hα hα4 hBcap ha hb hε
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCbound⟩ := hbound Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ Fhole F R hFhole hFcut hF hR S H hS hH η z hz hcond hex
    ι instι pool ν Wslot P M hP hM hpool hp hν hWnorm hW B hB hV d hd
    t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  let e : Id×Id := (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1))
  have he : e.1≠0∧e.2≠0 := ⟨mul_ne_zero hd.1 (hB _),mul_ne_zero hd.2 (hB _)⟩
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  have hvs₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Iic b :=
    (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans (fun x hx=>(hs₁ hx).2)
  have hvs₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Iic b :=
    (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans (fun x hx=>(hs₂ hx).2)
  have hcover (I : Id) (hI : Supported I)
      (hh : (((I.absNorm:ℝ)≤b*(X₁/e.1.absNorm)∨(I.absNorm:ℝ)≤b*(X₂/e.2.absNorm))∨
        ((I.absNorm:ℝ)≤b*(Y₁/e.1.absNorm)∨(I.absNorm:ℝ)≤b*(Y₂/e.2.absNorm)))) :
      primeSupport I⊆primeValues S := by
    apply henclose I hI
    rcases hh with (h|h)|(h|h)
    · exact Or.inl (h.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hXU₁ (Nat.cast_nonneg _)) hb))
    · exact Or.inr (h.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hXU₂ (Nat.cast_nonneg _)) hb))
    · exact Or.inl (h.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hYU₁ (Nat.cast_nonneg _)) hb))
    · exact Or.inr (h.trans (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hYU₂ (Nat.cast_nonneg _)) hb))
  have hid := source_live_profile (naturalCharacter η z) S H pool hpool d hd B hB F R hF hR
    ν Wslot P V₁ V₂ b X₁ X₂ Y₁ Y₂
    (hL.trans_le hX₁) (hL.trans_le hX₂) (hL.trans_le hY₁) (hL.trans_le hY₂)
    (hpX.trans hpY.symm) hvs₁ hvs₂ (natural_character_off_supported η z hz) hcover
  have hchild := hCbound W₁ W₂ hs₁ hs₂ Z hZ Fhole (R*F) hFhole hFcut (mul_ne_zero hR hF)
    S H hS hH η z hz hcond hex (liveIndices B)
    (fun i=>pool i.val) (fun i I=>ν i.val I*Wslot i.val (I.absNorm/P i.val))
    (fun i=>P i.val) (fun i=>M i.val) (fun i=>hP i.val) (fun i=>zero_le_one.trans (hM i.val))
    (fun i I hI=>hp i.val I hI) (fun i I _=>by
      rw [norm_mul]
      exact (mul_le_mul (hν i.val I) (hWnorm i.val _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    hV e he t₁ t₂ X₁ X₂ Y₁ Y₂ U₁ U₂ T L hL hX₁ hX₂ hY₁ hY₂ hXU₁ hXU₂ hYU₁ hYU₂ hpX hpY henclose
  change normalization (X₁*X₂) (fun i : liveIndices B=>P i.val)*
    liveSum (naturalCharacter η z) S H pool d hd B hB F R ν Wslot P V₁ V₂ b X₁ X₂ Y₁ Y₂=
      centeredRow (excluded (naturalCharacter η z) (R*F)) S H
        (fun i : liveIndices B=>pool i.val)
        (fun i I=>ν i.val I*Wslot i.val (I.absNorm/P i.val)) (fun i=>P i.val)
        V₁ V₂ b X₁ X₂ Y₁ Y₂ e at hid
  rw [←hid] at hchild
  let c := frozenCoefficient B (finiteTupleProduct B) R ν Wslot P
  let A := C*(sourceControl control W₁*sourceControl control W₂)*Z^ε*
    (1+‖t₁‖+‖t₂‖)^J*(∏i : liveIndices B,256*M i.val)
  let saving := (max 1 (L/prefixNormMax e))^(-α)
  have hA : 0≤A := by
    have := sourceControl_nonneg control W₁
    have := sourceControl_nonneg control W₂
    have hm : ∀i : liveIndices B,0≤256*M i.val := fun i=>mul_nonneg (by norm_num) (zero_le_one.trans (hM i.val))
    have hp := Finset.prod_nonneg (fun i (_ : i∈Finset.univ)=>hm i)
    have hz0 : 0<Z := zero_lt_one.trans_le hZ
    dsimp [A]
    positivity
  have hsave : 0≤saving := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have hG : finiteTupleProduct B≠0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have hcost := frozen_linear_cost B hB (finiteTupleProduct B) R hG rfl ν Wslot P M hP
    hν hWnorm hM 1 2 (by norm_num) hW
  norm_num only [max_eq_right (show (1:ℝ)≤2 by norm_num)] at hcost
  change ‖normalization (X₁*X₂) P*(c*
    liveSum (naturalCharacter η z) S H pool d hd B hB F R ν Wslot P V₁ V₂ b X₁ X₂ Y₁ Y₂)‖≤_
  rw [frozen_live_norm B (X₁*X₂) (by rw [hpX];exact hT.le) P (fun i=>(hP i).le)]
  apply (mul_le_mul_of_nonneg_left hchild (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).trans
  calc
    _ = A*((‖c‖/Real.sqrt (∏i,frozenScale B P i))*(Real.sqrt (T*∏i : liveIndices B,P i.val)/pairNorm e))*saving := by
      dsimp [A,saving];ring
    _ = A*((Real.sqrt (T*∏i,P i)/pairNorm d)*(‖c‖/rawReduction B P))*saving := by
      rw [frozen_volume_scalar B hB d hd T hT.le P hP c]
    _ ≤ A*((Real.sqrt (T*∏i,P i)/pairNorm d)*
        (((∏i,M i)*2^Fintype.card ι)/(finiteTupleProduct B).absNorm))*saving :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcost (div_nonneg (Real.sqrt_nonneg _) (pairNorm_pos hd.1 hd.2).le)) hA) hsave
    _ = _ := by dsimp [A,saving,e];ring

end
end Candidate.SilPrior.FourthPower.MixedPrincipalFrozen
