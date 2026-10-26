/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual common allocation and complete seed-prime extraction discharge every
nested polynomial norm cap in the exceptional physical source estimate. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalPhysical
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open QRH.Record1252270103Source.High.CorrectedCentered
open QRH.Record1252270103Source.ForcedCost
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance correctedAllocatedNormCapsDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma corrected_norm_mono_of_dvd (I J : Ideal O) (hJ : J≠0) (hd : I∣J) :
    (I.absNorm:ℝ)≤J.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
    (map_dvd Ideal.absNorm hd)

lemma corrected_norm_mul_cap (I J : Ideal O) (Z BI BJ : ℝ) (hZ : 0<Z)
    (hI : (I.absNorm:ℝ)≤Z^BI) (hJ : (J.absNorm:ℝ)≤Z^BJ) :
    ((I*J).absNorm:ℝ)≤Z^(BI+BJ) := by
  rw [map_mul,Nat.cast_mul,Real.rpow_add hZ]
  exact mul_le_mul hI hJ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

lemma corrected_allocated_frozen_norm_cap (s : Input ι) (X : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (A₁ A₂ : Ideal O) (Z BA BX : ℝ) (hZ : 0<Z)
    (hA : ((A₁*A₂).absNorm:ℝ)≤Z^BA) (hXcap : (X.absNorm:ℝ)≤Z^BX) :
    (((A₁*B.val (Sum.inr 0))*(A₂*B.val (Sum.inr 1))).absNorm:ℝ)≤Z^(BA+BX) := by
  have hprod : finiteTupleProduct B.val=X := (Finset.mem_filter.mp B.property).2
  have hd : B.val (Sum.inr 0)*B.val (Sum.inr 1)∣X := by
    have hh:=plain_product_dvd_tuple B.val
    rw [hprod] at hh
    exact hh
  have hp := (corrected_norm_mono_of_dvd _ X hX hd).trans hXcap
  have hm : (A₁*B.val (Sum.inr 0))*(A₂*B.val (Sum.inr 1))=
      (A₁*A₂)*(B.val (Sum.inr 0)*B.val (Sum.inr 1)) := by ring
  rw [hm]
  exact corrected_norm_mul_cap _ _ Z BA BX hZ hA hp

lemma corrected_forced_label_norm_cap (s : Input ι) (A₁ A₂ Df K R L : Ideal O)
    (P : Finset (Ideal O)) (hL : Squarefree L) (Z BL : ℝ) (hZ : 0<Z)
    (hLcap : (L.absNorm:ℝ)≤Z^BL)
    (Cf : correctedForcedLabels s A₁ A₂ Df K R L P) :
    ((Cf:Ideal O).absNorm:ℝ)≤Z^(2*BL) := by
  have hd:=marked_forced_label_dvd_square s A₁ A₂ Df K R L (poolCorrection P) hL Cf
  have hh:=(corrected_norm_mono_of_dvd _ (L^2) (pow_ne_zero 2 hL.ne_zero) hd)
  have hpow : (((L^2).absNorm:ℝ))≤Z^(2*BL) := by
    rw [map_pow,Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hLcap 2).trans_eq
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  exact hh.trans hpow

theorem corrected_allocated_caps_of_original (s : Input ι) (X R0 : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) (W₁ W₂ : 𝓢(ℝ,ℂ))
    (b Z BA0 BD0 BR0 BX BL Bpool Bplain ell : ℝ) (depth : ℕ)
    (A₁ A₂ Df K L : Ideal O) (P : Finset (Ideal O))
    (hb : 0≤b) (hZ : 1<Z) (hL : Squarefree L)
    (hW₁ : s.W₁=(W₁:ℝ→ℂ)) (hW₂ : s.W₂=(W₂:ℝ→ℂ)) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (hR : R0≠0) (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hDR : Df∣R0)
    (hA : ((A₁*A₂).absNorm:ℝ)≤Z^BA0) (hD : (Df.absNorm:ℝ)≤Z^BD0)
    (hRcap : (R0.absNorm:ℝ)≤Z^BR0) (hXcap : (X.absNorm:ℝ)≤Z^BX)
    (hLcap : (L.absNorm:ℝ)≤Z^BL)
    (hP : 0<P.card) (hp : ∀p∈P,Prime p) (h16 : ∀p∈P,16≤p.absNorm)
    (hfloor : ∀p∈P,Z^ell≤(p.absNorm:ℝ)) (hupper : ∀p∈P,(p.absNorm:ℝ)≤Z^Bpool)
    (havoid : ∀p∈P,∀i I,I∈s.slots i→¬p∣I)
    (hsize : 2*((BD0+BX+2*BL)/ell+depth+1)≤P.card) (hdepth : Bplain/ell≤depth)
    (hplain : b^2*(s.X₁*s.X₂)≤Z^Bplain) :
    CorrectedAllocatedCaps s X R0 B W₁ W₂ b Z (BA0+BX+2*BL) Bpool Bplain
      (BD0+BX+2*BL) (BR0+BX+2*BL) ell depth A₁ A₂ Df K L P := by
  let sc:=child s X R0 B s.η 0
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hAouter:=corrected_allocated_frozen_norm_cap s X hX B A₁ A₂ Z BA0 BX hZ0 hA hXcap
  have hDouter:=corrected_norm_mul_cap Df X Z BD0 BX hZ0 hD hXcap
  have hRouter:=corrected_norm_mul_cap R0 X Z BR0 BX hZ0 hRcap hXcap
  have hCf : ∀Cf : correctedForcedLabels sc (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1))
      (Df*X) (K*Collision.markedProduct B.val) (R0*X) L P,
      ((Cf:Ideal O).absNorm:ℝ)≤Z^(2*BL) :=
    corrected_forced_label_norm_cap sc _ _ _ _ _ L P hL Z BL hZ0 hLcap
  refine ⟨hW₁,hW₂,hb₁,hb₂,mul_ne_zero hR hX,
    mul_ne_zero hA₁ (alloc_ne s X B _),mul_ne_zero hA₂ (alloc_ne s X B _),
    mul_dvd_mul hDR (dvd_refl X),?_,?_,?_,hP,hp,h16,hfloor,hupper,?_,hsize,hdepth,?_⟩
  · intro Cf Bf
    exact corrected_allocated_frozen_norm_cap sc Cf (forcedLabel_ne_zero L _ Cf) Bf
      (A₁*B.val (Sum.inr 0)) (A₂*B.val (Sum.inr 1)) Z (BA0+BX) (2*BL) hZ0 hAouter (hCf Cf)
  · intro Cf
    exact corrected_norm_mul_cap (Df*X) Cf Z (BD0+BX) (2*BL) hZ0 hDouter (hCf Cf)
  · intro Cf
    exact corrected_norm_mul_cap (R0*X) Cf Z (BR0+BX) (2*BL) hZ0 hRouter (hCf Cf)
  · intro p hp i I hI
    exact havoid p hp i.val I hI
  · have hx₁ : sc.X₁≤s.X₁ := div_le_self s.X₁_pos.le (alloc_norm_ge_one s X B (Sum.inr 0))
    have hx₂ : sc.X₂≤s.X₂ := div_le_self s.X₂_pos.le (alloc_norm_ge_one s X B (Sum.inr 1))
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hx₁ hx₂ sc.X₂_pos.le s.X₁_pos.le) (sq_nonneg b)).trans hplain
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_allocated_caps_of_original
