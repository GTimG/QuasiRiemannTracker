/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected forced-prime norm and polynomial caps; no energy assumptions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedForcedGeometryData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedForcedGeometry
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open Record1252270103Second Record1252270103Source Collision
open JointForced
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

/-- Both actually allocated portions divide the complete common factor. -/
theorem allocated_parts_dvd (s:Input ι) (C:Ideal O) (B:actualAllocations s.pools C) :
    B.val (Sum.inr 0)*B.val (Sum.inr 1)∣C ∧ markedProduct B.val∣C := by
  have hb:finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
  have hp:=plain_product_dvd_tuple B.val
  rw [hb] at hp
  refine ⟨hp,?_⟩
  simpa only [one_mul] using marked_puncture_invariant 1 1 C B.val (dvd_refl 1) hb

lemma norm_le_of_dvd (I C:Ideal O) (hC:C≠0) (hIC:I∣C) :
    (I.absNorm:ℝ)≤C.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm hIC)

variable (s:Input ι) (A₁ A₂ D K R L:Ideal O) (F:Ideal O→ℂ)
local notation "Mod"=>markedSourceModifier (ι:=ι) A₁ A₂ D K F
local notation "Idx"=>ChildIndex s Mod R L

/-- Valuation-two support is read from the actual modified column. No
unmodified support, disjoint-pool premise or replacement norm is used. -/
theorem selected_common_bound (hL:Squarefree L) (p:Idx) :
    L∣(p.1:Ideal O) ∧ (p.1:Ideal O)∣L^2 ∧ ((p.1:Ideal O).absNorm:ℝ)≤(L.absNorm:ℝ)^2 := by
  have hd:=marked_forced_label_dvd_square s A₁ A₂ D K R L F hL p.1
  refine ⟨forcedSource_label_seed s Mod R L hL.ne_zero p.1,hd,?_⟩
  simpa only [map_pow,Nat.cast_pow] using norm_le_of_dvd p.1 (L^2) (pow_ne_zero 2 hL.ne_zero) hd

/-- Every updated frozen ideal is bounded using the same actual C|L². -/
theorem selected_norm_bounds (hL:Squarefree L) (p:Idx) :
    (Ideal.absNorm ((A₁*p.2.val (Sum.inr 0))*(A₂*p.2.val (Sum.inr 1))):ℝ)≤
      (Ideal.absNorm (A₁*A₂):ℝ)*(L.absNorm:ℝ)^2 ∧
    (Ideal.absNorm (D*(p.1:Ideal O)):ℝ)≤(D.absNorm:ℝ)*(L.absNorm:ℝ)^2 ∧
    (Ideal.absNorm (R*(p.1:Ideal O)):ℝ)≤(R.absNorm:ℝ)*(L.absNorm:ℝ)^2 ∧
    (Ideal.absNorm (K*markedProduct p.2.val):ℝ)≤(K.absNorm:ℝ)*(L.absNorm:ℝ)^2 := by
  have hC:=(selected_common_bound s A₁ A₂ D K R L F hL p).2.2
  have hc0:=forcedLabel_ne_zero L (forcedSource s Mod R L) p.1
  have hparts:=allocated_parts_dvd s p.1 p.2
  have hplain:=(norm_le_of_dvd _ _ hc0 hparts.1).trans hC
  have hmarked:=(norm_le_of_dvd _ _ hc0 hparts.2).trans hC
  have hmul:(A₁*p.2.val (Sum.inr 0))*(A₂*p.2.val (Sum.inr 1))=
      (A₁*A₂)*(p.2.val (Sum.inr 0)*p.2.val (Sum.inr 1)) := by ring
  rw [hmul]
  simp only [map_mul,Nat.cast_mul]
  exact ⟨mul_le_mul_of_nonneg_left (by simpa only [map_mul,Nat.cast_mul] using hplain) (by positivity),
    mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _),mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _),
    mul_le_mul_of_nonneg_left hmarked (Nat.cast_nonneg _)⟩

/-- Parent polynomial caps are explicit and may vary with the original row.
Each updated exponent receives only the actual complete-part allowance 2 B_L. -/
theorem selected_polynomial_caps (hL:Squarefree L) (p:Idx)
    (Z B_A B_D B_R B_K B_L:ℝ) (hZ:0<Z)
    (hA:(Ideal.absNorm (A₁*A₂):ℝ)≤Z^B_A) (hD:(D.absNorm:ℝ)≤Z^B_D)
    (hR:(R.absNorm:ℝ)≤Z^B_R) (hK:(K.absNorm:ℝ)≤Z^B_K) (hNL:(L.absNorm:ℝ)≤Z^B_L) :
    (Ideal.absNorm ((A₁*p.2.val (Sum.inr 0))*(A₂*p.2.val (Sum.inr 1))):ℝ)≤Z^(B_A+2*B_L) ∧
    (Ideal.absNorm (D*(p.1:Ideal O)):ℝ)≤Z^(B_D+2*B_L) ∧
    (Ideal.absNorm (R*(p.1:Ideal O)):ℝ)≤Z^(B_R+2*B_L) ∧
    (Ideal.absNorm (K*markedProduct p.2.val):ℝ)≤Z^(B_K+2*B_L) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩:=selected_norm_bounds s A₁ A₂ D K R L F hL p
  have hpow:(L.absNorm:ℝ)^2≤Z^(2*B_L) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hNL 2).trans_eq
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  have hm (I:Ideal O) (b:ℝ) (hI:(I.absNorm:ℝ)≤Z^b) :
      (I.absNorm:ℝ)*(L.absNorm:ℝ)^2≤Z^(b+2*B_L) := by
    rw [Real.rpow_add hZ]
    exact mul_le_mul hI hpow (sq_nonneg _) (Real.rpow_nonneg hZ.le _)
  exact ⟨h₁.trans (hm _ _ hA),h₂.trans (hm _ _ hD),h₃.trans (hm _ _ hR),h₄.trans (hm _ _ hK)⟩

/-- The true shortened corners also have a lower bound from C|L². This
permits a later width budget to pay the forced seed without changing corners. -/
theorem selected_raw_lower (hL:Squarefree L) (p:Idx) (τ:Character) (t:ℝ) :
    s.X₁/(L.absNorm:ℝ)^2≤(child s p.1 R p.2 τ t).X₁ ∧
    s.X₂/(L.absNorm:ℝ)^2≤(child s p.1 R p.2 τ t).X₂ ∧
    s.Y₁/(L.absNorm:ℝ)^2≤(child s p.1 R p.2 τ t).Y₁ ∧
    s.Y₂/(L.absNorm:ℝ)^2≤(child s p.1 R p.2 τ t).Y₂ := by
  have hC:=(selected_common_bound s A₁ A₂ D K R L F hL p).2.2
  have hc0:=forcedLabel_ne_zero L (forcedSource s Mod R L) p.1
  have hparts:=(allocated_parts_dvd s p.1 p.2).1
  have h₁:((p.2.val (Sum.inr 0)).absNorm:ℝ)≤(L.absNorm:ℝ)^2 :=
    (norm_le_of_dvd _ _ hc0 ((dvd_mul_right _ _).trans hparts)).trans hC
  have h₂:((p.2.val (Sum.inr 1)).absNorm:ℝ)≤(L.absNorm:ℝ)^2 :=
    (norm_le_of_dvd _ _ hc0 ((dvd_mul_left _ _).trans hparts)).trans hC
  exact ⟨div_le_div_of_nonneg_left s.X₁_pos.le (alloc_norm_pos s p.1 p.2 _) h₁,
    div_le_div_of_nonneg_left s.X₂_pos.le (alloc_norm_pos s p.1 p.2 _) h₂,
    div_le_div_of_nonneg_left s.Y₁_pos.le (alloc_norm_pos s p.1 p.2 _) h₁,
    div_le_div_of_nonneg_left s.Y₂_pos.le (alloc_norm_pos s p.1 p.2 _) h₂⟩

/-- A precise logarithmic lower-width allowance, uniform in the selected
row and all its moving ideals: at most 2 B_L per raw corner. -/
theorem selected_log_width_lower (hL:Squarefree L) (p:Idx) (τ:Character) (t Z B_L:ℝ)
    (hZ:1<Z) (hNL:(L.absNorm:ℝ)≤Z^B_L) :
    Real.logb Z s.X₁-2*B_L≤Real.logb Z (child s p.1 R p.2 τ t).X₁ ∧
    Real.logb Z s.X₂-2*B_L≤Real.logb Z (child s p.1 R p.2 τ t).X₂ ∧
    Real.logb Z s.Y₁-2*B_L≤Real.logb Z (child s p.1 R p.2 τ t).Y₁ ∧
    Real.logb Z s.Y₂-2*B_L≤Real.logb Z (child s p.1 R p.2 τ t).Y₂ := by
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have hpow:(L.absNorm:ℝ)^2≤Z^(2*B_L) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hNL 2).trans_eq
    rw [←Real.rpow_mul_natCast hZ0.le]
    congr 1
    ring
  have hLn:(0:ℝ)<L.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL.ne_zero)
  have hl (x y:ℝ) (hx:0<x) (hxy:x/(L.absNorm:ℝ)^2≤y) :
      Real.logb Z x-2*B_L≤Real.logb Z y := by
    have h:=Real.logb_le_logb_of_le hZ (div_pos hx (Real.rpow_pos_of_pos hZ0 _))
      ((div_le_div_of_nonneg_left hx.le (pow_pos hLn 2) hpow).trans hxy)
    rwa [Real.logb_div hx.ne' (Real.rpow_pos_of_pos hZ0 _).ne',
      Real.logb_rpow hZ0 (ne_of_gt hZ)] at h
  obtain ⟨h₁,h₂,h₃,h₄⟩:=selected_raw_lower s A₁ A₂ D K R L F hL p τ t
  exact ⟨hl _ _ s.X₁_pos h₁,hl _ _ s.X₂_pos h₂,hl _ _ s.Y₁_pos h₃,hl _ _ s.Y₂_pos h₄⟩


/-- Four distinct original caps survive two common allocations followed by
forced extraction. Crossed X/Y corners are never replaced by common maxima. -/
theorem third_child_raw_caps (s₀:Input ι) (C R₀:Ideal O) (B:actualAllocations s₀.pools C)
    (τ:Character) (t:ℝ) (D₀:Ideal O)
    (E:actualAllocations (child s₀ C R₀ B τ t).pools D₀) (ψ:Character) (v:ℝ)
    (Q:Ideal O) (H:actualAllocations (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v).pools Q)
    (χ:Character) (w U₁ U₂ V₁ V₂:ℝ)
    (hX₁:s₀.X₁≤U₁) (hX₂:s₀.X₂≤U₂) (hY₁:s₀.Y₁≤V₁) (hY₂:s₀.Y₂≤V₂) :
    (child (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v) Q ((R₀*C)*D₀) H χ w).X₁≤U₁ ∧
    (child (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v) Q ((R₀*C)*D₀) H χ w).X₂≤U₂ ∧
    (child (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v) Q ((R₀*C)*D₀) H χ w).Y₁≤V₁ ∧
    (child (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v) Q ((R₀*C)*D₀) H χ w).Y₂≤V₂ := by
  obtain ⟨h₁,h₂,h₃,h₄⟩:=child_raw_caps s₀ C R₀ B τ t U₁ U₂ V₁ V₂ hX₁ hX₂ hY₁ hY₂
  obtain ⟨h₁,h₂,h₃,h₄⟩:=child_raw_caps (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v
    U₁ U₂ V₁ V₂ h₁ h₂ h₃ h₄
  exact child_raw_caps (child (child s₀ C R₀ B τ t) D₀ (R₀*C) E ψ v) Q ((R₀*C)*D₀) H χ w
    U₁ U₂ V₁ V₂ h₁ h₂ h₃ h₄

end
end QRH.Record1252270103Source.Admission.SelectedForcedGeometry
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.selected_common_bound
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.selected_norm_bounds
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.selected_polynomial_caps
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.selected_raw_lower
#print axioms QRH.Record1252270103Source.Admission.SelectedForcedGeometry.selected_log_width_lower
