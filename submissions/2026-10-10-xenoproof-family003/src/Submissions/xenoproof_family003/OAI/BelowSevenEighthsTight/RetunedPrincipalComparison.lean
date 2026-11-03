import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedSlotEstimates
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedSignalBounds
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceNormalization

/- Comparison of the original slots and original Hecke signal at an arbitrary
   Mellin shift. The contour is still above the actual zero supremum beta.
   This supplies a residue estimate, not a construction of the physical probe. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.PrincipalExtension
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
open OAI OAI.SevenEighths
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open PrincipalSignalComparison PrincipalMellinResidues
variable {κ ι : Type*}

structure SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(13/15 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j


theorem slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 13/15 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(13/15 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    SlotExtension.weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 13/15 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(13/15 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [slotRatio_error S T w Q A η h hs]

theorem principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 13/15 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := SlotExtension.principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (SlotExtension.principal_correction_ne_zero hQ hA hη hs)

theorem slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBounds S T w Q A η P) {a : ℝ} (ha : 13/15 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)


theorem slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (c : ℝ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H c a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) c Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def kernel (χ : Character) (H : ℂ → ℂ) (c : ℝ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) c Z ((a : ℂ)+t*I)

def kernelEnvelope (c a C Z : ℝ) : ℝ :=
  Z^(a+c) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 13/15 < s.re})
    {a Z : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H c a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (SignalExtension.quotient_holomorphic χ H hH ha hβ) c hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H c a Z t‖ ≤ kernelEnvelope c a C Z * polynomialGaussian 2 t := by
  have hq := SignalExtension.quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+c)*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 13/15 < s.re})
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H c a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope c a C Z)).mono'
    (kernel_continuous χ H c hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H c hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 13/15 < s.re})
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H c a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H c a Z S T w Q A η - signal χ H c Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a+c) * P^(-(13/15 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable χ H c hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H c a Z S T w Q A η - signal χ H c Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H c a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [slotResidue_eq_reciprocal,
      SignalExtension.contour_shift_left χ H hH hb c a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H c a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H c a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H c a Z t * _ - kernel χ H c a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(13/15 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H c a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope c a C Z * (slotErrorConstant S * P^(-(13/15 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope c a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(13/15 : ℝ))) :=
        mul_le_mul (kernel_norm_bound χ H c hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope c a C Z * (slotErrorConstant S * P^(-(13/15 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 13/15 < s.re})
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H c a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H c a Z S T w Q A η - signal χ H c Z‖ ≤
          D * Z^(a+c) * P^(-(13/15 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact slotResidue_bound_of_reciprocal_bound χ H c hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (c : ℝ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H c a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)+(c : ℂ)) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf


theorem slotResidue_active (χ : Character) (H : ℂ → ℂ) (c : ℝ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H c a Z S (activePools T w) w Q A η = slotResidue χ H c a Z S T w Q A η := by
  simp only [slotResidue, slotRatio_active]

theorem slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (13/15)*ell)
    (χ : Character) (H : ℂ → ℂ) (c : ℝ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 13/15 < s.re})
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => slotResidue χ H c a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H c Z) =O[atTop] (fun Z : ℝ => Z^(a+c-saving)) := by
  obtain ⟨D, hD, hd⟩ := exists_slotResidue_bound χ H c hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(13/15 : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(13/15 : ℝ)) = c0^(-(13/15 : ℝ))*Z^(ell*(-(13/15 : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a+c+ell*(-(13/15 : ℝ))) ≤ Z^(a+c-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖slotResidue χ H c a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H c Z‖ ≤ (D*c0^(-(13/15 : ℝ)))*Z^(a+c-saving) := by
    calc
      _ ≤ D*Z^(a+c)*(c0^(-(13/15 : ℝ))*Z^(ell*(-(13/15 : ℝ)))) := he
      _ = (D*c0^(-(13/15 : ℝ)))*Z^(a+c+ell*(-(13/15 : ℝ))) := by
        simp only [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'


theorem normalized_source_signal_bound
    (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M]
    (χ : Character) (H : ℂ → ℂ → ℂ → ℂ)
    (hH : DifferentiableOn ℂ (fun s => H s 1 (1/6)) {s : ℂ | 13/15 < s.re})
    (hb : ∀ s : ℂ, 13/15 < s.re → ‖H s 1 (1/6)-1‖ ≤ 1/2)
    (ξ ℓ : ℝ) {a C : ℝ} (ha : 13/15 < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) (Y : ℝ)
    (B : ℂ → ℂ → ℂ → ℂ) (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ) ≠ 0 ∧
    ‖sourceResidueIntegral W0 W1 M χ a (Z^ξ) Y Z H B /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ)) -
      signal χ (fun s => H s 1 (1/6)) (sourceShift ξ ℓ) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a+sourceShift ξ ℓ) * P^(-(13/15 : ℝ)) := by
  have hnorm := sourceResidueIntegral_normalized W0 W1 M χ ξ ℓ a Y Z
    (by linarith) H B S T w Q A η hc h.mass_pos hB
  refine ⟨hnorm.1, ?_⟩
  rw [hnorm.2]
  exact (slotResidue_bound_of_reciprocal_bound χ (fun s => H s 1 (1/6))
    (sourceShift ξ ℓ) hH hb ha ha2 hβ hC hR S T w Q A η h hZ).2

#print axioms slotResidue_bound_of_reciprocal_bound
#print axioms exists_slotResidue_bound
#print axioms slotResidue_isBigO
#print axioms normalized_source_signal_bound
end
end BelowSevenEighthsTight.PrincipalExtension
