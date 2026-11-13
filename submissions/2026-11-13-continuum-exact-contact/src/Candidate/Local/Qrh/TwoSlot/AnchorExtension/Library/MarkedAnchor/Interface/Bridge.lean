/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberBridge
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.FiberImproved
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField

/-!
# Interface.Bridge

From the anchor family `Contract.ImprovedMoments` to the fiber moments `ImprovedFiberMoments`
consumed by the return (`Return/Final.lean`, `dirichlet_of_improved`).

* Slot dictionary: on the identity-ray primes of a slot, the fiber's physical slot
  `canonicalPrimeAmplitude M H u V 2 D z` is the complex conjugate of the contract's
  `directSlot u (canonicalPool M H D) β D` with the canonical coefficient of
  `canonicalSlots V (33/50)` (`θ = 1`, imaginary height `-Im z`); the relative character times the
  row base is `1` on primes above the deleted modulus. Norms of products ignore the conjugation.
  `‖β‖ ≤ 1`. The contract admits overlapping pools, so no slot separation is needed
  (`canonicalPool_disjoint` is a utility).
* `fiber_reference_of_rect`: one fiber, one contract `InverseRectAt` at the fiber scale, gives
  the reference-profile fiber moment (rows `FreeRow ↦ NonzeroElement`, family/reverse via
  `norm_of_oriented_coefficients`, profile orientation via `oriented_child`).
* Finite grid: for the error `ε` a decrement `δ` and the grid `anchorLeft + kδ`; each fiber
  width `r ∈ [anchorLeft, anchorTop]` is covered by a grid point `w ∈ [r+δ, r+2δ]` whose rectangle
  `anchorRect w (g0-g1 w) δ` admits free width `r` and every slot total `≤ markCap r - ε`.
* `fiber_of_improved`: the bridge. The anchor family is required on `[anchorLeft, hi]` for some
  `hi > anchorTop` (an anchor `(R, z)` only admits free widths `≤ R - δ < R`, so a fiber of width
  exactly `anchorTop` needs an anchor beyond `anchorTop`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Interface.Bridge
noncomputable section

open scoped Classical BigOperators ComplexConjugate ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer DetectorDictionaryInverseRawInitialGates ProbeHighRowFamily
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-! ## The canonical slot coefficient and the physical slot -/

/-- The coefficient of `canonicalSlots W (33/50)` with trivial ray character `θ = 1` and imaginary
height `-Im z`. -/
def canonCoeff (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η : Character) (W : ℝ → ℂ) (D : ℝ) (z : ℂ) :
    Ideal O → ℂ := fun I =>
  idealCoeff (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH η 1) I *
    idealCoeff η I * HeckePrimeAnnular.annularWeight W D (33/50) (-z.im) I

/-- A prime above the deleted modulus does not divide the row base character. -/
theorem eta_ne_zero (data : RowData) (P : Ideal O) (hP : Prime P)
    (hN : ((deletedBase data).modulus.absNorm : ℝ) < (P.absNorm : ℝ)) :
    idealCoeff data.η P ≠ 0 := by
  have hc := ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P, hP⟩ hN
  have h1 := HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P
    hP.ne_zero hc
  have h2 : idealCoeff (deletedBase data) P =
      if (∀ Q ∈ excluded data, IsCoprime P Q) then
        idealCoeff (InverseInitialDetectorSource.baseCharacter data) P else 0 :=
    HeckeFamily.idealCoeff_excludePrimes _ _ _ P
  rw [h2] at h1
  split_ifs at h1 with hcop
  · rw [InverseInitialDetectorSource.baseCharacter_coeff] at h1
    have he : InverseInitialRawDictionary.fixedBase data.η data.m data.f P =
        idealCoeff data.η P * CanonicalRowCompletion.idealRowHom (data.m^6*data.f^4) P := rfl
    rw [he] at h1
    exact left_ne_zero_of_mul h1
  · exact absurd rfl h1

/-- On an identity-class prime where the base character does not vanish, the relative character
(`θ = 1`) times the base character is `1`. -/
theorem canon_unit (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η : Character) (P : Ideal O)
    (hcl : P ∈ RayQuotient.identityClass rayM H) (hη : idealCoeff η P ≠ 0) :
    idealCoeff (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH η 1) P *
      idealCoeff η P = 1 := by
  have hch : HeckeRayQuotient.character rayM H hH 1 = HeckeRayFamily.character rayM 1 := by
    rw [HeckeRayQuotient.character, map_one]
  have hray : idealCoeff (HeckeRayQuotient.character rayM H hH 1) P = 1 := by
    rw [hch]
    exact HeckePrimeRow.identityClass_principal_coeff rayM H hH hcl
  rw [CenteredMomentNaturalFixedRaySource.relativeCharacter_ideal, hray, one_mul,
    HeckeDetectorRelativePrime.idealCoeff_inverse, inv_mul_cancel₀ hη]

theorem conj_cpow_ofReal {x : ℝ} (hx : 0 < x) (c : ℂ) :
    conj ((x : ℂ)^c) = (x : ℂ)^(conj c) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0, ← Complex.exp_conj,
    map_mul, ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

theorem conj_neg_shift (z : ℂ) (hz : z.re = 17/50) :
    conj (-HeckeDyadic.shift (33/50) (-z.im)) = z - 1 := by
  apply Complex.ext
  · simp only [HeckeDyadic.shift, Complex.conj_re, Complex.neg_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, hz]
    norm_num
  · simp only [HeckeDyadic.shift, Complex.conj_im, Complex.neg_im, Complex.sub_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_im]
    ring

/-- **Slot dictionary.** The fiber's physical slot is the conjugate of the canonical direct slot
(real bump `V` supported in `[1,2]`, upper end `2`, real part `17/50`, width above the deleted
modulus). -/
theorem physical_eq_conj_directSlot (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (data : RowData) (V : ℝ → ℂ)
    (hVr : ∀ x, conj (V x) = V x) (hVs : ∀ x, V x ≠ 0 → x ∈ Icc (1:ℝ) 2)
    (D : ℝ) (hD : 0 < D) (hlarge : ((deletedBase data).modulus.absNorm : ℝ) < D)
    (z : ℂ) (hz : z.re = 17/50) (u : O) :
    HeckePrimeRow.canonicalPrimeAmplitude rayM H u V 2 D z =
      conj (Contract.directSlot u (Contract.canonicalPool rayM H D)
        (canonCoeff rayM H hH data.η V D z) D) := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude Contract.directSlot Contract.canonicalPool
  conv_rhs => rw [map_mul, map_inv₀, Complex.conj_ofReal, Finset.sum_filter, map_sum]
  rw [← CenteredMomentPrimeSlot.sqrt_inverse_cpow D hD]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  obtain ⟨hprime, hcl⟩ := (Finset.mem_filter.mp hP).2
  split_ifs with hx
  · have hxpos : 0 < (P.absNorm : ℝ)/D := lt_of_lt_of_le one_pos hx.1
    have hND : D ≤ (P.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hx.1
      linarith
    have hη := eta_ne_zero data P hprime (lt_of_lt_of_le hlarge hND)
    have h1 := canon_unit rayM H hH data.η P hcl hη
    have h1' : conj (idealCoeff
        (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH data.η 1) P) *
        conj (idealCoeff data.η P) = 1 := by
      rw [← map_mul, h1, map_one]
    simp only [canonCoeff, HeckePrimeAnnular.annularWeight, map_mul]
    rw [hVr, conj_cpow_ofReal hxpos, conj_neg_shift z hz]
    linear_combination (-(V ((P.absNorm : ℝ)/D) * (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1) *
      conj (CanonicalRowCompletion.idealRowHom u P))) * h1'
  · rw [map_zero]
    have hV0 : V ((P.absNorm : ℝ)/D) = 0 := by
      by_contra hne
      exact hx (hVs _ hne)
    rw [hV0, mul_zero, zero_mul]

/-- `‖β‖ ≤ 1` on the canonical pool. -/
theorem canonCoeff_norm_le (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η : Character) (V : ℝ → ℂ)
    (hVb : ∀ x, ‖V x‖ ≤ 1) (D : ℝ) (z : ℂ) (P : Ideal O)
    (hP : P ∈ Contract.canonicalPool rayM H D) :
    ‖canonCoeff rayM H hH η V D z P‖ ≤ 1 := by
  have hx : ((P.absNorm : ℝ)/D) ∈ Icc (1:ℝ) 2 := (Finset.mem_filter.mp hP).2
  have hxpos : 0 < (P.absNorm : ℝ)/D := lt_of_lt_of_le one_pos hx.1
  simp only [canonCoeff, HeckePrimeAnnular.annularWeight, norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have h1 := idealCoeff_norm_le_one
    (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH η 1) P
  have h2 := idealCoeff_norm_le_one η P
  have h3 := hVb ((P.absNorm : ℝ)/D)
  have h4 : ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift (33/50) (-z.im)).re) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hx.1
    simp only [Complex.neg_re, HeckeDyadic.shift_re]
    norm_num
  have h5 : 0 ≤ ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift (33/50) (-z.im)).re) :=
    Real.rpow_nonneg hxpos.le _
  have h12 : ‖idealCoeff
      (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH η 1) P‖ *
      ‖idealCoeff η P‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  have h34 : ‖V ((P.absNorm : ℝ)/D)‖ *
      ((P.absNorm : ℝ)/D)^((-HeckeDyadic.shift (33/50) (-z.im)).re) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h3 h4 h5 zero_le_one
  simpa only [one_mul] using
    mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) h5) zero_le_one

/-- Canonical pools at separated widths are disjoint. -/
theorem canonicalPool_disjoint (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    {D₁ D₂ : ℝ} (h1 : 0 < D₁) (h2 : 0 < D₂) (hsep : 2*D₁ < D₂ ∨ 2*D₂ < D₁) :
    Disjoint (Contract.canonicalPool rayM H D₁) (Contract.canonicalPool rayM H D₂) := by
  rw [Finset.disjoint_left]
  intro P hP hQ
  have ha := (Finset.mem_filter.mp hP).2
  have hb := (Finset.mem_filter.mp hQ).2
  have a1 := (le_div_iff₀ h1).mp ha.1
  have a2 := (div_le_iff₀ h1).mp ha.2
  have b1 := (le_div_iff₀ h2).mp hb.1
  have b2 := (div_le_iff₀ h2).mp hb.2
  rcases hsep with h | h <;> linarith

/-! ## One fiber -/

/-- **Fiber transport.** A contract `InverseRectAt` for the canonical slots of the fiber's
source bump, at the fiber scale `U` and the fiber's row data, gives the reference-profile marked
inverse moment of the fiber (the input of `fiber_inverse_height_uniform`). -/
theorem fiber_reference_of_rect {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    (hH : RayOrthogonality.globalUnits M ≤ H) {Label : Type*} {Slot : Type}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (V : ℝ → ℂ) (hVr : ∀ x, conj (V x) = V x) (hVs : ∀ x, V x ≠ 0 → x ∈ Icc (1:ℝ) 2)
    (hVb : ∀ x, ‖V x‖ ≤ 1) (W : ℝ → ℂ)
    {ρ : Contract.AnchorRect} {K : ℕ} {mesh εs : ℝ} {degree : ℕ} {C : ℝ}
    (hrect : Contract.InverseRectAt (Contract.canonicalSlotsRay V (33/50) M (Contract.SlotTwist.diag H) hH) ρ
      (orientedProfile F.reverse W) K mesh 1 1 εs U F.rowData degree C)
    (hU : 1 < U) (hK : selected.card ≤ K)
    (hprof : ∀ s ∈ selected, F.profile s = V) (hup : ∀ s ∈ selected, F.upper s = 2)
    (hext : ∀ s ∈ selected, (F.external s).re = 17/50)
    (hw0 : ∀ s ∈ selected, 0 ≤ F.widths s) (hwm : ∀ s ∈ selected, F.widths s ≤ mesh)
    (hlarge : ∀ s ∈ selected,
      ((deletedBase F.rowData).modulus.absNorm : ℝ) < U^(F.widths s))
    (hadm : ρ.Admissible F.r (∑ s ∈ selected, F.widths s) 1)
    (hv : ℝ) (hv0 : 0 ≤ hv) (hexth : ∀ s ∈ selected, |(F.external s).im| ≤ hv) (v : ℝ) :
    (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) true (InverseMoment.childLogTest W v)
      (U^F.r) 0 0 * F.physicalProduct selected u‖^2) ≤
      C*U^(1+εs)*((1+‖v‖+hv)^degree)^2 := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hD (s : Slot) : 0 < U^(F.widths s) := Real.rpow_pos_of_pos hU0 _
  let L : selected → Finset (Ideal O) := fun s => Contract.canonicalPool M H (U^(F.widths s))
  let ell : selected → ℝ := fun s => F.widths s
  let β : selected → Ideal O → ℂ := fun s =>
    canonCoeff M H hH F.rowData.η V (U^(F.widths s)) (F.external s)
  have hcls : Contract.canonicalSlotsRay V (33/50) M (Contract.SlotTwist.diag H) hH selected
      F.rowData L ell β U hv :=
    ⟨1, fun s => -(F.external s).im, fun s => by rw [abs_neg]; exact hexth s s.2,
      fun _ => ⟨rfl, rfl⟩⟩
  have hK' : Fintype.card selected ≤ K := by simpa using hK
  have hb := hrect hK' L ell β hv hv0 hcls
    (fun s => hw0 s s.2) (fun s => hwm s s.2)
    (fun s P hP => (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1)
    (fun s P hP => (Finset.mem_filter.mp hP).2)
    (fun s P hP => canonCoeff_norm_le M H hH _ V hVb _ _ P hP)
    (fun s => hlarge s s.2) 1 le_rfl le_rfl F.r
    (show ρ.Admissible F.r (∑ s : selected, F.widths s) 1 by
      rw [Finset.sum_coe_sort]; exact hadm)
    (F.rows.image DetectorDictionaryInverseMarkedPhysicalRows.actualRow)
    (by
      intro u hu
      rw [Real.rpow_one, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      exact DetectorDictionaryInverseMarkedPhysicalRows.actual_rows_norm F u hu)
    (orientedFrequency F.reverse v)
  unfold Contract.inverseMarkedSum at hb
  rw [DetectorDictionaryInverseMarkedPhysicalRows.actual_rows_sum] at hb
  have hθ : ‖orientedFrequency F.reverse v‖ = ‖v‖ := by
    unfold orientedFrequency
    split_ifs <;> simp
  rw [hθ] at hb
  refine (Finset.sum_congr rfl ?_).trans_le hb
  intro u hu
  congr 1
  have hpoly := norm_of_oriented_coefficients (F.family u F.label)
    (F.rowData.character (DetectorDictionaryInverseMarkedPhysicalRows.actualRow u)) F.reverse
    (F.row_coeff u hu) true (InverseMoment.childLogTest W v) (U^F.r) 0 0
    (Real.rpow_pos_of_pos hU0 _)
  have hf0 : orientedFrequency F.reverse 0 = 0 := by
    unfold orientedFrequency
    split_ifs <;> simp
  rw [DetectorDictionaryInverseMarkedPhysicalRows.oriented_child, hf0] at hpoly
  have hprod : F.physicalProduct selected u =
      conj (∏ s : selected, Contract.directSlot u.val (L s) (β s) (U^(ell s))) := by
    rw [DetectorDictionaryInverseMarkedPhysicalRows.physicalProduct_eq, map_prod]
    apply Finset.prod_congr rfl
    intro s _
    rw [hprof s s.2, hup s s.2]
    exact physical_eq_conj_directSlot M H hH F.rowData V hVr hVs _ (hD s) (hlarge s s.2) _
      (hext s s.2) u.val
  rw [norm_mul, norm_mul, hpoly, hprod, Complex.norm_conj]
  rfl

/-! ## The finite grid of anchors -/

/-- Number of grid steps for the decrement `δ`. -/
def gridN (δ : ℝ) : ℕ := ⌈(anchorTop - anchorLeft)/δ⌉₊ + 2

/-- Grid point `anchorLeft + kδ`. -/
def gridPt (δ : ℝ) (k : ℕ) : ℝ := anchorLeft + k*δ

theorem grid_cover {δ r : ℝ} (hδ : 0 < δ) (hr : anchorLeft ≤ r) (hr' : r ≤ anchorTop) :
    ∃ k : Fin (gridN δ + 1), r + δ ≤ gridPt δ k ∧ gridPt δ k ≤ r + 2*δ := by
  have hq0 : 0 ≤ (r - anchorLeft)/δ := div_nonneg (by linarith) hδ.le
  have hqle : (r - anchorLeft)/δ ≤ (anchorTop - anchorLeft)/δ :=
    div_le_div_of_nonneg_right (by linarith) hδ.le
  have hc1 : (r - anchorLeft)/δ ≤ (⌈(r - anchorLeft)/δ⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈(r - anchorLeft)/δ⌉₊ : ℝ) < (r - anchorLeft)/δ + 1 := Nat.ceil_lt_add_one hq0
  have hcm : ⌈(r - anchorLeft)/δ⌉₊ ≤ ⌈(anchorTop - anchorLeft)/δ⌉₊ := Nat.ceil_mono hqle
  have hqδ : (r - anchorLeft)/δ*δ = r - anchorLeft := by field_simp
  have e1 := mul_le_mul_of_nonneg_right hc1 hδ.le
  have e2 := mul_lt_mul_of_pos_right hc2 hδ
  refine ⟨⟨⌈(r - anchorLeft)/δ⌉₊ + 1, by unfold gridN; omega⟩, ?_, ?_⟩
  · simp only [gridPt]
    push_cast
    nlinarith
  · simp only [gridPt]
    push_cast
    nlinarith

theorem grid_range {δ : ℝ} (hδ : 0 < δ) (k : Fin (gridN δ + 1)) :
    anchorLeft ≤ gridPt δ k ∧ gridPt δ k ≤ anchorTop + 3*δ := by
  have hk : (k : ℕ) ≤ ⌈(anchorTop - anchorLeft)/δ⌉₊ + 2 := Nat.lt_succ_iff.mp k.2
  have hQ0 : 0 ≤ (anchorTop - anchorLeft)/δ :=
    div_nonneg (by norm_num [anchorTop, anchorLeft]) hδ.le
  have hc2 : (⌈(anchorTop - anchorLeft)/δ⌉₊ : ℝ) < (anchorTop - anchorLeft)/δ + 1 :=
    Nat.ceil_lt_add_one hQ0
  have hQδ : (anchorTop - anchorLeft)/δ*δ = anchorTop - anchorLeft := by field_simp
  have hkR : ((k : ℕ) : ℝ) ≤ (⌈(anchorTop - anchorLeft)/δ⌉₊ : ℝ) + 2 := by exact_mod_cast hk
  have hk0 : (0:ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
  have e1 := mul_le_mul_of_nonneg_right hkR hδ.le
  have e2 := mul_lt_mul_of_pos_right hc2 hδ
  have e3 := mul_nonneg hk0 hδ.le
  constructor
  · simp only [gridPt]
    linarith
  · simp only [gridPt]
    nlinarith

/-- The decrement used for the error `ε` and the top margin `hi - anchorTop`. -/
def stepδ (ε hi : ℝ) : ℝ := min (ε/4) (min ((hi - anchorTop)/4) (1/10))

/-- A grid point `w ∈ [r, r+2δ]` with `δ ≤ ε/4` keeps every slot total `≤ markCap r - ε` inside
the rectangle `anchorRect w (g0 - g1 w) δ`. -/
theorem slot_slack {ε δ r w : ℝ} (hδε : δ ≤ ε/4) (hw : w ≤ r + 2*δ) (hrw : r + δ ≤ w) :
    markCap r - ε ≤ (1-w)/2 + (lineG0 - lineG1*w) - δ := by
  unfold markCap lineG0 lineG1
  linarith

/-- Gluing two anchor families. -/
theorem improved_glue {lo mid hi g0 g1 : ℝ} (h1 : Contract.ImprovedMoments lo mid g0 g1)
    (h2 : Contract.ImprovedMoments mid hi g0 g1) : Contract.ImprovedMoments lo hi g0 g1 := by
  intro r hlo hhi
  by_cases hm : r ≤ mid
  · exact h1 r hlo hm
  · exact h2 r (le_of_lt (lt_of_not_ge hm)) hhi

/-! ## The bridge -/

/-- **Bridge source → fiber.** Anchors `(r, g0 - g1 r)` for every `r ∈ [anchorLeft, hi]`,
`hi > anchorTop`, give the improved fiber moments of the return. -/
theorem fiber_of_improved {hi : ℝ} (hhi : anchorTop < hi)
    (h : Contract.ImprovedMoments anchorLeft hi lineG0 lineG1) : ImprovedFiberMoments := by
  intro ε hε
  have hδ : 0 < stepδ ε hi :=
    lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hδε : stepδ ε hi ≤ ε/4 := min_le_left _ _
  have hδhi : stepδ ε hi ≤ (hi - anchorTop)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ10 : stepδ ε hi ≤ 1/10 := (min_le_right _ _).trans (min_le_right _ _)
  set δ := stepδ ε hi with hδdef
  let ρ : Fin (gridN δ + 1) → Contract.AnchorRect := fun k =>
    Contract.anchorRect (gridPt δ k) (lineG0 - lineG1*gridPt δ k) δ
  have hsrc (k : Fin (gridN δ + 1)) :
      Contract.UniformInverseRectSource Contract.canonicalFamily (ρ k) ∧
        Contract.OrdinaryRectSource (ρ k) :=
    h.rect (grid_range hδ k).1 (by linarith [(grid_range hδ k).2]) hδ
  have hP (k : Fin (gridN δ + 1)) : 1/2 ≤ (ρ k).Pmax := by
    show 1/2 ≤ gridPt δ k - δ
    have := (grid_range hδ k).1
    norm_num [anchorLeft] at this
    linarith
  choose meshI hmeshI hI using fun k => (hsrc k).1 ε hε
  choose meshO hmeshO hO using fun k =>
    FiberBridge.OrdinaryRectSource.affine_input (hsrc k).2 (hP k) ε hε
  let mesh : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun k => min (meshI k) (meshO k))
  have hmeshpos : 0 < mesh :=
    (Finset.lt_inf'_iff _).2 (fun k _ => lt_min (hmeshI k) (hmeshO k))
  have hmI (k : Fin (gridN δ + 1)) : mesh ≤ meshI k :=
    (Finset.inf'_le _ (Finset.mem_univ k)).trans (min_le_left _ _)
  have hmO (k : Fin (gridN δ + 1)) : mesh ≤ meshO k :=
    (Finset.inf'_le _ (Finset.mem_univ k)).trans (min_le_right _ _)
  refine ⟨mesh, hmeshpos, ?_⟩
  intro D S hDt hfine
  have hOrd (k : Fin (gridN δ + 1)) :
      QRH.Record12518109Count.WeightedAffineFineInput S (FiberBridge.countFace (ρ k)) :=
    hO k hDt (fun j => (hfine j).trans (by have := hmO k; linarith)) S
  have hsupp (b : Bool) : Function.support (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) ⊆
      Icc (1/18 : ℝ) (13/4) := by
    intro x hx
    apply DetectorDictionaryInverseClippedUniform.referenceWindow_support
    apply subset_tsupport
    intro h0
    apply hx
    cases b <;> simp [orientedProfile, h0]
  have hsmooth (b : Bool) : ContDiff ℝ ∞ (orientedProfile b
      (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) := by
    cases b
    · simpa only [orientedProfile, Bool.false_eq_true, ite_false] using
        DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤
    · simpa only [orientedProfile, ite_true] using
        HeckeInverseAmplification.conjugate_profile_smooth _
          (DetectorDictionaryInverseClippedUniform.referenceWindow.smooth ⊤)
  have hcf : Contract.canonicalFamily (Contract.canonicalSlotsRay (S.W : ℝ → ℂ) (33/50) S.modulus (Contract.SlotTwist.diag ⊤) le_top) :=
    ⟨S.W, S.W.smooth ⊤, S.complex_support, S.modulus, inferInstance, Contract.SlotTwist.diag ⊤, le_top, rfl⟩
  intro η
  let data := sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η
  -- the inverse degree depends on the row data; for one `η` only the finitely many
  -- data `data q.2` (labels) occur, so one degree `∑ q, deg q` serves all of them.
  choose deg Cl Z₀ hCl hZ₀ hb using
    fun q : (Fin (gridN δ + 1) × Bool) × Sum Bool (RayQuotient.Characters S.modulus ⊤) =>
      hI q.1.1 D.N _ hcf (orientedProfile q.1.2
        (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ)) (1/18) (13/4)
        (by norm_num) (by norm_num) (hsupp q.1.2) (hsmooth q.1.2) (data q.2)
  have hdegle (q : (Fin (gridN δ + 1) × Bool) × Sum Bool (RayQuotient.Characters S.modulus ⊤)) :
      deg q ≤ ∑ q, deg q :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  obtain ⟨Kf, Cf, hCf, hfib⟩ :=
    DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform (∑ q, deg q)
  choose Jo Co hCo hevo using fun k => hOrd k η
  have hCsum : 0 < 1 + ∑ q, Cl q := by
    have := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => (hCl q).le)
    linarith
  have hClle (q) : Cl q ≤ 1 + ∑ q, Cl q := by
    have := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => (hCl q).le)
      (Finset.mem_univ q)
    linarith
  have hCo0 : 0 ≤ ∑ k, Co k := Finset.sum_nonneg (fun k _ => (hCo k).le)
  have hCfin : 0 < Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by positivity
  have hCole (k) : Co k ≤ Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by
    have := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCo k).le)
      (Finset.mem_univ k)
    have := mul_pos hCf hCsum
    linarith
  -- the slot heights `|Im external| ≤ height` are paid by `(1+height)^(2 ∑ deg)`
  have hJole (k) : Jo k ≤ Kf + 2*(∑ q, deg q) + ∑ k, Jo k :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans
      (Nat.le_add_left _ _)
  refine ⟨Kf + 2*(∑ q, deg q) + ∑ k, Jo k, Cf*(1 + ∑ q, Cl q) + ∑ k, Co k, hCfin, ?_⟩
  have hscale : ∀ᶠ Z : ℝ in atTop, ∀ q, ∀ d : ℝ, (1/200:ℝ) ≤ d → Z₀ q ≤ Z^d :=
    Filter.eventually_all.mpr (fun q =>
      HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (Z₀ q) (by norm_num))
  filter_upwards [eventually_gt_atTop (1:ℝ), hscale,
    DetectorDictionaryInverseMarkedReference.deleted_large_eventually data D.ell
      (fun s => (D.slots_bounds s).1),
    Filter.eventually_all.mpr hevo] with Z hZ hscaleZ hlarge hord
  refine ⟨hZ, ?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal
  have hdpos : 0 < d := by linarith
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hUp : 0 < Z^d := zero_lt_one.trans hU
  have hpow1 : 1 ≤ 1 + height := by linarith
  have hZpow : 0 ≤ (Z^d)^(1+D.t) := Real.rpow_nonneg hUp.le _
  have hFw (x : Fin D.N) : (B.fiber bin label left right hne).widths x = D.ell x / d := by
    change B.widths x = _
    rw [hwidth]
  constructor
  · -- inverse marked moment
    intro h1 h2 sel hsel hw n hn s hs t ht
    obtain ⟨k, hk1, hk2⟩ := grid_cover hδ h1 h2
    have hfd : (B.fiber bin label left right hne).rowData = data label := by
      change B.data label = data label
      rw [hdata]
    have hrect : Contract.InverseRectAt (Contract.canonicalSlotsRay (S.W : ℝ → ℂ) (33/50) S.modulus (Contract.SlotTwist.diag ⊤) le_top) (ρ k)
        (orientedProfile (B.fiber bin label left right hne).reverse
          (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ))
        D.N (meshI k) 1 1 ε (Z^d) (B.fiber bin label left right hne).rowData
        (deg ((k, (B.fiber bin label left right hne).reverse), label))
        (Cl ((k, (B.fiber bin label left right hne).reverse), label)) := by
      rw [hfd]
      exact hb ((k, (B.fiber bin label left right hne).reverse), label) (Z^d)
        (hscaleZ _ d hd)
    have hadm : (ρ k).Admissible (B.fiber bin label left right hne).r
        (∑ x ∈ sel, (B.fiber bin label left right hne).widths x) 1 := by
      refine ⟨by linarith [show (0:ℝ) < anchorLeft by norm_num [anchorLeft]], ?_,
        Finset.sum_nonneg (fun x hx =>
          ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le), ?_⟩
      · show _ ≤ (gridPt δ k - δ)*1
        linarith
      · show _ ≤ ((1 - gridPt δ k)/2 + (lineG0 - lineG1*gridPt δ k) - δ)*1
        have := slot_slack hδε hk2 hk1
        rw [hDt] at hw
        linarith
    have href : ∀ v : ℝ, (∑ u ∈ (B.fiber bin label left right hne).rows,
        ‖polynomial ((B.fiber bin label left right hne).family u
          (B.fiber bin label left right hne).label) true
          (InverseMoment.childLogTest
            (DetectorDictionaryInverseClippedUniform.referenceWindow : ℝ → ℂ) v)
          ((Z^d)^(B.fiber bin label left right hne).r) 0 0 *
          (B.fiber bin label left right hne).physicalProduct sel u‖^2) ≤
        ((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q)))*
          (1+‖v‖)^(2*(∑ q, deg q)) := by
      intro v
      have hr := fiber_reference_of_rect le_top (B.fiber bin label left right hne) sel
        (S.W : ℝ → ℂ)
        (fun x => Complex.conj_eq_iff_im.mpr (S.real x))
        (fun x hx => S.complex_support hx)
        (fun x => by
          rw [S.complex_eq x, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (S.bounded x).1]
          exact (S.bounded x).2)
        _ hrect hU (by simpa using Finset.card_le_univ sel)
        (fun x _ => by
          change B.profile x = _
          rw [hprof]
          funext y
          exact (S.complex_eq y).symm)
        (fun x _ => hupper x) (fun x _ => hreal x)
        (fun x hx => ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le)
        (fun x _ => by
          rw [hFw x]
          apply (div_le_iff₀ hdpos).mpr
          have h1 := hfine x
          have h2 := hmI k
          have h3 := mul_le_mul_of_nonneg_left hd (hmeshI k).le
          linarith)
        (fun x _ => by
          rw [hfd, hFw x]
          exact hlarge.2 d hdpos label x)
        hadm height hheight (fun x _ => hexternal x) v
      rw [hDt]
      set dq := deg ((k, (B.fiber bin label left right hne).reverse), label) with hdq
      have hdq_le : dq ≤ ∑ q, deg q := hdegle _
      have hpv : (1+‖v‖)^(2*dq) ≤ (1+‖v‖)^(2*(∑ q, deg q)) :=
        pow_le_pow_right₀ (by linarith [norm_nonneg v]) (by omega)
      have hph : (1+height)^(2*dq) ≤ (1+height)^(2*(∑ q, deg q)) :=
        pow_le_pow_right₀ hpow1 (by omega)
      have hZe : 0 ≤ (Z^d)^(1+ε) := Real.rpow_nonneg hUp.le _
      refine hr.trans ?_
      have hsplit := Contract.heightFactor_split v hheight dq
      calc Cl ((k, (B.fiber bin label left right hne).reverse), label)*(Z^d)^(1+ε)*
            ((1+‖v‖+height)^dq)^2
          ≤ Cl ((k, (B.fiber bin label left right hne).reverse), label)*(Z^d)^(1+ε)*
            ((1+height)^(2*dq)*(1+‖v‖)^(2*dq)) :=
            mul_le_mul_of_nonneg_left hsplit (mul_nonneg (hCl _).le hZe)
        _ ≤ (1 + ∑ q, Cl q)*(Z^d)^(1+ε)*
            ((1+height)^(2*(∑ q, deg q))*(1+‖v‖)^(2*(∑ q, deg q))) := by
            gcongr
            exact hClle _
        _ = ((1 + ∑ q, Cl q)*(Z^d)^(1+ε)*(1+height)^(2*(∑ q, deg q)))*
            (1+‖v‖)^(2*(∑ q, deg q)) := by ring
    have hres := hfib (B.fiber bin label left right hne) sel hUp
      ((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q))) (by positivity) href
      n hn s hs height t hheight ht
    refine hres.trans ?_
    have e1 : (1+height)^(Kf + 2*(∑ q, deg q)) ≤
        (1+height)^(Kf + 2*(∑ q, deg q) + ∑ k, Jo k) :=
      pow_le_pow_right₀ hpow1 (Nat.le_add_right _ _)
    have e2 : Cf*(1 + ∑ q, Cl q) ≤ Cf*(1 + ∑ q, Cl q) + ∑ k, Co k := by linarith
    calc Cf*((1 + ∑ q, Cl q)*(Z^d)^(1+D.t)*(1+height)^(2*(∑ q, deg q)))*(1+height)^Kf =
          (Cf*(1 + ∑ q, Cl q))*(1+height)^(Kf + 2*(∑ q, deg q))*(Z^d)^(1+D.t) := by
          rw [pow_add]; ring
      _ ≤ (Cf*(1 + ∑ q, Cl q) + ∑ k, Co k)*(1+height)^(Kf + 2*(∑ q, deg q) + ∑ k, Jo k)*
          (Z^d)^(1+D.t) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul e2 e1 (by positivity) hCfin.le) hZpow
  · -- ordinary two-factor moment
    intro h1 h2 sel hsel hw j k' hjk s hs t ht
    obtain ⟨k, hk1, hk2⟩ := grid_cover hδ h1 h2
    have hA := (hord k).2 rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper
      hreal bin label left right hne height hheight hexternal
    have hm0 : (0:ℝ) ≤ (B.fiber bin label left right hne).m := by
      have : (0:ℝ) < anchorLeft := by norm_num [anchorLeft]
      linarith
    have hm1 : (B.fiber bin label left right hne).m ≤ 1/2 := by
      have : anchorTop < 1 := by norm_num [anchorTop]
      linarith
    have hsum0 : (0:ℝ) ≤ ∑ x ∈ sel, (B.fiber bin label left right hne).widths x :=
      Finset.sum_nonneg (fun x hx =>
        ((B.fiber bin label left right hne).widths_pos x (hsel hx)).le)
    have hsumS : ∑ x ∈ sel, (B.fiber bin label left right hne).widths x ≤
        (1 - gridPt δ k)/2 + (lineG0 - lineG1*gridPt δ k) - δ := by
      have := slot_slack hδε hk2 hk1
      rw [hDt] at hw
      linarith
    have hB' : 2*(B.fiber bin label left right hne).m +
        0*(∑ x ∈ sel, (B.fiber bin label left right hne).widths x) ≤ gridPt δ k - δ := by
      linarith
    have hmom := hA hm0 hm1 sel hsel hsum0 hsumS hB' j k' hjk s hs t ht
    refine hmom.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hCole k) (pow_le_pow_right₀ hpow1 (hJole k)) (by positivity) hCfin.le) hZpow

/-- The bridge with the anchor family split at `anchorTop`: the stage family on
`[anchorLeft, anchorTop]` and any family slightly above `anchorTop`. -/
theorem fiber_of_improved_split {hi : ℝ} (hhi : anchorTop < hi)
    (hstages : Contract.ImprovedMoments anchorLeft anchorTop lineG0 lineG1)
    (htop : Contract.ImprovedMoments anchorTop hi lineG0 lineG1) : ImprovedFiberMoments :=
  fiber_of_improved hhi (improved_glue hstages htop)

end
end Qrh.MarkedAnchor.Interface.Bridge

#print axioms Qrh.MarkedAnchor.Interface.Bridge.fiber_of_improved
#print axioms Qrh.MarkedAnchor.Interface.Bridge.fiber_of_improved_split
