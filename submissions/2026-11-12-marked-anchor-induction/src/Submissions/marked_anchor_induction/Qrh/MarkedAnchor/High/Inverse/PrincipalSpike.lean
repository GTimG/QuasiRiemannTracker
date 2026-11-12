/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.PrincipalShift
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.Pointwise

/-!
# High.Inverse.PrincipalSpike — the inverse spike of every Hecke character

The inverse dyadic polynomial `∑ μ(I)χ(I)Φ(NI/D)NI^{ifreq}` of ANY Hecke character (principal ones
included, finitely many deleted primes allowed) satisfies
`‖polynomial χ true Φ (U^r) 0 freq‖² ≤ C U^((2β-1)r + ε)`, `β = HeckeZeroSupremum.beta`, uniformly in
`χ` with modulus `≤ U` and `|freq| ≤ U^A`.

Proof: Mellin inversion and a contour shift to `Re s = β + 8e` (`PrincipalShift`): the integrand
`series χ true = reciprocal χ` is holomorphic on `Re s > β` (for principal `χ`, `1/L` has no pole
at `s = 1`), and there `‖reciprocal χ s‖ ≤ D (presentationComplexity χ (Im s))^κ`
(baseline `HeckeReciprocalGrowth.reciprocal_subpower`, uniform in `χ`). The rectangle has height
`U`; its horizontal sides and the far tail are paid by `(1+U)^n`.

* `inverseSpike_scale` — the statement at scale `U`;
* `inverseSpike_beta` — the same at scale `Z^d` (all characters);
* `PrincipalInverseSpike` / `principalInverseSpike` — the statement for principal characters;
* `principalInverseSpike_childLogTest` — the form used by the inverse HIGH leaf.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse.Principal
noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic

/-- `series χ true` is the reciprocal `1/L`. -/
theorem series_true (χ : Character) :
    HeckeDyadic.series χ true = HeckeReciprocal.reciprocal χ := by
  funext s
  simp [HeckeDyadic.series]

/-- Height cost: for `|t| ≤ U + U^A` the presentation complexity is `≤ 50 U^(2A+4)`. -/
theorem complexity_le (χ : Character) (U A t : ℝ) (hU : 1 ≤ U) (hA : 0 ≤ A)
    (hQ : (χ.modulus.absNorm : ℝ) ≤ U) (ht : |t| ≤ U + U^A) :
    HeckeReciprocalGrowth.presentationComplexity χ t ≤ 50 * U^(2*A+4) := by
  have hU0 : 0 < U := by linarith
  have hP1 : U^A ≤ U^(A+1) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hP2 : U ≤ U^(A+1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hU (by linarith : (1:ℝ) ≤ A+1)
    rwa [Real.rpow_one] at h
  have hP3 : 1 ≤ U^(A+1) := Real.one_le_rpow hU (by linarith)
  have h3 : 3 + |t| ≤ 5 * U^(A+1) := by linarith
  have hc := presentationComplexity_le_of_modulus_le χ U t hQ
  have hsq : (3+|t|)^2 ≤ (5*U^(A+1))^2 := pow_le_pow_left₀ (by positivity) h3 2
  have hid : U^2 * (U^(A+1))^2 = U^(2*A+4) := by
    rw [← Real.rpow_natCast U 2, ← Real.rpow_natCast (U^(A+1)) 2, ← Real.rpow_mul hU0.le,
      ← Real.rpow_add hU0]
    congr 1
    push_cast
    ring
  calc _ ≤ 2*U^2*(3+|t|)^2 := hc
    _ ≤ 2*U^2*(5*U^(A+1))^2 := by gcongr
    _ = 50 * (U^2 * (U^(A+1))^2) := by ring
    _ = _ := by rw [hid]

/-- The four contour pieces collapse to three. -/
theorem three_pieces (a1 a2 a3 l : ℝ) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (hl : |2-l| ≤ 2) :
    (1/(2*Real.pi))*(a1*Real.pi + 2*a2*|2-l| + a3*Real.pi) ≤ a1 + (a2 + a3) := by
  have hπ := Real.pi_gt_three
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg h1 Real.pi_pos.le, mul_nonneg h3 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left hl h2, mul_nonneg h2 (by linarith : (0:ℝ) ≤ Real.pi - 2)]

/-- The central segment at `Re s = β + 8e`. -/
theorem central_piece (U r R β e κ A c k : ℝ) (hU : 1 ≤ U) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (_hr : 0 ≤ r) (hrR : r ≤ R) (he : 0 ≤ e) :
    c * (U^r)^(β + 8*e - 1/2) * (k * U^(κ*(2*A+4))) ≤
      (c*k) * U^((β-1/2)*r + (8*e*R + κ*(2*A+4))) := by
  have hU0 : 0 < U := by linarith
  have hexp : r*(β + 8*e - 1/2) + κ*(2*A+4) ≤ (β-1/2)*r + (8*e*R + κ*(2*A+4)) := by
    have h1 : 8*e*r ≤ 8*e*R := mul_le_mul_of_nonneg_left hrR (by positivity)
    have h2 : r*(β + 8*e - 1/2) = (β-1/2)*r + 8*e*r := by ring
    linarith
  calc c * (U^r)^(β + 8*e - 1/2) * (k * U^(κ*(2*A+4)))
      = (c*k) * ((U^r)^(β + 8*e - 1/2) * U^(κ*(2*A+4))) := by ring
    _ = (c*k) * U^(r*(β + 8*e - 1/2) + κ*(2*A+4)) := by
        rw [← Real.rpow_mul hU0.le, ← Real.rpow_add hU0]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hexp)
        (by positivity)

/-- The horizontal joins and the far tail, paid by `(1+U)^n`. -/
theorem error_piece (U r R A κ c k B : ℝ) (n : ℕ) (hU : 1 ≤ U) (hc : 0 ≤ c) (hk : 0 ≤ k)
    (hB : 0 ≤ B) (_hr : 0 ≤ r) (hrR : r ≤ R) (hA : 0 ≤ A) (_hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hn : 3/2*R + (2*A+4) ≤ n) :
    c * (U^r)^(2-1/2:ℝ) * (k * U^(κ*(2*A+4))) / (1+U)^n +
      c * (U^r)^(2-1/2:ℝ) * B / (1+U)^n ≤ c * (k + B) := by
  have hU0 : 0 < U := by linarith
  have hK : U^(κ*(2*A+4)) ≤ U^(2*A+4) :=
    Real.rpow_le_rpow_of_exponent_le hU (mul_le_of_le_one_left (by linarith) hκ1)
  have hU24 : 1 ≤ U^(2*A+4) := Real.one_le_rpow hU (by linarith)
  have hKB : k * U^(κ*(2*A+4)) + B ≤ (k + B) * U^(2*A+4) := by
    have h1 := mul_le_mul_of_nonneg_left hK hk
    have h2 := le_mul_of_one_le_right hB hU24
    rw [add_mul]
    linarith
  have hD32 : (U^r)^(2-1/2:ℝ) ≤ U^(3/2*R) := by
    rw [← Real.rpow_mul hU0.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hceil : U^(3/2*R + (2*A+4)) ≤ U^n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hU hn
  have hUn : U^n ≤ (1+U)^n := pow_le_pow_left₀ hU0.le (by linarith) n
  have hpos : 0 < (1+U)^n := by positivity
  rw [← add_div, div_le_iff₀ hpos]
  calc c * (U^r)^(2-1/2:ℝ) * (k * U^(κ*(2*A+4))) + c * (U^r)^(2-1/2:ℝ) * B
      = c * (U^r)^(2-1/2:ℝ) * (k * U^(κ*(2*A+4)) + B) := by ring
    _ ≤ c * U^(3/2*R) * ((k + B) * U^(2*A+4)) := by gcongr
    _ = c * (k+B) * (U^(3/2*R) * U^(2*A+4)) := by ring
    _ = c * (k+B) * U^(3/2*R + (2*A+4)) := by rw [← Real.rpow_add hU0]
    _ ≤ c * (k+B) * (1+U)^n := mul_le_mul_of_nonneg_left (hceil.trans hUn) (by positivity)

/-- **The inverse spike at the zero supremum, scale `U`** (every character). -/
theorem inverseSpike_scale (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao)
    (hΦs : Function.support Φ ⊆ Icc ao bo) (hΦ : ContDiff ℝ ∞ Φ)
    (R A ε : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 1 ≤ U → ∀ (χ : Character),
      (χ.modulus.absNorm : ℝ) ≤ U → ∀ (r freq : ℝ), 0 ≤ r → r ≤ R → |freq| ≤ U^A →
      ‖HeckeDyadic.polynomial χ true Φ (U^r) 0 freq‖^2 ≤
        C * U^((2*HeckeZeroSupremum.beta-1)*r + ε) := by
  have hβ0 : 1/2 ≤ HeckeZeroSupremum.beta := HeckeZeroSupremum.half_le_beta
  have hβ1 : HeckeZeroSupremum.beta ≤ 1 := HeckeZeroSupremum.beta_le_one
  set β := HeckeZeroSupremum.beta with hβdef
  set e : ℝ := min (1/2000) (ε/(32*(R+1))) with hedef
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he' : e < 1/1000 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have heR : 8*e*R ≤ ε/4 := by
    have h1 : e ≤ ε/(32*(R+1)) := min_le_right _ _
    have h2 : e*(32*(R+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp h1
    have h3 : e*(32*(R+1)) = 32*(e*R) + 32*e := by ring
    have h4 : 8*e*R = 8*(e*R) := by ring
    linarith
  set κ : ℝ := min 1 (ε/(8*(2*A+4))) with hκdef
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκA : κ*(2*A+4) ≤ ε/8 := by
    have h1 : κ ≤ ε/(8*(2*A+4)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity : (0:ℝ) < 8*(2*A+4))).mp h1
    have h3 : κ*(8*(2*A+4)) = 8*(κ*(2*A+4)) := by ring
    linarith
  obtain ⟨Dsub, hDsub, hsub⟩ := HeckeReciprocalGrowth.reciprocal_subpower e κ he he' hκ
  let pb : ℕ → ℝ := fun k =>
    Classical.choose (CubicReflectionKernel.compact_source_mellin_strip_decay Φ ao bo hao hΦs hΦ
      0 2 k)
  have hpb : ∀ k, 0 < pb k ∧ ∀ σ ∈ Icc (0 : ℝ) 2, ∀ t : ℝ,
      (1 + |t|) ^ k * ‖mellin Φ ((σ : ℂ) + t * Complex.I)‖ ≤ pb k := fun k =>
    Classical.choose_spec (CubicReflectionKernel.compact_source_mellin_strip_decay Φ ao bo hao hΦs
      hΦ 0 2 k)
  set n : ℕ := ⌈3/2*R + (2*A+4)⌉₊ with hndef
  have hB2 : 0 ≤ HeckeReciprocalBound.bound 2 := tsum_nonneg (fun _ => norm_nonneg _)
  set M := pb 2 * (Dsub*50) with hMdef
  set E := pb (n+2) * (Dsub*50 + HeckeReciprocalBound.bound 2) with hEdef
  have hM : 0 ≤ M := by have := (hpb 2).1; positivity
  have hE : 0 ≤ E := by have := (hpb (n+2)).1; positivity
  refine ⟨(M+E)^2 + 1, by positivity, ?_⟩
  intro U hU χ hQ r freq hr hrR hfreq
  have hU0 : 0 < U := by linarith
  set l : ℝ := β + 8*e with hldef
  have hl0 : 0 ≤ l := by linarith
  have hl2 : l ≤ 2 := by linarith
  set K : ℝ := Dsub * 50 * U^(κ*(2*A+4)) with hKdef
  have hK : 0 ≤ K := by positivity
  have hDr : 1 ≤ U^r := Real.one_le_rpow hU hr
  -- the rectangle `[l, 2] × [-U, U]`, shifted by `-freq i`
  have hrect : ∀ s ∈ (uIcc l 2 ×ℂ uIcc (-U) U),
      l ≤ (s + HeckeDyadic.shift 0 freq).re ∧ |(s + HeckeDyadic.shift 0 freq).im| ≤ U + U^A := by
    intro s hs
    have hs' : s.re ∈ uIcc l 2 ∧ s.im ∈ uIcc (-U) U := hs
    rw [uIcc_of_le hl2, uIcc_of_le (by linarith : -U ≤ U)] at hs'
    have hre : (s + HeckeDyadic.shift 0 freq).re = s.re := by simp [HeckeDyadic.shift]
    have him : (s + HeckeDyadic.shift 0 freq).im = s.im - freq := by
      simp [HeckeDyadic.shift]
      ring
    refine ⟨by rw [hre]; exact hs'.1.1, ?_⟩
    rw [him]
    have h1 := abs_sub s.im freq
    have h2 : |s.im| ≤ U := abs_le.mpr ⟨hs'.2.1, hs'.2.2⟩
    linarith
  have hseries : ∀ s ∈ (uIcc l 2 ×ℂ uIcc (-U) U),
      ‖HeckeDyadic.series χ true (s + HeckeDyadic.shift 0 freq)‖ ≤ K := by
    intro s hs
    obtain ⟨hre, him⟩ := hrect s hs
    rw [series_true]
    refine (hsub χ _ hre).trans ?_
    have hc := complexity_le χ U A _ hU hA hQ him
    have hc0 : 0 ≤ HeckeReciprocalGrowth.presentationComplexity χ
        (s + HeckeDyadic.shift 0 freq).im := by
      unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity
      positivity
    have h50 : (50:ℝ)^κ ≤ 50 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 50) hκ1
    calc Dsub * (HeckeReciprocalGrowth.presentationComplexity χ
          (s + HeckeDyadic.shift 0 freq).im)^κ
        ≤ Dsub * (50 * U^(2*A+4))^κ := by gcongr
      _ = Dsub * ((50:ℝ)^κ * U^(κ*(2*A+4))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hU0.le,
            mul_comm (2*A+4) κ]
      _ ≤ Dsub * (50 * U^(κ*(2*A+4))) := by gcongr
      _ = K := by rw [hKdef]; ring
  have hdiff : ∀ s ∈ (uIcc l 2 ×ℂ uIcc (-U) U),
      DifferentiableAt ℂ (HeckeDyadic.series χ true) (s + HeckeDyadic.shift 0 freq) := by
    intro s hs
    rw [series_true]
    exact HeckeReciprocal.reciprocal_differentiableAt χ (by linarith [(hrect s hs).1])
  have hb := polynomial_bound_of_rectangle_of_diff χ true Φ ao bo hao hΦs hΦ (U^r) 0 freq l 2 U
    (pb 2) (pb (n+2)) K n hDr hl2 (by norm_num) hU0.le (hpb 2).1.le (hpb (n+2)).1.le hK
    (fun t => (hpb 2).2 l ⟨hl0, hl2⟩ t)
    (fun x hx t => (hpb (n+2)).2 x ⟨hl0.trans hx.1, hx.2⟩ t) hdiff hseries
  have hpos : 0 < (1+U)^n := by positivity
  have ha1 : 0 ≤ pb 2 * (U^r)^(l-1/2) * K := by have := (hpb 2).1; positivity
  have ha2 : 0 ≤ pb (n+2) * (U^r)^(2-1/2:ℝ) * K / (1+U)^n := by
    have := (hpb (n+2)).1; positivity
  have ha3 : 0 ≤ pb (n+2) * (U^r)^(2-1/2:ℝ) * HeckeReciprocalBound.bound 2 / (1+U)^n := by
    have := (hpb (n+2)).1; positivity
  have habs : |2-l| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h3 := three_pieces _ _ _ l ha1 ha2 ha3 habs
  have hcentral := central_piece U r R β e κ A (pb 2) (Dsub*50) hU (hpb 2).1.le
    (by positivity) hr hrR he.le
  have herr := error_piece U r R A κ (pb (n+2)) (Dsub*50) (HeckeReciprocalBound.bound 2) n hU
    (hpb (n+2)).1.le (by positivity) hB2 hr hrR hA hκ.le hκ1 (Nat.le_ceil _)
  have hp : 0 ≤ (β - 1/2)*r := mul_nonneg (by linarith) hr
  have hUp : 1 ≤ U^((β - 1/2)*r) := Real.one_le_rpow hU hp
  have hsum : ‖HeckeDyadic.polynomial χ true Φ (U^r) 0 freq‖ ≤
      M * U^((β-1/2)*r + (8*e*R + κ*(2*A+4))) + E * U^((β - 1/2)*r) := by
    have hEle : E ≤ E * U^((β - 1/2)*r) := le_mul_of_one_le_right hE hUp
    have hb' := hb.trans (le_of_eq_of_le (by simp only [add_zero]) h3)
    have hc' : pb 2 * (U^r)^(l-1/2) * K ≤ M * U^((β-1/2)*r + (8*e*R + κ*(2*A+4))) := hcentral
    have he' : pb (n+2) * (U^r)^(2-1/2:ℝ) * K / (1+U)^n +
        pb (n+2) * (U^r)^(2-1/2:ℝ) * HeckeReciprocalBound.bound 2 / (1+U)^n ≤ E := herr
    linarith
  have hb2 : 2*(8*e*R + κ*(2*A+4)) ≤ ε := by linarith
  have hfin := squared_bound_of_central_and_error _ U M E ((β - 1/2)*r)
    (8*e*R + κ*(2*A+4)) ε hU hM hE hε.le hb2 hsum
  refine hfin.trans ?_
  have hexp : 2*((β - 1/2)*r) + ε = (2*β-1)*r + ε := by ring
  rw [hexp]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hU0.le _)


/-- **The inverse spike at the zero supremum, scale `Z^d`** (every character). -/
theorem inverseSpike_beta (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao)
    (hΦs : Function.support Φ ⊆ Icc ao bo) (hΦ : ContDiff ℝ ∞ Φ)
    (R d A ε : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (χ : Character),
      (χ.modulus.absNorm : ℝ) ≤ Z^d → ∀ (r freq : ℝ), 0 ≤ r → r ≤ R → |freq| ≤ Z^A →
      ‖HeckeDyadic.polynomial χ true Φ ((Z^d)^r) 0 freq‖^2 ≤
        C * (Z^d)^((2*HeckeZeroSupremum.beta-1)*r + ε) := by
  obtain ⟨C, hC, h⟩ := inverseSpike_scale Φ ao bo hao hΦs hΦ R (A/d) ε hR
    (div_nonneg hA hd.le) hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ χ hQ r freq hr hrR hfreq
  apply h (Z^d) (Real.one_le_rpow hZ hd.le) χ hQ r freq hr hrR
  rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ hd.ne']
  exact hfreq

/-- **Principal inverse spike**: the inverse spike of a principal character at the zero
supremum `β`. -/
def PrincipalInverseSpike : Prop :=
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → Function.support Φ ⊆ Icc ao bo → ContDiff ℝ ∞ Φ →
  ∀ (R d A ε : ℝ), 0 ≤ R → 0 < d → 0 ≤ A → 0 < ε →
  ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (χ : Character), χ.residue = 1 →
    (χ.modulus.absNorm : ℝ) ≤ Z^d → ∀ (r freq : ℝ), 0 ≤ r → r ≤ R → |freq| ≤ Z^A →
    ‖HeckeDyadic.polynomial χ true Φ ((Z^d)^r) 0 freq‖^2 ≤
      C * (Z^d)^((2*HeckeZeroSupremum.beta-1)*r + ε)

theorem principalInverseSpike : PrincipalInverseSpike := by
  intro Φ ao bo hao hΦs hΦ R d A ε hR hd hA hε
  obtain ⟨C, hC, h⟩ := inverseSpike_beta Φ ao bo hao hΦs hΦ R d A ε hR hd hA hε
  exact ⟨C, hC, fun Z hZ χ _ hQ => h Z hZ χ hQ⟩

/-- The principal spike bound for the actual inverse factor of a row, `childLogTest Φ θ` at frequency `0`. -/
theorem principalInverseSpike_childLogTest (Φ : ℝ → ℂ) (ao bo : ℝ) (hao : 0 < ao)
    (hΦs : Function.support Φ ⊆ Icc ao bo) (hΦ : ContDiff ℝ ∞ Φ)
    (R d A ε : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z → ∀ (χ : Character), χ.residue = 1 →
      (χ.modulus.absNorm : ℝ) ≤ Z^d → ∀ (r θ : ℝ), 0 ≤ r → r ≤ R →
      |2*Real.pi*θ| ≤ Z^A →
      ‖HeckeDyadic.polynomial χ true (InverseMoment.childLogTest Φ θ) ((Z^d)^r) 0 0‖^2 ≤
        C * (Z^d)^((2*HeckeZeroSupremum.beta-1)*r + ε) := by
  obtain ⟨C, hC, h⟩ := principalInverseSpike Φ ao bo hao hΦs hΦ R d A ε hR hd hA hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ χ hχ hQ r θ hr hrR hθ
  have hD : 0 < (Z^d)^r :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by linarith) _) _
  rw [Qrh.MarkedAnchor.High.Inverse.polynomial_childLogTest _ _ _ _ _ hD]
  exact h Z hZ χ hχ hQ r (2*Real.pi*θ) hr hrR hθ

end
end Qrh.MarkedAnchor.High.Inverse.Principal

#print axioms Qrh.MarkedAnchor.High.Inverse.Principal.inverseSpike_beta
#print axioms Qrh.MarkedAnchor.High.Inverse.Principal.principalInverseSpike
#print axioms Qrh.MarkedAnchor.High.Inverse.Principal.principalInverseSpike_childLogTest
