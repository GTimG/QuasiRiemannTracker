/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform separation of the actual radial Fourier weight on dyadic boxes.
The analytic Fourier-separation theorem is reused unchanged from the baseline. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.SieveBilinear

set_option autoImplicit false
namespace Candidate.FourthPower.SieveWindow
noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory OAI OAI.SevenEighths FourierBridge EisensteinSchwartzPoisson

private def window (x : ℝ) : ℂ := if |x| ≤ Real.log 2 then 1 else 0
private def signs : Fin 3 → ℝ := ![-1,-1,1]

theorem log_separation (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ u v w : ℝ, |u| ≤ Real.log 2 → |v| ≤ Real.log 2 → |w| ≤ Real.log 2 →
        paperRadialFourier W (R*Real.exp (w-u-v)) =
          ∫ t : ℝ, (logPhase t (-u)*logPhase t (-v)*logPhase t w)*b t) ∧
      Integrable (fun t : ℝ => ‖b t‖) volume ∧
      (1+R)^m*(∫ t : ℝ, ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1+R)^m*‖b t‖ ≤ C) := by
  obtain ⟨C,hC,h⟩ := paperRadialFourier_log_separation_envelope
    W (fun _ : Fin 3 => window) signs (fun _ => Real.log 2)
    (fun _ => Real.log_nonneg (by norm_num : (1:ℝ)≤2))
    (by intro j z hz; exact of_not_not (fun hn => hz (by simp [window,hn]))) m 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b,hb,hi,hm,hp⟩ := h R hR
  refine ⟨b,?_,by simpa using hi,by simpa using hm,by simpa using hp⟩
  intro u v w hu hv hw
  have he := hb ![u,v,w]
  have hs : (∑ j : Fin 3, signs j * (![u,v,w] : Fin 3 → ℝ) j) = w-u-v := by
    simp [signs, Fin.sum_univ_succ]
    ring
  rw [hs] at he
  simpa [window,signs,Fin.prod_univ_succ,hu,hv,hw,mul_assoc] using he

theorem log_bound {x : ℝ} (hx : 1 ≤ x) (hx' : x ≤ 2) : |Real.log x| ≤ Real.log 2 := by
  rw [abs_of_nonneg (Real.log_nonneg hx)]
  exact Real.log_le_log (zero_lt_one.trans_le hx) hx'

/-- The separated coefficient function depends on the box scale R but not
on the three individual entries x,y,z. This is the required uniformity. -/
theorem radial_separation (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y z : ℝ, 1 ≤ x → x ≤ 2 → 1 ≤ y → y ≤ 2 → 1 ≤ z → z ≤ 2 →
        paperRadialFourier W (R*z/(x*y)) =
          ∫ t : ℝ,
            (logPhase t (-Real.log x)*logPhase t (-Real.log y)*logPhase t (Real.log z))*b t) ∧
      Integrable (fun t : ℝ => ‖b t‖) volume ∧
      (1+R)^m*(∫ t : ℝ, ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1+R)^m*‖b t‖ ≤ C) := by
  obtain ⟨C,hC,h⟩ := log_separation W m
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b,hb,hi,hm,hp⟩ := h R hR
  refine ⟨b,?_,hi,hm,hp⟩
  intro x y z hx hx' hy hy' hz hz'
  have he := hb (Real.log x) (Real.log y) (Real.log z)
    (log_bound hx hx') (log_bound hy hy') (log_bound hz hz')
  have hf : R*Real.exp (Real.log z-Real.log x-Real.log y) = R*z/(x*y) := by
    rw [Real.exp_sub,Real.exp_sub,Real.exp_log (zero_lt_one.trans_le hz),
      Real.exp_log (zero_lt_one.trans_le hx),Real.exp_log (zero_lt_one.trans_le hy)]
    ring
  rwa [hf] at he

def separatedPhase (u v w t : ℝ) : ℂ :=
  logPhase t (-u)*logPhase t (-v)*logPhase t w

theorem separatedPhase_norm (u v w t : ℝ) : ‖separatedPhase u v w t‖ = 1 := by
  simp only [separatedPhase,norm_mul,logPhase_norm,mul_one]

theorem separatedPhase_continuous (u v w : ℝ) : Continuous (separatedPhase u v w) :=
  ((logPhase_continuous_left (-u)).mul (logPhase_continuous_left (-v))).mul
    (logPhase_continuous_left w)

theorem phase_integrable (b : 𝓢(ℝ, ℂ)) (c : ℂ) (u v w : ℝ) :
    Integrable (fun t : ℝ => c*separatedPhase u v w t*b t) volume := by
  have hm : AEStronglyMeasurable (fun t => c*separatedPhase u v w t) volume :=
    ((separatedPhase_continuous u v w).const_mul c).aestronglyMeasurable
  have hi := b.integrable.mul_bdd hm (Filter.Eventually.of_forall
    (fun t => (show ‖c*separatedPhase u v w t‖ ≤ ‖c‖ by
      simp only [norm_mul,separatedPhase_norm,mul_one,le_refl])))
  simpa only [mul_comm] using hi

/-- A complete finite-family consequence of the separation theorem.
The frequency-dependent sum is bounded before integrating; hence its
common coefficients are never replaced by separately chosen maxima. -/
theorem separated_family_bound (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {ι : Type*} [Fintype ι] (c : ι → ℂ) (u v w : ι → ℝ),
      (∀ i, |u i| ≤ Real.log 2) → (∀ i, |v i| ≤ Real.log 2) →
      (∀ i, |w i| ≤ Real.log 2) → ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, ‖∑ i, c i*separatedPhase (u i) (v i) (w i) t‖ ≤ E) →
      ‖∑ i, c i*paperRadialFourier W (R*Real.exp (w i-u i-v i))‖ ≤
        (C/(1+R)^m)*E := by
  obtain ⟨C,hC,h⟩ := log_separation W m
  refine ⟨C,hC,?_⟩
  intro R hR ι _ c u v w hu hv hw E hE hbound
  obtain ⟨b,hb,hi,hm,_hp⟩ := h R hR
  have he : (∑ i, c i*paperRadialFourier W (R*Real.exp (w i-u i-v i))) =
      ∫ t : ℝ, (∑ i, c i*separatedPhase (u i) (v i) (w i) t)*b t := by
    calc
      _ = ∑ i, ∫ t : ℝ, c i*separatedPhase (u i) (v i) (w i) t*b t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hb (u i) (v i) (w i) (hu i) (hv i) (hw i), ← integral_const_mul]
        congr 1
        ext t
        simp only [separatedPhase,mul_assoc]
      _ = ∫ t : ℝ, ∑ i, c i*separatedPhase (u i) (v i) (w i) t*b t :=
        (integral_finsetSum _ (fun i _ => phase_integrable b (c i) (u i) (v i) (w i))).symm
      _ = _ := by simp only [Finset.sum_mul]
  rw [he]
  have hbnd : ‖∫ t : ℝ, (∑ i, c i*separatedPhase (u i) (v i) (w i) t)*b t‖ ≤
      E*(∫ t : ℝ, ‖b t‖) := by
    calc
      _ ≤ ∫ t : ℝ, E*‖b t‖ := norm_integral_le_of_norm_le (hi.const_mul E)
        (Filter.Eventually.of_forall (fun t => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)))
      _ = _ := integral_const_mul _ _
  have hmass : (∫ t : ℝ, ‖b t‖) ≤ C/(1+R)^m :=
    (le_div_iff₀ (pow_pos (by linarith : 0<1+R) m)).mpr (by simpa only [mul_comm] using hm)
  exact hbnd.trans ((mul_le_mul_of_nonneg_left hmass hE).trans_eq (mul_comm _ _))

private def align (z : ℂ) : ℂ := star z/(‖z‖ : ℂ)

private theorem align_norm (z : ℂ) : ‖align z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [align,hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [align,hn]

private theorem align_mul (z : ℂ) : align z*z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [align,hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    unfold align
    rw [div_mul_eq_mul_div,← starRingEnd_apply,Complex.conj_mul']
    field_simp

/-- Grouped version, with no loss equal to the number of groups. Alignment
is chosen once from the original finite sums and is independent of t. -/
theorem separated_groups_bound (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → κ → ℂ) (u v w : ι → κ → ℝ),
      (∀ i j, |u i j| ≤ Real.log 2) → (∀ i j, |v i j| ≤ Real.log 2) →
      (∀ i j, |w i j| ≤ Real.log 2) → ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, (∑ i, ‖∑ j, c i j*separatedPhase (u i j) (v i j) (w i j) t‖) ≤ E) →
      (∑ i, ‖∑ j, c i j*paperRadialFourier W (R*Real.exp (w i j-u i j-v i j))‖) ≤
        (C/(1+R)^m)*E := by
  obtain ⟨C,hC,h⟩ := separated_family_bound W m
  refine ⟨C,hC,?_⟩
  intro R hR ι κ _ _ c u v w hu hv hw E hE hbound
  let X (i : ι) : ℂ := ∑ j, c i j*paperRadialFourier W (R*Real.exp (w i j-u i j-v i j))
  have hb := h R hR (fun q : ι × κ => align (X q.1)*c q.1 q.2)
    (fun q => u q.1 q.2) (fun q => v q.1 q.2) (fun q => w q.1 q.2)
    (fun q => hu q.1 q.2) (fun q => hv q.1 q.2) (fun q => hw q.1 q.2) E hE
  have hp : ∀ t : ℝ,
      ‖∑ q : ι × κ, (align (X q.1)*c q.1 q.2)*separatedPhase (u q.1 q.2) (v q.1 q.2) (w q.1 q.2) t‖ ≤ E := by
    intro t
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc,← Finset.mul_sum]
    apply ((norm_sum_le _ _).trans _).trans (hbound t)
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (align_norm _)
  specialize hb hp
  have he : ‖∑ q : ι × κ, (align (X q.1)*c q.1 q.2)*
      paperRadialFourier W (R*Real.exp (w q.1 q.2-u q.1 q.2-v q.1 q.2))‖ = ∑ i, ‖X i‖ := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc,← Finset.mul_sum]
    change ‖∑ i, align (X i)*X i‖ = _
    simp_rw [align_mul]
    rw [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg (X i)))]
  rw [he] at hb
  exact hb

end
end Candidate.FourthPower.SieveWindow
