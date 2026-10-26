import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Density.NaturalEndpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.LocalMoment
open HeckeFamily ProbePhysical

/-- A finite set whose fibers under `f` have at most `F` elements has at most `F` times as many elements as its
image. -/
theorem card_le_image_card_mul {α β : Type*} [DecidableEq β] (f : α → β) (s : Finset α) (F : ℝ)
    (hF : ∀ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) ≤ F) :
    (s.card : ℝ) ≤ ((s.image f).card : ℝ)*F := by
  have he := Finset.card_eq_sum_card_fiberwise (fun a (ha : a ∈ s) => Finset.mem_image_of_mem f ha)
  calc (s.card : ℝ) = ∑ b ∈ s.image f, ((s.filter (fun a => f a = b)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _b ∈ s.image f, F := Finset.sum_le_sum hF
    _ = ((s.image f).card : ℝ)*F := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The density loss `loss/(2 (Q + 1))` on rows of norm at most `Z^q`, `q ≤ Q`, costs at most `Z^(loss/2)`. -/
theorem density_loss_absorb {Z q Q loss ρ : ℝ} (hZ : 1 ≤ Z) (hQ : 0 ≤ Q) (hq : q ≤ Q) (hloss : 0 < loss) :
    (Z^q)^(ρ+loss/(2*(Q+1))) ≤ Z^(q*ρ+loss/2) := by
  have hδ : 0 < loss/(2*(Q+1)) := div_pos hloss (by positivity)
  have hbudget : q*(loss/(2*(Q+1))) ≤ loss/2 := by
    have hid : loss/(2*(Q+1))*(2*(Q+1)) = loss := div_mul_cancel₀ _ (by positivity)
    have hqδ := mul_le_mul_of_nonneg_right hq hδ.le
    nlinarith
  rw [← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

/-- Labels whose rows have norm at most `H` and, in the given orientation of the fixed dictionary family, a zero with
real part at least `a` and height at most `T`: their number is at most the density bound for the distinct rows times
a bound `F` on the labels over each row. The height degree precedes the dictionary. -/
theorem card_le_density_mul_fiber {Label : Type*} [Fintype Label] (loss : ℝ) (hloss : 0 < loss) :
    ∃ J : ℕ, ∀ base : Label → Character, ∃ C : ℝ, 0 < C ∧
      ∀ {L : Type*} (row : L → NonzeroFrequency) (reverse : Label → Bool) (a T : ℝ), 4/5 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ H : ℝ, 0 < H → ∀ (labels : Finset L) (F : ℝ),
      (∀ l ∈ labels, rawFrequencyNorm (row l) ≤ H ∧ naturalActualZeroRow base reverse a T (row l)) →
      (∀ w, ((labels.filter (fun l => row l = w)).card : ℝ) ≤ F) →
        (labels.card : ℝ) ≤ C*(1+T)^J*H^(unmarkedDensity (2*a-1)+loss)*F := by
  obtain ⟨J, hJ⟩ := fixed_natural_dictionary_raw_density (Label := Label) loss hloss
  refine ⟨J, fun base => ?_⟩
  obtain ⟨C, hC, hdensity⟩ := hJ base
  refine ⟨C, hC, ?_⟩
  intro L row reverse a T ha ha' hT H hH labels F hrows hfiber
  have hd := hdensity reverse a T ha ha' hT H hH (labels.image row) (by
    intro w hw
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
    exact hrows l hl)
  have hF : 0 ≤ F := (Nat.cast_nonneg _).trans (hfiber ⟨1, one_ne_zero⟩)
  exact (card_le_image_card_mul row labels F (fun w _ => hfiber w)).trans (mul_le_mul_of_nonneg_right hd hF)

/-- Labels with the same row `w` whose first-level rows divide `w` number at most the divisors of `w` times a bound
on the labels over each divisor. -/
theorem composite_row_fiber_card {L : Type*} (S : Finset L) (first row : L → O) (w : O) (hw : w ≠ 0) (A : ℝ)
    (hdvd : ∀ p ∈ S, row p = w → first p ∣ w)
    (hfiber : ∀ D : Ideal O,
      ((S.filter (fun p => row p = w ∧ Ideal.span {first p} = D)).card : ℝ) ≤ A) :
    ((S.filter (fun p => row p = w)).card : ℝ) ≤ (IdealMobiusDivisorSum.idealDivisors (Ideal.span {w})).card * A := by
  classical
  have hspan : Ideal.span {w} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  let over := fun D : Ideal O => S.filter (fun p => row p = w ∧ Ideal.span {first p} = D)
  have hsub : S.filter (fun p => row p = w) ⊆ (IdealMobiusDivisorSum.idealDivisors (Ideal.span {w})).biUnion over := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_biUnion]
    refine ⟨Ideal.span {first p}, ?_, ?_⟩
    · rw [IdealMobiusDivisorSum.mem_idealDivisors hspan]
      exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (hdvd p hp.1 hp.2)
    · simp only [over, Finset.mem_filter]
      exact ⟨hp.1, hp.2, trivial⟩
  calc ((S.filter (fun p => row p = w)).card : ℝ)
      ≤ (((IdealMobiusDivisorSum.idealDivisors (Ideal.span {w})).biUnion over).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ D ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {w}), ((over D).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ IdealMobiusDivisorSum.idealDivisors (Ideal.span {w}), A := Finset.sum_le_sum (fun D _ => hfiber D)
    _ = (IdealMobiusDivisorSum.idealDivisors (Ideal.span {w})).card * A := by rw [Finset.sum_const, nsmul_eq_mul]

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
