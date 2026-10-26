import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLabelDisintegration
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.FirstProjectorMultiplicity
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.DepthTwoCount
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The rows of the second expansion over one child prefix: at most the squarefree divisors of the prefix's first common
ideal times the dyad box, hence at most a small power of the norm cap times the box. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment IdealMobiusDivisorSum CenteredMomentCommonRadialData

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The child prefix of a row of the second expansion: the first label of its first-stage row and the arithmetic
label of its second block. -/
def secondBlockPrefix {Label : Type*} (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (K Tsec : Label → ℝ) (Z ξ : ℝ) (first : Label → FirstSourceLabel)
    (r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ) : ChildPrefix :=
  ⟨first r.1, actualSecondArithmeticLabel (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2⟩

/-- The rows of the second expansion over one child prefix number at most the squarefree divisors of the prefix's
first common ideal times the dyad box. The first-stage label of a row is fixed by its first label and its seed, which
is a squarefree divisor of that ideal, and its block by its arithmetic label and its dyad. -/
theorem second_block_rows_per_prefix {Label : Type*} [Fintype Label]
    (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (hseed : ∀ l, Squarefree (seed l))
    (hz₁ : ∀ l, (s l).W₁ 0 = 0) (hz₂ : ∀ l, (s l).W₂ 0 = 0)
    (K Tsec : Label → ℝ) (Z ξ : ℝ) (hK : ∀ l, 0 < K l)
    (first : Label → FirstSourceLabel) (hfirst : Function.Injective (fun l => (first l, seed l)))
    (rows : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ))
    (box : Finset (Fin 4 → ℤ))
    (hbox : ∀ r ∈ rows, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 ∈ box)
    (p : ChildPrefix) (hp : p.2.1.1 ≠ ⊥) :
    ((rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)).card : ℝ) ≤
      (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ)*box.card := by
  let fiber := rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)
  let code := fun r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ =>
    (seed r.1, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2)
  have hmaps : ∀ r ∈ fiber, code r ∈ ((idealDivisors p.2.1.1).filter Squarefree) ×ˢ box := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hgates := actual_retained_block_gates (slots r.1) (s r.1) (R r.1) (seed r.1) (hseed r.1) (hz₁ r.1)
      (hz₂ r.1) (K r.1) (Tsec r.1) Z ξ (hK r.1) r.2
    have hC : p.2.1.1 = r.2.1.val.val.1 := by
      rw [← hr'.2]
      rfl
    have hdvd : seed r.1 ∣ p.2.1.1 := by
      rw [hC]
      exact hgates.1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨(mem_idealDivisors hp).mpr hdvd, hseed r.1⟩,
      hbox r hr'.1⟩
  have hinj : Set.InjOn code fiber := by
    rintro ⟨l, q⟩ hr ⟨l', q'⟩ hr' he
    have hpre := (Finset.mem_filter.mp hr).2
    have hpre' := (Finset.mem_filter.mp hr').2
    have hcode := Prod.mk.inj he
    have hsame : secondBlockPrefix slots s R seed K Tsec Z ξ first ⟨l, q⟩ =
        secondBlockPrefix slots s R seed K Tsec Z ξ first ⟨l', q'⟩ := hpre.trans hpre'.symm
    have hfst : first l = first l' := congrArg Sigma.fst hsame
    have hl : l = l' := hfirst (Prod.ext hfst hcode.1)
    subst hl
    have hlabel : actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q =
        actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q' :=
      eq_of_heq (Sigma.mk.inj hsame).2
    have hq := actual_second_label_dyad_injective (s l) (R l) (seed l) (K l) (Tsec l) Z ξ
      (Prod.ext hlabel hcode.2)
    rw [hq]
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  rw [Finset.card_product] at hcard
  exact_mod_cast hcard

/-- The rows of the second expansion over one child prefix whose first common ideal has norm at most `Z^B`: at most
`Kc Z^ε` times the dyad box. The constant precedes `Z`, the labels, the rows and the prefix. -/
theorem second_block_rows_per_prefix_small (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ {Label : Type*} [Fintype Label]
      (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
      (R seed : Label → Ideal O) (_hseed : ∀ l, Squarefree (seed l))
      (_hz₁ : ∀ l, (s l).W₁ 0 = 0) (_hz₂ : ∀ l, (s l).W₂ 0 = 0)
      (K Tsec : Label → ℝ) (ξ : ℝ) (_hK : ∀ l, 0 < K l) (first : Label → FirstSourceLabel),
      Function.Injective (fun l => (first l, seed l)) →
      ∀ (rows : Finset ((l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ))
        (box : Finset (Fin 4 → ℤ)),
      (∀ r ∈ rows, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2 ∈ box) →
      ∀ p : ChildPrefix, p.2.1.1 ≠ ⊥ → (p.2.1.1.absNorm : ℝ) ≤ Z^B →
      ((rows.filter (fun r => secondBlockPrefix slots s R seed K Tsec Z ξ first r = p)).card : ℝ) ≤
        Kc*Z^ε*box.card := by
  let δ := ε/(B+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Kc, hKc, hbound⟩ := SquarefreeDivisorBound.squarefree_divisor_small_power δ hδ
  refine ⟨Kc, hKc, ?_⟩
  intro Z hZ Label _ slots s R seed hseed hz₁ hz₂ K Tsec ξ hK first hfirst rows box hbox p hp hnorm
  have hrows := second_block_rows_per_prefix slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK first hfirst rows box
    hbox p hp
  have he : B*δ ≤ ε := by
    have hid : δ*(B+1) = ε := by dsimp only [δ]; field_simp
    nlinarith
  have hdiv : (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ) ≤ Kc*Z^ε :=
    calc (((idealDivisors p.2.1.1).filter Squarefree).card : ℝ)
        ≤ Kc*(p.2.1.1.absNorm : ℝ)^δ := hbound _ hp
      _ ≤ Kc*(Z^B)^δ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hKc.le
      _ = Kc*Z^(B*δ) := by rw [← Real.rpow_mul (zero_le_one.trans hZ)]
      _ ≤ Kc*Z^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) hKc.le
  exact hrows.trans (mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg _))

/-- The elements over one ideal of their prefix multipliers number at most the prefixes over that ideal times a bound
on the elements of one prefix. -/
theorem rows_over_ideal_card {ρ π : Type*} (rows : Finset ρ) (pre : ρ → π) (v : π → O) (F : ℝ) (hF0 : 0 ≤ F)
    (hF : ∀ p ∈ rows.image pre, ((rows.filter (fun r => pre r = p)).card : ℝ) ≤ F) (D : Ideal O) :
    ((rows.filter (fun r => Ideal.span {v (pre r)} = D)).card : ℝ) ≤
      (((rows.image pre).filter (fun p => Ideal.span {v p} = D)).card : ℝ)*F := by
  let fibreRows := rows.filter (fun r => Ideal.span {v (pre r)} = D)
  have hfib : ∀ p ∈ fibreRows.image pre, ((fibreRows.filter (fun r => pre r = p)).card : ℝ) ≤ F := by
    intro p hp
    have hsub : fibreRows.filter (fun r => pre r = p) ⊆ rows.filter (fun r => pre r = p) := by
      intro r hr
      rw [Finset.mem_filter] at hr ⊢
      exact ⟨(Finset.mem_filter.mp hr.1).1, hr.2⟩
    have hp' : p ∈ rows.image pre := by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image_of_mem pre (Finset.mem_filter.mp hr).1
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hF p hp')
  have himage : fibreRows.image pre ⊆ (rows.image pre).filter (fun p => Ideal.span {v p} = D) := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    have hr' := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem pre hr'.1, hr'.2⟩
  calc ((rows.filter (fun r => Ideal.span {v (pre r)} = D)).card : ℝ)
      ≤ ((fibreRows.image pre).card : ℝ)*F := LocalMoment.card_le_image_card_mul pre fibreRows F hfib
    _ ≤ (((rows.image pre).filter (fun p => Ideal.span {v p} = D)).card : ℝ)*F :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card himage)) hF0

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
