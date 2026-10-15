/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B001
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B002
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B005
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness

/- BEGIN ORIGINAL MODULE Analytic.SignedReconstruction ; sha256 b77636ebfd23847cabd3bdec67826dcc008cbb0144351473d1d46df24e244df8 -/
section



/-!
Whole first-column reconstruction from the actual signed prime identities.
Reduction modulo six retains the canceled prime as a coprimality mask.
The product of reciprocity phases has fixed period four, independently of
the number or size of the common primes. This module proves coefficient
identities; it does not assume or assert the improved moment estimate.
-/

set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Local44.Analytic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentFirstColumns
open LocalMomentSignedRows ActualEisensteinCubic

local notation "O" => ActualEisensteinCubic.O

theorem row_argument_product {ι : Type*} (s : Finset ι) (p : ι → O)
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (∏ i ∈ s, p i) I = ∏ i ∈ s, idealRowHom (p i) I := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using idealRowHom_one_supported I hI
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, idealRowHom_argument_mul, ih]

/-- A positive exponent at most six is reduced without erasing its zero. -/
theorem row_power_reduce_six (p : O) (I : Ideal O) (hI : Supported I)
    (k : ℕ) (hk : 0 < k) (hk6 : k ≤ 6) :
    idealRowHom (p ^ k) I = idealRowHom (p ^ (k % 6)) I *
      (if k = 6 then if IsCoprime I (Ideal.span {p}) then (1 : ℂ) else 0 else 1) := by
  by_cases h : k = 6
  · subst k
    simp only [Nat.mod_self, pow_zero, idealRowHom_one_supported I hI,
      one_mul]
    exact idealRowHom_sixth_mask p I hI
  · rw [ite_eq_right h, mul_one, Nat.mod_eq_of_lt (by omega)]

theorem left_local_reduced (p n : O) (t : ℕ)
    (ht : 0 < t) (ht6 : t < 6)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda ^ 2 ∣ p - 1) (hnp : goodLambda ^ 2 ∣ n - 1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p}) ^ t =
      sexticReciprocityPhase p n ^ t *
        idealRowHom (p ^ ((1 + t) % 6)) (Ideal.span {n}) *
        (if t = 5 then if IsCoprime n p then (1 : ℂ) else 0 else 1) := by
  rw [left_local p n t hp hn hpp hnp,
    row_power_reduce_six p (Ideal.span {n}) hn (1+t) (by omega) (by omega),
    Ideal.isCoprime_span_singleton_iff]
  have he : 1 + t = 6 ↔ t = 5 := by omega
  simp only [he]
  ring

theorem right_local_reduced (p n : O) [(Ideal.span {p}).IsMaximal] (t : ℕ)
    (ht : 0 < t) (ht6 : t < 6)
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda ^ 2 ∣ p - 1) (hnp : goodLambda ^ 2 ∣ n - 1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p}) ^ t) =
      sexticReciprocityPhase p n ^ (6-t) *
        idealRowHom (p ^ ((7-t) % 6)) (Ideal.span {n}) *
        (if t = 1 then if IsCoprime n p then (1 : ℂ) else 0 else 1) := by
  rw [right_local p n t ht ht6 hg hc hp hn hpp hnp,
    row_power_reduce_six p (Ideal.span {n}) hn (7-t) (by omega) (by omega),
    Ideal.isCoprime_span_singleton_iff]
  have he : 7-t = 6 ↔ t = 1 := by omega
  simp only [he]
  ring

/-- Complete left first-column identity, including a retained generator unit.
The row after reconstruction has reduced prime exponents between zero and five.
-/
theorem left_column_reconstruction {ι : Type*} [Fintype ι]
    (p : ι → O) (t : ι → ℕ) (e u n : O)
    (ht : ∀ i, 0 < t i) (ht6 : ∀ i, t i < 6)
    (hp : ∀ i, Supported (Ideal.span {p i})) (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i, goodLambda ^ 2 ∣ p i - 1) (hnp : goodLambda ^ 2 ∣ n - 1) :
    leftCoefficient e (u * ∏ i, p i)
      (fun a => ∏ i, idealRowHom a (Ideal.span {p i}) ^ t i) n =
      idealRowHom (e * u * ∏ i, p i ^ ((1 + t i) % 6)) (Ideal.span {n}) *
        (∏ i, sexticReciprocityPhase (p i) n ^ t i) *
        (∏ i, if t i = 5 then if IsCoprime n (p i) then (1 : ℂ) else 0 else 1) := by
  have hl : (∏ i, idealRowHom (p i) (Ideal.span {n}) *
      idealRowHom n (Ideal.span {p i}) ^ t i) =
      ∏ i, sexticReciprocityPhase (p i) n ^ t i *
        idealRowHom (p i ^ ((1 + t i) % 6)) (Ideal.span {n}) *
        (if t i = 5 then if IsCoprime n (p i) then (1 : ℂ) else 0 else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    exact left_local_reduced (p i) n (t i) (ht i) (ht6 i) (hp i) hn (hpp i) hnp
  simp only [Finset.prod_mul_distrib] at hl
  simp only [leftCoefficient, idealRowHom_argument_mul, row_argument_product _ _ _ hn]
  calc
    _ = idealRowHom e (Ideal.span {n}) * idealRowHom u (Ideal.span {n}) *
        ((∏ i, idealRowHom (p i) (Ideal.span {n})) *
          ∏ i, idealRowHom n (Ideal.span {p i}) ^ t i) := by ring
    _ = _ := by rw [hl]; ring

theorem right_column_reconstruction {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (t : ι → ℕ) (e u n : O)
    (ht : ∀ i, 0 < t i) (ht6 : ∀ i, t i < 6)
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hp : ∀ i, Supported (Ideal.span {p i})) (hn : Supported (Ideal.span {n}))
    (hpp : ∀ i, goodLambda ^ 2 ∣ p i - 1) (hnp : goodLambda ^ 2 ∣ n - 1) :
    rightCoefficient e (u * ∏ i, p i)
      (fun a => ∏ i, idealRowHom a (Ideal.span {p i}) ^ t i) n =
      idealRowHom (e * u * ∏ i, p i ^ ((7-t i) % 6)) (Ideal.span {n}) *
        (∏ i, sexticReciprocityPhase (p i) n ^ (6-t i)) *
        (∏ i, if t i = 1 then if IsCoprime n (p i) then (1 : ℂ) else 0 else 1) := by
  have hl : (∏ i, idealRowHom (p i) (Ideal.span {n}) *
      star (idealRowHom n (Ideal.span {p i}) ^ t i)) =
      ∏ i, sexticReciprocityPhase (p i) n ^ (6-t i) *
        idealRowHom (p i ^ ((7-t i) % 6)) (Ideal.span {n}) *
        (if t i = 1 then if IsCoprime n (p i) then (1 : ℂ) else 0 else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    exact right_local_reduced (p i) n (t i) (ht i) (ht6 i)
      (hg i) (hc i) (hp i) hn (hpp i) hnp
  simp only [Finset.prod_mul_distrib] at hl
  simp only [rightCoefficient, idealRowHom_argument_mul,
    row_argument_product _ _ _ hn]
  calc
    _ = idealRowHom e (Ideal.span {n}) * idealRowHom u (Ideal.span {n}) *
        ((∏ i, idealRowHom (p i) (Ideal.span {n})) *
          ∏ i, star (idealRowHom n (Ideal.span {p i}) ^ t i)) := by
      rw [star_prod]
      ring
    _ = _ := by rw [hl]; ring

/-- Arbitrarily many common primes still produce one fixed-period phase. -/
theorem reciprocity_product_periodic {ι : Type*} [Fintype ι]
    (p : ι → O) (t : ι → ℕ) (x y : O) (hxy : (4 : O) ∣ x-y) :
    (∏ i, sexticReciprocityPhase (p i) x ^ t i) =
      ∏ i, sexticReciprocityPhase (p i) y ^ t i := by
  apply Finset.prod_congr rfl
  intro i _
  rw [sexticReciprocityPhase_congr_right (p i) x y hxy]

/-- The original active character, including its nonunit zeros, is precisely
the ideal-row product used in the two reconstruction identities. -/
theorem finiteSexticRow_as_ideal_rows {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (t : ι → ℕ) (ht : ∀ i, t i ≠ 0) (n : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg t n =
      ∏ i, idealRowHom n (Ideal.span {p i}) ^ t i := by
  unfold finiteSexticRow
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.pow_apply' _ (ht i), idealRowHom_prime n _ (hg i)]

/-- The source's chosen radical generator differs from the product of chosen
prime generators by a unit. The identity does not assume those choices agree. -/
theorem prime_modulus_unit_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) (p : ι → O) (hp : ∀ i, Ideal.span {p i} = P i) :
    ∃ u : Oˣ, finitePrimeModulus P = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} = Ideal.span {finitePrimeModulus P} := by
    rw [← Ideal.prod_span_singleton, span_finitePrimeModulus]
    simp only [hp]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

#print axioms row_power_reduce_six
#print axioms left_column_reconstruction
#print axioms right_column_reconstruction
#print axioms reciprocity_product_periodic
#print axioms finiteSexticRow_as_ideal_rows
#print axioms prime_modulus_unit_product

end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.SignedReconstruction -/

/- BEGIN ORIGINAL MODULE Cycle25.Arithmetic.Geometry ; sha256 c0145ee4ec60383eaad9011778e34009b311e96fbb831bae5676620911966140 -/
section


/-! Rational formulas and geometry certificates for B0.45--B0.49.
This module is elementary real arithmetic and is independent of the analytic route. -/

namespace Cycle25.Arithmetic

noncomputable def delta0 : ℝ :=
  (25-60*ell0+27*ell0^2)/(6*(5+4*ell0-3*ell0^2))
noncomputable def count0 : ℝ := (6*kappa0-1)/(15*kappa0-2)
noncomputable def v0 : ℝ := 5/6-delta0
noncomputable def rprime0 : ℝ :=
  -1+count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2)
noncomputable def h0 : ℝ :=
  -((1+ell0)/2+ell0/(6*kappa0))/(3*rprime0/4-1/(24*kappa0))
noncomputable def x0 : ℝ := 1+ell0-h0
noncomputable def y0 : ℝ := h0-2*ell0

theorem ell0_short_interval : (16712:ℝ)/100000 < ell0 ∧ ell0 < 167121/1000000 := by
  have hl := ell0_lo
  have hu := ell0_hi
  norm_num [rootLo, rootHi] at hl hu
  constructor <;> linarith

theorem delta0_den_pos : 0 < 6*(5+4*ell0-3*ell0^2) := by
  have h := ell0_coarse
  have hsq : ell0^2 ≤ (1:ℝ)/25 := by nlinarith [h.1, h.2]
  nlinarith [h.1]

theorem delta0_interval : (46934:ℝ)/100000 < delta0 ∧ delta0 < 46935/100000 := by
  have h := ell0_short_interval
  unfold delta0
  constructor
  · apply (lt_div_iff₀ delta0_den_pos).2
    nlinarith [sq_nonneg (ell0 - 16712/100000), sq_nonneg (ell0 - 167121/1000000)]
  · apply (div_lt_iff₀ delta0_den_pos).2
    nlinarith [sq_nonneg (ell0 - 16712/100000), sq_nonneg (ell0 - 167121/1000000)]

theorem count0_den_pos : 0 < 15*kappa0-2 := by linarith [kappa0_range.1]

theorem count0_interval : (37837:ℝ)/100000 < count0 ∧ count0 < 37838/100000 := by
  have h := ell0_short_interval
  unfold count0
  constructor
  · apply (lt_div_iff₀ count0_den_pos).2
    unfold kappa0
    linarith
  · apply (div_lt_iff₀ count0_den_pos).2
    unfold kappa0
    linarith

theorem v0_interval : (36398:ℝ)/100000 < v0 ∧ v0 < 364/1000 := by
  unfold v0
  constructor <;> linarith [delta0_interval.1, delta0_interval.2]

theorem binding_second :
    delta0*(6*kappa0+(6*kappa0+2)*ell0) = kappa0*(5-9*ell0) := by
  unfold delta0 kappa0
  have hd : 5+4*ell0-3*ell0^2 ≠ 0 := by
    have := delta0_den_pos
    intro he
    rw [he] at this
    norm_num at this
  ring_nf at hd
  field_simp [hd]
  ring

theorem binding_first :
    (324*kappa0^2-3)*delta0^2+(-756*kappa0^2+54*kappa0+5)*delta0+
      300*kappa0^2-40*kappa0 = 0 := by
  have hd : 5+4*ell0-3*ell0^2 ≠ 0 := by
    have := delta0_den_pos
    intro he
    rw [he] at this
    norm_num at this
  have hd2 : 25+40*ell0-14*ell0^2-24*ell0^3+9*ell0^4 ≠ 0 := by
    convert pow_ne_zero 2 hd using 1
    ring
  ring_nf at hd hd2
  have hid :
      (324*kappa0^2-3)*delta0^2+(-756*kappa0^2+54*kappa0+5)*delta0+
        300*kappa0^2-40*kappa0 =
      (600-675*ell0+189*ell0^2)*quartic ell0/(6*(5+4*ell0-3*ell0^2))^2 := by
    unfold kappa0 delta0 quartic
    field_simp [hd, hd2]
    ring_nf
    field_simp [hd, hd2]
    ring
  rw [hid, ell0_quartic]
  simp

private theorem product_interval {a b la ua lb ub : ℝ}
    (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) : la*lb ≤ a*b ∧ a*b ≤ ua*ub := by
  have ha0 : 0 ≤ a := hla.trans ha.1
  have hb0 : 0 ≤ b := hlb.trans hb.1
  exact ⟨mul_le_mul ha.1 hb.1 hlb ha0, mul_le_mul ha.2 hb.2 hb0 (ha0.trans ha.2)⟩

theorem rprime0_den_pos : 0 < 2*(v0+delta0*count0)^2 := by
  have hc : 0 < count0 := by linarith [count0_interval.1]
  have hd : 0 < delta0 := by linarith [delta0_interval.1]
  have hv : 0 < v0 := by linarith [v0_interval.1]
  positivity

theorem rprime0_interval : (-969:ℝ)/1000 < rprime0 ∧ rprime0 < -968/1000 := by
  have hd := delta0_interval
  have hc := count0_interval
  have hv := v0_interval
  have hd2 : (46934/100000:ℝ)^2 ≤ delta0^2 ∧ delta0^2 ≤ (46935/100000:ℝ)^2 := by
    constructor <;> nlinarith
  have hv2 : (36398/100000:ℝ)^2 ≤ v0^2 ∧ v0^2 ≤ (364/1000:ℝ)^2 := by
    constructor <;> nlinarith
  have hdc := product_interval ⟨le_of_lt hd.1, le_of_lt hd.2⟩
    ⟨le_of_lt hc.1, le_of_lt hc.2⟩ (by norm_num) (by norm_num)
  have hd2c := product_interval hd2 ⟨le_of_lt hc.1, le_of_lt hc.2⟩
    (by norm_num) (by norm_num)
  have hdif : (49:ℝ)/1000 ≤ v0^2-delta0^2*count0 ∧
      v0^2-delta0^2*count0 ≤ 493/10000 := by
    constructor <;> norm_num at * <;> linarith
  have hn := product_interval ⟨le_of_lt hc.1, le_of_lt hc.2⟩ hdif
    (by norm_num) (by norm_num)
  have hs : (541:ℝ)/1000 ≤ v0+delta0*count0 ∧ v0+delta0*count0 ≤ 542/1000 := by
    constructor <;> norm_num at * <;> linarith
  have hs2 : (541/1000:ℝ)^2 ≤ (v0+delta0*count0)^2 ∧
      (v0+delta0*count0)^2 ≤ (542/1000:ℝ)^2 := by
    constructor <;> nlinarith
  unfold rprime0
  constructor
  · have he : (31:ℝ)/1000 < count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) := by
      apply (lt_div_iff₀ rprime0_den_pos).2
      norm_num at hn hs2
      linarith
    linarith
  · have he : count0*(v0^2-delta0^2*count0)/(2*(v0+delta0*count0)^2) < (32:ℝ)/1000 := by
      apply (div_lt_iff₀ rprime0_den_pos).2
      norm_num at hn hs2
      linarith
    linarith

theorem kappa0_short_interval : (74977:ℝ)/100000 < kappa0 ∧ kappa0 < 74978/100000 := by
  have h := ell0_short_interval
  unfold kappa0
  constructor <;> linarith

theorem h0_den_neg : 3*rprime0/4-1/(24*kappa0) < 0 := by
  have hi : 0 < 1/(24*kappa0) := by positivity [kappa0_range.1]
  linarith [rprime0_interval.2]

theorem h0_interval : (793:ℝ)/1000 < h0 ∧ h0 < 795/1000 := by
  have he := ell0_short_interval
  have hk := kappa0_short_interval
  have hr := rprime0_interval
  have hk0 : 0 < kappa0 := by linarith [kappa0_range.1]
  have hnsmall : (37:ℝ)/1000 < ell0/(6*kappa0) ∧ ell0/(6*kappa0) < 372/10000 := by
    constructor
    · apply (lt_div_iff₀ (by positivity : 0 < 6*kappa0)).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < 6*kappa0)).2
      linarith
  have hn : (6205:ℝ)/10000 < (1+ell0)/2+ell0/(6*kappa0) ∧
      (1+ell0)/2+ell0/(6*kappa0) < 6208/10000 := by
    constructor <;> linarith
  have hinv : (555:ℝ)/10000 < 1/(24*kappa0) ∧ 1/(24*kappa0) < 556/10000 := by
    constructor
    · apply (lt_div_iff₀ (by positivity : 0 < 24*kappa0)).2
      linarith
    · apply (div_lt_iff₀ (by positivity : 0 < 24*kappa0)).2
      linarith
  have hden : (7815:ℝ)/10000 < 1/(24*kappa0)-3*rprime0/4 ∧
      1/(24*kappa0)-3*rprime0/4 < 7824/10000 := by
    constructor <;> linarith
  have hdenpos : 0 < 1/(24*kappa0)-3*rprime0/4 := by linarith
  have hrewrite : h0 = ((1+ell0)/2+ell0/(6*kappa0))/(1/(24*kappa0)-3*rprime0/4) := by
    unfold h0
    rw [show 1/(24*kappa0)-3*rprime0/4 = -(3*rprime0/4-1/(24*kappa0)) by ring]
    rw [div_neg, neg_div]
  rw [hrewrite]
  constructor
  · apply (lt_div_iff₀ hdenpos).2
    linarith
  · apply (div_lt_iff₀ hdenpos).2
    linarith

theorem physical_geometry : ell0 < x0 ∧ x0 < y0 ∧ y0 < 2*x0 ∧
    y0 < 1/2 ∧ 1/2 < h0 ∧ h0 < 2*y0 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold x0 y0
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

theorem derivative_geometry : h0 < (4:ℝ)/5 ∧ 0 < h0-4*ell0 ∧ h0-4*ell0 < 13/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  constructor
  · linarith
  constructor <;> linarith

theorem supply_geometry : (1:ℝ)/5 < ell0/h0 ∧ (4:ℝ)/21 < ell0/h0 ∧ y0 < 4*ell0 := by
  have he := ell0_short_interval
  have hh := h0_interval
  have hh0 : 0 < h0 := by linarith
  have hmain : (1:ℝ)/5 < ell0/h0 := (lt_div_iff₀ hh0).2 (by linarith)
  refine ⟨hmain, ?_, ?_⟩
  · linarith
  · unfold y0; linarith

theorem positive_part_branch : 5*ell0 < 1 := by linarith [ell0_short_interval.2]

theorem other_endpoint_margin :
    11/12-49*h0/150+11*ell0/12 < b0-6/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold b0
  linarith

theorem floor_margin : (51:ℝ)/100+h0/3+51*ell0/100 < b0-1/100 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold b0
  linarith

theorem small_row_margin : h0*(17/50-1/6)-y0/2+(63:ℝ)/50*(1/200) < -1/20 := by
  have he := ell0_short_interval
  have hh := h0_interval
  unfold y0
  linarith

theorem positive_A1_minorant (d : ℝ) : 0 < 36-174*d+347*d^2 := by
  nlinarith [sq_nonneg (d - (87:ℝ)/347)]

theorem comparison_margin {κ : ℝ} (hκ : 7/10 ≤ κ) :
    1/16 ≤ (2*κ-1)/(2*(6*κ-1)) := by
  apply (le_div_iff₀ (by linarith : 0 < 2*(6*κ-1))).2
  linarith

theorem counting_derivative_minorant :
    ((8:ℝ)/9)/(((15:ℝ)/2*(7/10)-1)^2) < 1/18 := by norm_num

theorem uniform_derivative_minorant :
    (3:ℝ)/4*(4/5)*(5/12)*(1/18)+(5/12)*(13/100)/(12*(7/10)^2) < 1/10 := by
  norm_num

end Cycle25.Arithmetic
end
/- END ORIGINAL MODULE Cycle25.Arithmetic.Geometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Budget ; sha256 e38c45d009427ad135e5f99b5c9698e186565d120507e02339501099c1d312f6 -/
section


namespace OAI

noncomputable section
namespace SevenEighths.Cycle25DetectorBranchBudget
open Cycle25DetectorRowCount

def commonLoss (ε εm mesh ν : ℝ) : ℝ := 154*ε+εm+mesh+ν

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤ mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤ x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x κ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤ x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(6*κ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(6*κ)-ν)=
      2*(δ*x)*(1-2*m)/(6*κ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤ r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (κ x t r m ε ν : ℝ)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) (hx : 0≤ x) (hx1 : x≤1/2) (ht : 1≤ t) (ht1 : t≤3/2)
    (hr : r≤ crossing x κ t) (hleft : t-r-ε≤ m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(6*κ)) :
    0≤(1-2*m)/(6*κ)-ν ∧ (1-2*m)/(6*κ)-ν≤7/37 ∧
      2*m+6*κ*((1-2*m)/(6*κ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 hk hk1 ht ht1
  have hm : 1/4≤ m := by linarith [hcross.2.2.1]
  have hd : 0<6*κ := by linarith
  have hc : (1-2*m)/(6*κ)≤5/42 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  rw [mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.Cycle25DetectorBranchBudget
end
end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Budget -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Endpoint ; sha256 3a49b221517994d59cbca8da2f61bc333603502f42201e317206b5e170dcd284 -/
section

namespace OAI.SevenEighths.Cycle25DetectorRowCount
noncomputable section

def V (δ : ℝ) : ℝ := 5/6-δ
def cutoff (δ p κ : ℝ) : ℝ := 1+δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))
def rowCount (δ p κ : ℝ) : ℝ :=
  1-δ+δ*coefficient p κ*V δ/(2*(V δ+δ*coefficient p κ))

lemma coefficient_nonneg {p κ : ℝ} (hp : 0≤ p) (hp1 : p≤1/2)
    (hk : 7/10≤κ) (hk1 : κ≤3/4) : 0≤ coefficient p κ := by
  have hb := b_bounds hp hp1 hk hk1
  have hd : 0< denominator p κ := lt_of_lt_of_le (by norm_num) (denominator_lower hp hp1 hk hk1)
  unfold coefficient primeWeight
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) hd.le

lemma cutoff_bounds {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤ p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    1≤ cutoff δ p κ ∧ cutoff δ p κ≤3/2 := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hn : 0≤δ*coefficient p κ := mul_nonneg hδ hc
  have hv : 0< V δ := by unfold V; linarith
  have hd : 0<2*(V δ+δ*coefficient p κ) := by positivity
  unfold cutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hn hd.le)
  · have he : δ*coefficient p κ/(2*(V δ+δ*coefficient p κ))≤1/2 :=
      (div_le_iff₀ hd).mpr (by linarith)
    linarith

theorem short_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤ p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    shortExponent δ p κ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0< V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold shortExponent cutoff rowCount
  field_simp
  ring

theorem long_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤ p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    longExponent δ (cutoff δ p κ)=rowCount δ p κ := by
  have hc := coefficient_nonneg hp hp1 hk hk1
  have hd : V δ+δ*coefficient p κ≠0 := by
    apply ne_of_gt
    have hv : 0< V δ := by unfold V; linarith
    exact add_pos_of_pos_of_nonneg hv (mul_nonneg hδ hc)
  unfold longExponent HeckeDetectorRowCount.longExponent cutoff rowCount V at *
  field_simp
  ring

theorem max_at_cutoff {δ p κ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤3/4)
    (hp : 0≤ p) (hp1 : p≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4) :
    max (shortExponent δ p κ (cutoff δ p κ)) (longExponent δ (cutoff δ p κ))=rowCount δ p κ := by
  rw [short_at_cutoff hδ hδ1 hp hp1 hk hk1,long_at_cutoff hδ hδ1 hp hp1 hk hk1,max_self]
end
end OAI.SevenEighths.Cycle25DetectorRowCount
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Endpoint -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.Optimization ; sha256 350f167638c34b2e377efc354636bd1fb62ff89020bc8e2d32977d3340e544e4 -/
section



namespace OAI

noncomputable section
namespace SevenEighths.Cycle25DetectorRowCount

theorem count_bound_of_source_branches (B C U δ x κ t r m ε ν γ : ℝ)
    (hC : 0≤ C) (hU : 1≤ U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤ x) (hx' : x≤1/2) (hk : 7/10≤κ) (hk1 : κ≤3/4)
    (ht : 1≤ t) (ht' : t≤3/2) (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤ m) (hright : r≤ t+γ)
    (hI0 : B≤ C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤ C*U^(1-2*δ*m+ε))
    (hI : 23/37≤ r → r<1 → ν<(1-r)/2 → B≤ C*U^(inverseExponent δ x r+ε))
    (hP : r≤ crossing x κ t → m<1/2 → ν<(1-2*m)/(6*κ) →
      B≤ C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(6*κ)+ε)) :
    B≤ C*U^(max (shortExponent δ x κ t) (longExponent δ t)+ε+6*ν+5*γ) := by
  let target := max (shortExponent δ x κ t) (longExponent δ t)+ε+6*ν+5*γ
  have hshort : shortExponent δ x κ t≤ max (shortExponent δ x κ t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t≤ max (shortExponent δ x κ t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' hk hk1 ht'
  have hcross := crossing_bounds hx hx' hk hk1 ht ht'
  have hchoose := selected_short_bound (t:=t) (r:=r) hδ hx hx' hk hk1
  have promote (p : ℝ) (hp : B≤ C*U^p) (hpt : p≤ target) : B≤ C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1≤ r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := HeckeDetectorRowCount.long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ≤γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x κ t≤ r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hz := HeckeDetectorRowCount.inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r≤ crossing x κ t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(6*κ)≤ν
  · apply promote _ hP0
    have hk0 : 0<κ := by linarith
    have hktop : κ≤1 := by linarith
    have hz := HeckeDetectorRowCount.plain_zero_capacity hδ hk0 hktop hν
      hcap
    have hv : 6*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ≤1 by linarith) hx hx' hk hk1 hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

end SevenEighths.Cycle25DetectorRowCount

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.Optimization -/

/- BEGIN ORIGINAL MODULE Cycle25.Assembly.Count.SourceBatch ; sha256 1b046c8026aa4ee7458ac17ac5126501e829989e19a1d7d824c85ce209a110f3 -/
section





/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.Cycle25WeightedHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤ tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (7/37)*dmax≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=> hnext u.val u.property) (fun u=> hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤ Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin dmax mesh hdmin hd hd' hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=> w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=> ell j/d) z mesh binWidth hm hb (fun j _=> hwp j) (fun j _=> hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end SevenEighths.Cycle25WeightedHighRowFamily

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Assembly.Count.SourceBatch -/
