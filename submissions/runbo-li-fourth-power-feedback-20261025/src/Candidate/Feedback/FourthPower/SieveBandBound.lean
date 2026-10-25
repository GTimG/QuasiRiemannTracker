/- Copyright (c) 2026 Sil. Apache-2.0.
Aggregate the actual Poisson family over all columns and one frequency band.
The majorants below contain only the already defined concrete lambda norms.
-/
import Candidate.Feedback.FourthPower.SieveColumnPartition

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveBandBound
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalQuadraticSieve EisensteinSchwartzPoisson ConcreteTraceCRT
open SexticSieve SieveBoxFamily SieveDualGeometry SievePairPoisson
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

def density (ε : ℝ) (hε : 0 < ε) (C P L : ℝ) : ℝ :=
  C*L^ε*SieveRanges.lambda L (2*P)*
    (IdealCoprimeSieveOperator.supportConstant ε hε*(2*P)^ε)/P

def weight (ε : ℝ) (hε : 0 < ε) (C D : ℝ) (d : ℕ) (M N X P Q : ℝ) : ℝ :=
  (D/(1+M*X/(2*P*Q))^d)^2 *
    (density ε hε C P (N*X/Q)*density ε hε C Q (N*X/P))

theorem density_nonneg (ε : ℝ) (hε : 0 < ε) (C P L : ℝ)
    (hC : 0 ≤ C) (hP : 0 < P) (hL : 0 ≤ L) : 0 ≤ density ε hε C P L := by
  have hl := SieveRanges.lambda_nonneg L (2*P)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  unfold density
  positivity

theorem density_mono (ε : ℝ) (hε : 0 < ε) (C P L L' : ℝ)
    (hC : 0 ≤ C) (hP : 0 < P) (hL : 0 ≤ L) (hLL : L ≤ L') :
    density ε hε C P L ≤ density ε hε C P L' := by
  have hL' : 0 ≤ L' := hL.trans hLL
  have hl := SieveRanges.lambda_nonneg L (2*P)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  unfold density
  apply div_le_div_of_nonneg_right _ hP.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL hLL hε.le) hC)
    (SieveRanges.lambda_mono hLL le_rfl) hl (by positivity)

theorem factor_norm_ge_one (X : ℝ) (l : SieveFrequencyGeometry.BadLabel X) :
    1 ≤ ‖eisEmbedding (SieveFrequencyGeometry.factor X l)‖^2 := by
  rw [SieveFrequencyGeometry.factor,SieveFrequencyGeometry.badFactor_norm_sq]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))

/-- The powers of 2 and 3 cancel from the Fourier scale and only shorten
the two completed row ranges. They are never discarded from a character. -/
theorem single_fiber_band (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (d : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ {n : Type*} [Fintype n] (N : ℝ) (hN : 0 ≤ N) (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (X : ℝ), 0 < X → ∀ (R : Finset O)
        (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X),
        (∀ x ∈ R, X/2 ≤ (Ideal.absNorm (Ideal.span {x}) : ℝ)) →
        ∀ (M : ℝ), 0 < M → ∀ (l₁ l₂ : SieveColumnPartition.Label N)
        (l : SieveFrequencyGeometry.BadLabel X) (a b : n → ℂ),
        (∑ k : SieveFrequencyGeometry.frequencies X R hR l,
          ‖∑ i : SieveColumnPartition.Fiber N cols hc l₁,
            ∑ j : SieveColumnPartition.Fiber N cols hc l₂,
            if IsCoprime (cols i.val) (cols j.val) then
              dualTerm (cols i.val) (cols j.val) (hc i.val) (hc j.val) (a i.val) (b j.val)
                W M (SieveFrequencyGeometry.factor X l*primaryGenerator k.val) else 0‖)^2 ≤
        weight ε hε C D d M N X (SieveColumnPartition.scale l₁) (SieveColumnPartition.scale l₂)*
          ((∑ i : SieveColumnPartition.Fiber N cols hc l₁, ‖a i.val‖^2)*
            (∑ j : SieveColumnPartition.Fiber N cols hc l₂, ‖b j.val‖^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := actual_box_bound ε hε W d
  refine ⟨C,D,hC,hD,?_⟩
  intro n _ N hN cols hc hf hi hn X hX R hR hRlo M hM l₁ l₂ l a b
  let P := SieveColumnPartition.scale l₁
  let Q := SieveColumnPartition.scale l₂
  let c := SieveFrequencyGeometry.factor X l
  let t : ℝ := ‖eisEmbedding c‖^2
  let K₀ : ℝ := X/(2*t)
  have hP : 0 < P := SieveColumnPartition.scale_pos l₁
  have hQ : 0 < Q := SieveColumnPartition.scale_pos l₂
  have ht : 1 ≤ t := factor_norm_ge_one X l
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  have hlo : X/2/t = K₀ := by dsimp only [K₀]; ring
  have hhi : X/t = 2*K₀ := by dsimp only [K₀]; ring
  have hKs : ∀ K ∈ SieveFrequencyGeometry.frequencies X R hR l,
      Supported K ∧ K₀ ≤ (Ideal.absNorm K : ℝ) ∧ (Ideal.absNorm K : ℝ) ≤ 2*K₀ := by
    intro K hK
    have hg := SieveFrequencyGeometry.frequency_geometry X R hR (X/2) hRlo l K hK
    change Supported K ∧ X/2/t ≤ (Ideal.absNorm K : ℝ) ∧ (Ideal.absNorm K : ℝ) ≤ X/t at hg
    rw [hlo,hhi] at hg
    exact hg
  have hb := h (SieveColumnPartition.box N hN cols hc hf hn l₁)
    (SieveColumnPartition.box N hN cols hc hf hn l₂) _ _
    (SieveColumnPartition.location N hN cols hc hf hi hn l₁)
    (SieveColumnPartition.location N hN cols hc hf hi hn l₂)
    (SieveFrequencyGeometry.frequencies X R hR l) K₀ hK₀ hKs M hM c
    (SieveFrequencyGeometry.factor_nonzero X l) (fun i => a i.val) (fun j => b j.val)
  have he₁ : 2*(N/Q)*K₀ = (N*X/Q)/t := by dsimp only [K₀]; ring
  have he₂ : 2*(N/P)*K₀ = (N*X/P)/t := by dsimp only [K₀]; ring
  have hl₁ : 2*(N/Q)*K₀ ≤ N*X/Q := by
    rw [he₁]
    exact div_le_self (by positivity) ht
  have hl₂ : 2*(N/P)*K₀ ≤ N*X/P := by
    rw [he₂]
    exact div_le_self (by positivity) ht
  have hd₁ := density_mono ε hε C P (2*(N/Q)*K₀) (N*X/Q) hC.le hP (by positivity) hl₁
  have hd₂ := density_mono ε hε C Q (2*(N/P)*K₀) (N*X/P) hC.le hQ (by positivity) hl₂
  have hd₁0 := density_nonneg ε hε C P (2*(N/Q)*K₀) hC.le hP (by positivity)
  have hd₂0 := density_nonneg ε hε C Q (2*(N/P)*K₀) hC.le hQ (by positivity)
  have hd₁' := density_nonneg ε hε C P (N*X/Q) hC.le hP (by positivity)
  have he : M*t*K₀/(P*Q) = M*X/(2*P*Q) := by
    dsimp only [K₀]
    field_simp
    <;> ring
  change _ ≤ (D/(1+M*t*K₀/(P*Q))^d)^2 *
    ((density ε hε C P (2*(N/Q)*K₀)*_)*(density ε hε C Q (2*(N/P)*K₀)*_)) at hb
  rw [he] at hb
  apply hb.trans
  unfold weight
  have hprod := mul_le_mul hd₁ hd₂ hd₂0 hd₁'
  have hm := mul_le_mul_of_nonneg_right hprod
    (show 0 ≤ (∑ i : SieveColumnPartition.Fiber N cols hc l₁, ‖a i.val‖^2)*
      (∑ j : SieveColumnPartition.Fiber N cols hc l₂, ‖b j.val‖^2) by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (D/(1+M*X/(2*P*Q))^d))
  convert hh using 1 <;> ring

theorem frequency_norm_sum (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) (F : O → ℂ) :
    (∑ x : R, ‖F x.val‖) = ∑ l : SieveFrequencyGeometry.BadLabel X,
      ∑ K : SieveFrequencyGeometry.frequencies X R hR l,
        ‖F (SieveFrequencyGeometry.factor X l*primaryGenerator K.val)‖ := by
  have he := congrArg Complex.re
    (SieveFrequencyGeometry.frequency_sum X R hR (fun x => (‖F x‖ : ℂ)))
  simp only [Complex.re_sum,Complex.ofReal_re] at he
  calc
    _ = ∑ x ∈ R, ‖F x‖ := Finset.sum_coe_sort R (fun x => ‖F x‖)
    _ = _ := he
    _ = _ := Finset.sum_congr rfl (fun l _ =>
      (Finset.sum_coe_sort (SieveFrequencyGeometry.frequencies X R hR l)
        (fun K => ‖F (SieveFrequencyGeometry.factor X l*primaryGenerator K)‖)).symm)

theorem pair_partition {n : Type*} [Fintype n] (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (F : n → n → ℂ) :
    (∑ i, ∑ j, F i j) = ∑ l : SieveColumnPartition.Label N,
      ∑ m : SieveColumnPartition.Label N, ∑ i : SieveColumnPartition.Fiber N cols hc l,
        ∑ j : SieveColumnPartition.Fiber N cols hc m, F i.val j.val := by
  calc
    _ = ∑ l : SieveColumnPartition.Label N, ∑ i : SieveColumnPartition.Fiber N cols hc l,
        ∑ j, F i.val j := (Fintype.sum_fiberwise (SieveColumnPartition.label N cols hc)
          (fun i => ∑ j, F i j)).symm
    _ = ∑ l : SieveColumnPartition.Label N, ∑ i : SieveColumnPartition.Fiber N cols hc l,
        ∑ m : SieveColumnPartition.Label N, ∑ j : SieveColumnPartition.Fiber N cols hc m,
          F i.val j.val := by simp only [Fintype.sum_fiberwise]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm

theorem fiber_scale_bounds {n : Type*} (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
    (l : SieveColumnPartition.Label N) (i : SieveColumnPartition.Fiber N cols hc l) :
    1 ≤ SieveColumnPartition.scale l ∧ SieveColumnPartition.scale l ≤ N := by
  refine ⟨divisorDyadicScale_ge_one l.2.val,?_⟩
  apply (SieveColumnPartition.fiber_radical_bounds N cols hc hn l i).1.trans
  exact (CenteredExceptionalCount.norm_le_of_dvd (hc i.val).1
    (Ideal.dvd_iff_le.mpr (cols i.val).le_radical)).trans (hn i.val)

def part {n : Type*} [Fintype n] (N X : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (a b : n → ℂ) (l : SieveFrequencyGeometry.BadLabel X)
    (u v : SieveColumnPartition.Label N) : ℝ :=
  ∑ k : SieveFrequencyGeometry.frequencies X R hR l,
    ‖∑ i : SieveColumnPartition.Fiber N cols hc u,
      ∑ j : SieveColumnPartition.Fiber N cols hc v,
      if IsCoprime (cols i.val) (cols j.val) then
        dualTerm (cols i.val) (cols j.val) (hc i.val) (hc j.val) (a i.val) (b j.val)
          W M (SieveFrequencyGeometry.factor X l*primaryGenerator k.val) else 0‖

theorem partition_triangle {n : Type*} [Fintype n] (N X : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (a b : n → ℂ) :
    (∑ x : R, ‖∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
      dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (b j) W M x.val else 0‖) ≤
    ∑ l : SieveFrequencyGeometry.BadLabel X, ∑ u : SieveColumnPartition.Label N,
      ∑ v : SieveColumnPartition.Label N, part N X cols hc R hR W M a b l u v := by
  rw [frequency_norm_sum X R hR (fun x => ∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
    dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (b j) W M x else 0)]
  apply Finset.sum_le_sum
  intro l _
  let F (k : SieveFrequencyGeometry.frequencies X R hR l) (i j : n) : ℂ :=
    if IsCoprime (cols i) (cols j) then dualTerm (cols i) (cols j) (hc i) (hc j)
      (a i) (b j) W M (SieveFrequencyGeometry.factor X l*primaryGenerator k.val) else 0
  let H (k : SieveFrequencyGeometry.frequencies X R hR l)
      (u v : SieveColumnPartition.Label N) : ℝ :=
    ‖∑ i : SieveColumnPartition.Fiber N cols hc u,
      ∑ j : SieveColumnPartition.Fiber N cols hc v, F k i.val j.val‖
  change (∑ k, ‖∑ i, ∑ j, F k i j‖) ≤ ∑ u, ∑ v, ∑ k, H k u v
  calc
    _ ≤ ∑ k, ∑ u, ∑ v, H k u v := by
      apply Finset.sum_le_sum
      intro k _
      rw [pair_partition N cols hc (F k)]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun u _ => norm_sum_le _ _))
    _ = _ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun u _ => Finset.sum_comm)

theorem square_sum_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (T : ℝ)
    (h : ∀ i, (f i)^2 ≤ T) : (∑ i, f i)^2 ≤ (Fintype.card ι : ℝ)^2*T := by
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
  have hb := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i))
    (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  simp only [Finset.card_univ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs hb
  exact hs.trans (hb.trans_eq (by ring))

/-- One full finite frequency band, with every column and every bad-prime
factor restored. T is any explicit upper bound for the displayed concrete
weight; this is a numerical majorization interface, not a sieve axiom. -/
theorem actual_band_bound (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (d : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ {n : Type*} [Fintype n] (N : ℝ) (hN : 0 ≤ N) (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (X : ℝ), 0 < X → ∀ (R : Finset O)
        (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X),
        (∀ x ∈ R, X/2 ≤ (Ideal.absNorm (Ideal.span {x}) : ℝ)) →
        ∀ (M : ℝ), 0 < M → ∀ T : ℝ, 0 ≤ T →
        (∀ P Q : ℝ, 1 ≤ P → P ≤ N → 1 ≤ Q → Q ≤ N → weight ε hε C D d M N X P Q ≤ T) →
        ∀ a b : n → ℂ,
        (∑ x : R, ‖∑ i, ∑ j, if IsCoprime (cols i) (cols j) then
          dualTerm (cols i) (cols j) (hc i) (hc j) (a i) (b j) W M x.val else 0‖)^2 ≤
        ((Fintype.card (SieveFrequencyGeometry.BadLabel X) : ℝ)*
          (Fintype.card (SieveColumnPartition.Label N) : ℝ)^2)^2 * T *
            ((∑ i, ‖a i‖^2)*(∑ j, ‖b j‖^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := single_fiber_band ε hε W d
  refine ⟨C,D,hC,hD,?_⟩
  intro n _ N hN cols hc hf hi hn X hX R hR hRlo M hM T hT hweight a b
  let A : ℝ := ∑ i, ‖a i‖^2
  let B : ℝ := ∑ j, ‖b j‖^2
  let f := part N X cols hc R hR W M a b
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp (l : SieveFrequencyGeometry.BadLabel X) (u v : SieveColumnPartition.Label N) :
      (f l u v)^2 ≤ T*(A*B) := by
    by_cases hu : Nonempty (SieveColumnPartition.Fiber N cols hc u)
    · by_cases hv : Nonempty (SieveColumnPartition.Fiber N cols hc v)
      · obtain ⟨i⟩ := hu
        obtain ⟨j⟩ := hv
        have hu' := fiber_scale_bounds N cols hc hn u i
        have hv' := fiber_scale_bounds N cols hc hn v j
        have hw := hweight _ _ hu'.1 hu'.2 hv'.1 hv'.2
        have hb := h N hN cols hc hf hi hn X hX R hR hRlo M hM u v l a b
        apply hb.trans
        have ha' := SieveColumnPartition.fiber_mass_le N cols hc a u
        have hb' := SieveColumnPartition.fiber_mass_le N cols hc b v
        have hm := mul_le_mul ha' hb' (Finset.sum_nonneg (fun j _ => sq_nonneg _)) hA
        exact mul_le_mul hw hm (by positivity) hT
      · letI : IsEmpty (SieveColumnPartition.Fiber N cols hc v) := ⟨fun j => hv ⟨j⟩⟩
        simp only [f,part,Finset.univ_eq_empty,Finset.sum_empty,norm_zero,Finset.sum_const_zero,
          zero_pow (by decide : (2 : ℕ) ≠ 0)]
        positivity
    · letI : IsEmpty (SieveColumnPartition.Fiber N cols hc u) := ⟨fun i => hu ⟨i⟩⟩
      simp only [f,part,Finset.univ_eq_empty,Finset.sum_empty,norm_zero,Finset.sum_const_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0)]
      positivity
  let L : ℝ := Fintype.card (SieveColumnPartition.Label N)
  have hu (l : SieveFrequencyGeometry.BadLabel X) (u : SieveColumnPartition.Label N) :
      (∑ v, f l u v)^2 ≤ L^2*(T*(A*B)) := square_sum_bound (f l u) _ (hp l u)
  have hl (l : SieveFrequencyGeometry.BadLabel X) :
      (∑ u, ∑ v, f l u v)^2 ≤ L^2*(L^2*(T*(A*B))) :=
    square_sum_bound (fun u => ∑ v, f l u v) _ (hu l)
  have hb := square_sum_bound (fun l => ∑ u, ∑ v, f l u v) _ hl
  have ht := partition_triangle N X cols hc R hR W M a b
  have hs := pow_le_pow_left₀ (Finset.sum_nonneg (fun x _ => norm_nonneg _)) ht 2
  exact hs.trans (hb.trans_eq (by dsimp only [L,A,B]; ring))

/-- Keep the column scales fixed until the infinite frequency sum has been
estimated. This avoids replacing each band by a different worst scale. -/
theorem fixed_column_band (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (d : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ {n : Type*} [Fintype n] (N : ℝ) (hN : 0 ≤ N) (cols : n → Id)
        (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
        (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
        (X : ℝ), 0 < X → ∀ (R : Finset O)
        (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X),
        (∀ x ∈ R, X/2 ≤ (Ideal.absNorm (Ideal.span {x}) : ℝ)) →
        ∀ (M : ℝ), 0 < M → ∀ (u v : SieveColumnPartition.Label N) (a b : n → ℂ),
        (∑ x : R, ‖∑ i : SieveColumnPartition.Fiber N cols hc u,
          ∑ j : SieveColumnPartition.Fiber N cols hc v,
          if IsCoprime (cols i.val) (cols j.val) then
            dualTerm (cols i.val) (cols j.val) (hc i.val) (hc j.val) (a i.val) (b j.val)
              W M x.val else 0‖) ≤
        (Fintype.card (SieveFrequencyGeometry.BadLabel X) : ℝ)*
          (D/(1+M*X/(2*SieveColumnPartition.scale u*SieveColumnPartition.scale v))^d)*
          Real.sqrt (density ε hε C (SieveColumnPartition.scale u) (N*X/SieveColumnPartition.scale v)*
            density ε hε C (SieveColumnPartition.scale v) (N*X/SieveColumnPartition.scale u))*
          Real.sqrt ((∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
            (∑ j : SieveColumnPartition.Fiber N cols hc v, ‖b j.val‖^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := single_fiber_band ε hε W d
  refine ⟨C,D,hC,hD,?_⟩
  intro n _ N hN cols hc hf hi hn X hX R hR hRlo M hM u v a b
  let P := SieveColumnPartition.scale u
  let Q := SieveColumnPartition.scale v
  let G := density ε hε C P (N*X/Q)*density ε hε C Q (N*X/P)
  let E := (∑ i : SieveColumnPartition.Fiber N cols hc u, ‖a i.val‖^2)*
    (∑ j : SieveColumnPartition.Fiber N cols hc v, ‖b j.val‖^2)
  let V := D/(1+M*X/(2*P*Q))^d*Real.sqrt G*Real.sqrt E
  have hP : 0 < P := SieveColumnPartition.scale_pos u
  have hQ : 0 < Q := SieveColumnPartition.scale_pos v
  have hg₁ := density_nonneg ε hε C P (N*X/Q) hC.le hP (by positivity)
  have hg₂ := density_nonneg ε hε C Q (N*X/P) hC.le hQ (by positivity)
  have hG : 0 ≤ G := mul_nonneg hg₁ hg₂
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hv (l : SieveFrequencyGeometry.BadLabel X) : part N X cols hc R hR W M a b l u v ≤ V := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => norm_nonneg _)) hV).mp
    have hb := h N hN cols hc hf hi hn X hX R hR hRlo M hM u v l a b
    apply hb.trans_eq
    dsimp only [V,weight]
    rw [mul_pow,mul_pow,Real.sq_sqrt hG,Real.sq_sqrt hE]
  have he := frequency_norm_sum X R hR (fun x => ∑ i : SieveColumnPartition.Fiber N cols hc u,
    ∑ j : SieveColumnPartition.Fiber N cols hc v,
      if IsCoprime (cols i.val) (cols j.val) then
        dualTerm (cols i.val) (cols j.val) (hc i.val) (hc j.val) (a i.val) (b j.val) W M x else 0)
  rw [he]
  change (∑ l, part N X cols hc R hR W M a b l u v) ≤ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun l _ => hv l)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  exact hs.trans_eq (by dsimp only [V,G,E,P,Q]; ring)

end
end Candidate.Feedback.FourthPower.SieveBandBound
