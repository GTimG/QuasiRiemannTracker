/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal two-allocation MAIN prefactor uses at most seven annular bands,
the actual fixed-cell prime pool, and uniform divisor-cardinality bounds. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.MarkedMainRemainderAllocation
import Submissions.hailey_collet_1252270103.Record1252270103Source.Pool.FixedCell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.MarkedMainPrefactor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstAnnularMajorant
open QRH.Record1252270103Source.Pool QRH.Record1252270103Source.MarkedMainRemainder
local notation "O"=>HeckeFamily.O

theorem fixed_pool_compensation {P : Finset (Ideal O)} {Z a ell mesh loss BD Bsource : ℝ} {depth : ℕ}
    (h : FixedCellPoolData P Z a ell mesh loss BD Bsource depth) :
    Z^a/(P.card:ℝ)≤Z^loss := by
  have hh:=mul_le_mul_of_nonneg_left h.reciprocal (Real.rpow_nonneg (zero_lt_one.trans h.scale_gt_one).le a)
  rw [←Real.rpow_add (zero_lt_one.trans h.scale_gt_one),show a+(-a+loss)=loss by ring] at hh
  simpa only [div_eq_mul_inv] using hh

/-- The power loss is fixed before either child type. N affects only the
constant; it does not multiply the exponent in the conclusion. -/
theorem uniform_two_card_squares (N : ℕ) (B₁ B₂ ε : ℝ)
    (hB₁ : 0≤B₁) (hB₂ : 0≤B₂) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀Z : ℝ,1≤Z→
    ∀{ι₁ ι₂ : Type}[Fintype ι₁][Fintype ι₂](s₁ : Input ι₁)(s₂ : Input ι₂),
      Fintype.card ι₁≤N→Fintype.card ι₂≤N→
    ∀C₁ C₂ : Ideal O,C₁≠0→C₂≠0→(C₁.absNorm:ℝ)≤Z^B₁→(C₂.absNorm:ℝ)≤Z^B₂→
      ((actualAllocations s₁.pools C₁).card:ℝ)^2*((actualAllocations s₂.pools C₂).card:ℝ)^2≤D*Z^ε := by
  let δ:=ε/(B₁+B₂+1)
  have hden:0<B₁+B₂+1:=by positivity
  have hδ:0<δ:=div_pos hε hden
  have hpay:(B₁+B₂)*δ≤ε := by
    have he:δ*(B₁+B₂+1)=ε:=by dsimp only [δ];field_simp
    nlinarith
  obtain ⟨D,hD,hcard⟩:=uniform_allocation_card_square N δ hδ
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro Z hZ ι₁ ι₂ _ _ s₁ s₂ hn₁ hn₂ C₁ C₂ hc₁ hc₂ hcap₁ hcap₂
  have bound {ι : Type}[Fintype ι](s : Input ι)(hn:Fintype.card ι≤N)(C:Ideal O)(hc:C≠0)
      (B:ℝ)(hcap:(C.absNorm:ℝ)≤Z^B) :
      ((actualAllocations s.pools C).card:ℝ)^2≤D*Z^(B*δ) := by
    have hp:=Real.rpow_le_rpow (Nat.cast_nonneg C.absNorm) hcap hδ.le
    rw [←Real.rpow_mul (zero_le_one.trans hZ)] at hp
    exact (hcard s hn C hc).trans (mul_le_mul_of_nonneg_left hp hD.le)
  have h:=mul_le_mul (bound s₁ hn₁ C₁ hc₁ B₁ hcap₁) (bound s₂ hn₂ C₂ hc₂ B₂ hcap₂)
    (sq_nonneg _) (by positivity)
  have he:(D*Z^(B₁*δ))*(D*Z^(B₂*δ))=D^2*Z^((B₁+B₂)*δ) := by
    rw [add_mul,Real.rpow_add (zero_lt_one.trans_le hZ)]
    ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpay) (sq_nonneg D))

/-- Exact prefactor used after selected first and second allocations. The
band count is paid by seven, not by a scale-dependent dyad estimate. The
fixed-cell pool supplies its genuine reciprocal, and both card squares remain. -/
theorem uniform_main_prefactor (N : ℕ) (B₁ B₂ ε ell lowerFactor radiusMax : ℝ)
    (hB₁ : 0≤B₁) (hB₂ : 0≤B₂) (hε : 0<ε) (hell : 0<ell)
    (hlower : 0<lowerFactor) (hmax : 0≤radiusMax) :
    ∃C : ℝ,0<C ∧ ∀{ι₁ ι₂ : Type}[Fintype ι₁][Fintype ι₂](s₁ : Input ι₁)(s₂ : Input ι₂),
      Fintype.card ι₁≤N→Fintype.card ι₂≤N→
    ∀(C₁ C₂ : Ideal O)(P : Finset (Ideal O))(Z a mesh loss BD Bsource : ℝ)(depth : ℕ),
      C₁≠0→C₂≠0→(C₁.absNorm:ℝ)≤Z^B₁→(C₂.absNorm:ℝ)≤Z^B₂→
      FixedCellPoolData P Z a ell mesh loss BD Bsource depth→
    ∀ H0 radius : ℝ, 0 < H0 → 0 ≤ radius + 6*a → radius + 6*a ≤ radiusMax →
      ((bands H0).card:ℝ)*((actualAllocations s₁.pools C₁).card:ℝ)^2*
        ((actualAllocations s₂.pools C₂).card:ℝ)^2*(Z^a/(P.card:ℝ))*
        ((radius+6*a)/ell)/lowerFactor≤C*Z^(ε+loss) := by
  obtain ⟨D,hD,hcards⟩:=uniform_two_card_squares N B₁ B₂ ε hB₁ hB₂ hε
  let C:=1+7*D*(radiusMax/ell)/lowerFactor
  have hC:0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro ι₁ ι₂ _ _ s₁ s₂ hn₁ hn₂ C₁ C₂ P Z a mesh loss BD Bsource depth hc₁ hc₂ hcap₁ hcap₂ hpool H0 radius hH hrad0 hrad
  have hc:=hcards Z hpool.scale_gt_one.le s₁ s₂ hn₁ hn₂ C₁ C₂ hc₁ hc₂ hcap₁ hcap₂
  have hp:=fixed_pool_compensation hpool
  have hr:(radius+6*a)/ell≤radiusMax/ell:=div_le_div_of_nonneg_right hrad hell.le
  have hz:0<Z:=zero_lt_one.trans hpool.scale_gt_one
  have hprod:((bands H0).card:ℝ)*
      (((actualAllocations s₁.pools C₁).card:ℝ)^2*((actualAllocations s₂.pools C₂).card:ℝ)^2)≤7*(D*Z^ε) :=
    mul_le_mul (bands_card H0 hH) hc (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  have hp':((bands H0).card:ℝ)*
      (((actualAllocations s₁.pools C₁).card:ℝ)^2*((actualAllocations s₂.pools C₂).card:ℝ)^2)*
        (Z^a/(P.card:ℝ))*((radius+6*a)/ell)≤
      (7*(D*Z^ε))*Z^loss*(radiusMax/ell) :=
    mul_le_mul (mul_le_mul hprod hp (div_nonneg (Real.rpow_nonneg hz.le a) (Nat.cast_nonneg _))
      (by positivity)) hr (div_nonneg hrad0 hell.le) (by positivity)
  have hd:=div_le_div_of_nonneg_right hp' hlower.le
  have he:(7*(D*Z^ε))*Z^loss*(radiusMax/ell)/lowerFactor=
      (7*D*(radiusMax/ell)/lowerFactor)*Z^(ε+loss) := by
    rw [Real.rpow_add hz]
    ring
  rw [he] at hd
  have hconst:7*D*(radiusMax/ell)/lowerFactor≤C:=by dsimp only [C];linarith
  exact (le_of_eq (by ring)).trans (hd.trans
    (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hz.le _)))

end
end QRH.Record1252270103Source.MarkedMainPrefactor
#print axioms QRH.Record1252270103Source.MarkedMainPrefactor.fixed_pool_compensation
#print axioms QRH.Record1252270103Source.MarkedMainPrefactor.uniform_two_card_squares
#print axioms QRH.Record1252270103Source.MarkedMainPrefactor.uniform_main_prefactor
