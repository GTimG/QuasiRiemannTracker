/- Copyright (c) 2026 Sil. Apache-2.0.
Finite genuine-allocation budget, with original prefix denominators and
the positive-part principal saving. No row/energy bound is assumed.
-/
import Candidate.FourthPower.MixedPrincipalAllocations
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentAllocationCost
open CenteredMomentFiniteProfileExceptional CenteredMomentSourceRectangle
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalCentered
open MixedPrincipalPositivePart MixedPrincipalMasked MixedLiveNormalization
local notation "Id" => Ideal HeckeFamily.O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The live marked factors enlarged to the original finite grid.
No M, dimension or numerical factor is absorbed into an unspecified C. -/
def fullMarkedCost (s : Source ι a b) : ℝ :=
  (∏i,256*s.M i)*(∏i,s.M i)*2^Fintype.card ι*((∏i,s.M i)*2^Fintype.card ι)

theorem fullMarkedCost_eq (s : Source ι a b) :
    fullMarkedCost s=(1024:ℝ)^Fintype.card ι*(∏i,s.M i)^3 := by
  simp only [fullMarkedCost,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  calc
    _ = ((256:ℝ)*2*2)^Fintype.card ι*(∏i,s.M i)^3 := by
      simp only [mul_pow]
      ring
    _ = _ := by norm_num

theorem fullMarkedCost_nonneg (s : Source ι a b) : 0≤fullMarkedCost s := by
  have hM : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  have hM256 : 0≤∏i,256*s.M i :=
    Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hM i)))
  unfold fullMarkedCost
  positivity

theorem markedCost_le_full (s : Source ι a b) : s.markedCost≤fullMarkedCost s := by
  have hm (i : ι) : 0≤s.M i := zero_le_one.trans (s.hM i)
  have h₁ : (∏i : liveIndices s.B,256*s.M i.val)≤∏i,256*s.M i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) (fun i=>256*s.M i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>mul_nonneg (by norm_num) (hm i)) (fun i _ _=>by linarith [s.hM i])
  have h₂ : (∏i : liveIndices s.B,s.M i.val)≤∏i,s.M i := by
    rw [Finset.prod_coe_sort (liveIndices s.B) (fun i=>s.M i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>hm i) (fun i _ _=>s.hM i)
  have hn : Fintype.card (liveIndices s.B)≤Fintype.card ι := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq Finset.card_univ
  have h₃ : (2:ℝ)^Fintype.card (liveIndices s.B)≤2^Fintype.card ι :=
    pow_le_pow_right₀ (by norm_num) hn
  have hlive : 0≤∏i : liveIndices s.B,s.M i.val := Finset.prod_nonneg (fun i _=>hm i.val)
  have hfull : 0≤∏i,256*s.M i := Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (hm i))
  have hM : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>hm i)
  unfold Source.markedCost fullMarkedCost
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul h₁ h₂ hlive hfull) h₃ (by positivity) (mul_nonneg hfull hM))
    (mul_nonneg hM (by positivity))

/-- Original volume, prefix and profile factors before dividing by the
genuine common ideal. The same quantity works for every allocation. -/
def baseBudget (s : Source ι a b) (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε : ℝ) : ℝ :=
  (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^J*fullMarkedCost s*
    Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d

theorem baseBudget_nonneg (s : Source ι a b) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0≤Z) : 0≤baseBudget s J control Z ε := by
  have := sourceControl_nonneg control s.W₁
  have := sourceControl_nonneg control s.W₂
  have := fullMarkedCost_nonneg s
  have := (pairNorm_pos s.hd.1 s.hd.2).le
  unfold baseBudget
  positivity

theorem allocated_budget_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0≤Z) :
    (allocationSource s hb cover G B).budget J control Z ε≤
      baseBudget s J control Z ε/(G.absNorm:ℝ) := by
  let A := (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    (1+‖s.t₁‖+‖s.t₂‖)^J*Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d/(G.absNorm:ℝ)
  have hA : 0≤A := by
    have := sourceControl_nonneg control s.W₁
    have := sourceControl_nonneg control s.W₂
    have := (pairNorm_pos s.hd.1 s.hd.2).le
    dsimp only [A]
    positivity
  calc
    _ = A*(allocationSource s hb cover G B).markedCost := by
      dsimp only [Source.budget,allocationSource,A]
      ring
    _ ≤ A*fullMarkedCost s := mul_le_mul_of_nonneg_left
      (markedCost_le_full (allocationSource s hb cover G B)) hA
    _ = _ := by dsimp only [baseBudget,A];ring

def commonSaving (s : Source ι a b) (G : Id) (α : ℝ) : ℝ :=
  (max 1 (s.L/(prefixNormMax s.d*(G.absNorm:ℝ))))^(-α)

theorem commonSaving_nonneg (s : Source ι a b) (G : Id) (α : ℝ) :
    0≤commonSaving s G α := Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _

/-- The genuine full norm controls each ordinary extracted prefix.
This is an inequality of actual ideals; no radical cap is substituted. -/
theorem allocated_saving_le (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) (α : ℝ) (hα : 0≤α) :
    (allocationSource s hb cover G B).saving α≤commonSaving s G α := by
  let sB := allocationSource s hb cover G B
  have hp : prefixNormMax sB.prefixPair≤prefixNormMax s.d*(G.absNorm:ℝ) := by
    have he := prefix_max_le_product sB.B sB.hB sB.d sB.hd
    rw [sB.hprod] at he
    exact he
  have hquot : s.L/(prefixNormMax s.d*(G.absNorm:ℝ))≤s.L/prefixNormMax sB.prefixPair :=
    div_le_div_of_nonneg_left s.hL.le (prefixNormMax_pos sB.prefixPair sB.prefixPair_nonzero) hp
  exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (le_max_left _ _))
    (max_le_max le_rfl hquot) (neg_nonpos.mpr hα)

/-- Finite allocation count, uniformly in the original dimension.
The two extra coordinates are the actual ordinary factors. -/
theorem uniform_pair_budget (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀(ι : Type u) [Fintype ι],∀a b : ℝ,
      ∀s : Source ι a b,∀hb : 0≤b,∀cover : OriginalEnclosure s,
      Fintype.card ι≤N→∀G₁ G₂ : Id,G₁≠0→G₂≠0→
      ∀(J : ℕ)(control : Finset (ℕ×ℕ))(Z ε α : ℝ),0≤Z→0≤α→
      pairBudget s hb cover G₁ G₂ J control Z ε α≤
        C*(G₁.absNorm:ℝ)^δ*(G₂.absNorm:ℝ)^δ*
          (baseBudget s J control Z ε)^2/((G₁.absNorm:ℝ)*G₂.absNorm)*
          min (commonSaving s G₁ α) (commonSaving s G₂ α) := by
  obtain ⟨K,hK,hcount⟩ := actualAllocations_uniform_small_power (N+2) δ hδ
  refine ⟨K^2,sq_pos_of_pos hK,?_⟩
  intro ι instι a b s hb cover hι G₁ G₂ hG₁ hG₂ J control Z ε α hZ hα
  let A := baseBudget s J control Z ε
  let saving := min (commonSaving s G₁ α) (commonSaving s G₂ α)
  let cost := A^2/((G₁.absNorm:ℝ)*G₂.absNorm)*saving
  have hA : 0≤A := baseBudget_nonneg s J control Z ε hZ
  have hsaving : 0≤saving := le_min (commonSaving_nonneg s G₁ α) (commonSaving_nonneg s G₂ α)
  have hcost : 0≤cost := mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) hsaving
  have hterm (p : actualAllocations (tuplePools s) G₁ × actualAllocations (tuplePools s) G₂) :
      (allocationSource s hb cover G₁ p.1).budget J control Z ε*
        (allocationSource s hb cover G₂ p.2).budget J control Z ε*
        min ((allocationSource s hb cover G₁ p.1).saving α)
          ((allocationSource s hb cover G₂ p.2).saving α)≤cost := by
    have hp := mul_le_mul
      (allocated_budget_le s hb cover G₁ p.1 J control Z ε hZ)
      (allocated_budget_le s hb cover G₂ p.2 J control Z ε hZ)
      ((allocationSource s hb cover G₂ p.2).budget_nonneg J control Z ε hZ)
      (div_nonneg hA (Nat.cast_nonneg _))
    have hs := min_le_min (allocated_saving_le s hb cover G₁ p.1 α hα)
      (allocated_saving_le s hb cover G₂ p.2 α hα)
    have hh := mul_le_mul hp hs
      (le_min ((allocationSource s hb cover G₁ p.1).saving_nonneg α)
        ((allocationSource s hb cover G₂ p.2).saving_nonneg α))
      (mul_nonneg (div_nonneg hA (Nat.cast_nonneg _)) (div_nonneg hA (Nat.cast_nonneg _)))
    apply hh.trans_eq
    dsimp only [cost,A,saving]
    ring
  have hn : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hι 2
  have hc₁ := hcount hn (tuplePools s) G₁ hG₁
  have hc₂ := hcount hn (tuplePools s) G₂ hG₂
  have hc := mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _)
    (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  calc
    _ ≤ ∑p : actualAllocations (tuplePools s) G₁ × actualAllocations (tuplePools s) G₂,cost :=
      Finset.sum_le_sum (fun p _=>hterm p)
    _ = ((actualAllocations (tuplePools s) G₁).card:ℝ)*
        (actualAllocations (tuplePools s) G₂).card*cost := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,
        nsmul_eq_mul,Nat.cast_mul]
    _ ≤ ((K*(G₁.absNorm:ℝ)^δ)*(K*(G₂.absNorm:ℝ)^δ))*cost :=
      mul_le_mul_of_nonneg_right hc hcost
    _ = _ := by dsimp only [cost,A,saving];ring

/-- Numerical conversion only. It works equally when L/U is below one. -/
theorem shortened_power_saving (Z l v L U α : ℝ) (hZ : 1≤Z)
    (hL : 0<L) (hU : 0<U) (hl : Z^l≤L) (hv : U≤Z^v) (hα : 0≤α) :
    (max 1 (L/U))^(-α)≤Z^(-α*max (l-v) 0) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hquot : Z^(l-v)≤L/U := by
    rw [Real.rpow_sub hz]
    exact (div_le_div_of_nonneg_right hl (Real.rpow_nonneg hz.le _)).trans
      (div_le_div_of_nonneg_left hL.le hU hv)
  have hp := Real.rpow_le_rpow_of_nonpos
    (zero_lt_one.trans_le (le_max_left 1 (Z^(l-v))))
    (max_le_max le_rfl hquot) (neg_nonpos.mpr hα)
  exact hp.trans_eq (max_power_saving Z l v α hZ)

/-- This is precisely the paper's positive-part factor, provided its
numeric common-width includes the retained ORIGINAL prefix norm. -/
theorem common_pair_saving_power (s : Source ι a b) (G₁ G₂ : Id)
    (hG₁ : G₁≠0) (hG₂ : G₂≠0) (Z l v α : ℝ) (hZ : 1≤Z) (hα : 0≤α)
    (hl : Z^l≤s.L)
    (hv : prefixNormMax s.d*min (G₁.absNorm:ℝ) (G₂.absNorm:ℝ)≤Z^v) :
    min (commonSaving s G₁ α) (commonSaving s G₂ α)≤Z^(-α*max (l-v) 0) := by
  have hn₁ : 0<(G₁.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG₁)
  have hn₂ : 0<(G₂.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG₂)
  by_cases h : (G₁.absNorm:ℝ)≤G₂.absNorm
  · apply (min_le_left _ _).trans
    exact shortened_power_saving Z l v s.L (prefixNormMax s.d*(G₁.absNorm:ℝ)) α
      hZ s.hL (mul_pos (prefixNormMax_pos s.d s.hd) hn₁) hl
      (by simpa only [min_eq_left h] using hv) hα
  · apply (min_le_right _ _).trans
    exact shortened_power_saving Z l v s.L (prefixNormMax s.d*(G₂.absNorm:ℝ)) α
      hZ s.hL (mul_pos (prefixNormMax_pos s.d s.hd) hn₂) hl
      (by simpa only [min_eq_right (le_of_not_ge h)] using hv) hα

end
end Candidate.FourthPower.MixedPrincipalBudget
