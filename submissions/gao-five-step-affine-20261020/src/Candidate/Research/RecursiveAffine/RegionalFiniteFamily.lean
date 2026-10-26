/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalRoundedPosition

set_option autoImplicit false
namespace Cycle153
noncomputable section

abbrev GridCoordinates (N : ℕ) : Type :=
  Fin (N+1) × Fin (N+1) × Fin (N+1) × Fin (N+1)

def gridPosition (N : ℕ) (i : GridCoordinates N) : RegionalPosition where
  B := (i.1:ℝ)/N
  slotTop := (i.2.1:ℝ)/N
  mesh := 1/N
  windowBottom := (i.2.2.1:ℝ)/N
  sumBottom := (i.2.2.2:ℝ)/N
  plainLossCap := max 0 (max (1/4-(i.2.2.1:ℝ)/N)
    (1/4-((i.2.2.2:ℝ)/N-(9/2)*((i.2.1:ℝ)/N)-1/100)/2))

def RegionalIndex (S : RegionalStage) (N : ℕ) : Type :=
  {i : GridCoordinates N // (gridPosition N i).Facts S}

instance (S : RegionalStage) (N : ℕ) : Finite (RegionalIndex S N) := Subtype.finite

@[instance_reducible]
def regionalFamily (S : RegionalStage) (N : ℕ) (i : RegionalIndex S N) : Cycle63.AffineLedger :=
  regionalLedger S (gridPosition N i.1) i.2

theorem roundUp_eq_coordinate {N : ℕ} {x : ℝ} (hx : 0≤x) :
    roundUp (1/N) x=((⌈x*N⌉).toNat:ℝ)/N := by
  have hc : 0≤⌈x*N⌉ := Int.ceil_nonneg (mul_nonneg hx (Nat.cast_nonneg N))
  unfold roundUp
  rw [div_div_eq_mul_div, div_one, mul_one_div]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hc).symm

theorem roundDown_eq_coordinate {N : ℕ} {x : ℝ} (hx : 0≤x) :
    roundDown (1/N) x=((⌊x*N⌋).toNat:ℝ)/N := by
  have hc : 0≤⌊x*N⌋ := Int.floor_nonneg.mpr (mul_nonneg hx (Nat.cast_nonneg N))
  unfold roundDown
  rw [div_div_eq_mul_div, div_one, mul_one_div]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hc).symm

theorem coordinate_le {N : ℕ} {x : ℝ} (hx : x≤1) :
    (⌈x*N⌉).toNat≤N ∧ (⌊x*N⌋).toNat≤N := by
  have h : ⌈x*N⌉≤N := Int.ceil_le.mpr (by
    push_cast
    exact mul_le_of_le_one_left (Nat.cast_nonneg N) hx)
  have h' : ⌊x*N⌋≤N := (Int.floor_le_ceil _).trans h
  omega

/-- The same finite grid covers fixed regional planes and terminal
planes through a moving actual child. Its size is independent of Z. -/
theorem exists_gridPosition {S : RegionalStage} {N : ℕ} {B n₁ n₂ z : ℝ}
    (hN : 0<N) (hz : 0≤z) (hB0 : 0≤B)
    (hplane : n₁+n₂+S.lam*z≤B)
    (h : (roundedPosition (1/N) B n₁ n₂ z).Facts S) :
    ∃i : GridCoordinates N, gridPosition N i=roundedPosition (1/N) B n₁ n₂ z := by
  have hg : (0:ℝ)<1/N := by
    have : (0:ℝ)<N := by exact_mod_cast hN
    positivity
  have hm : 0<min n₁ n₂ := lt_of_lt_of_le h.windowBottom_pos (roundDown_bounds hg _).2
  have hn₁ : 0<n₁ := hm.trans_le (min_le_left _ _)
  have hn₂ : 0<n₂ := hm.trans_le (min_le_right _ _)
  have hB : B≤1 := (roundUp_bounds hg _).1.trans h.B_le_one
  have hzz : z≤1 := (roundUp_bounds hg _).1.trans h.slotTop_le_one
  have hprod : 0≤S.lam*z := mul_nonneg (by linarith [S.one_le_lam]) hz
  have hs0 : 0≤n₁+n₂ := by linarith
  have hs : n₁+n₂≤1 := by linarith
  have hmm : min n₁ n₂≤1 := (min_le_left _ _).trans (by linarith)
  refine ⟨(⟨_,Nat.lt_succ_of_le (coordinate_le hB).1⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hzz).1⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hmm).2⟩,
    ⟨_,Nat.lt_succ_of_le (coordinate_le hs).2⟩),?_⟩
  simp only [gridPosition, roundedPosition, roundUp_eq_coordinate hB0,
    roundUp_eq_coordinate hz, roundDown_eq_coordinate hm.le, roundDown_eq_coordinate hs0]

theorem regionalLedger_congr (S : RegionalStage) {P P' : RegionalPosition}
    (heq : P=P') (h : P.Facts S) (h' : P'.Facts S) :
    regionalLedger S P h=regionalLedger S P' h' := by
  subst heq
  rfl

theorem roundedLedger_mem_family {S : RegionalStage} {N : ℕ} {B n₁ n₂ z : ℝ}
    (hN : 0<N) (hz : 0≤z) (hB0 : 0≤B)
    (hplane : n₁+n₂+S.lam*z≤B)
    (h : (roundedPosition (1/N) B n₁ n₂ z).Facts S) :
    ∃i : RegionalIndex S N,
      regionalFamily S N i=regionalLedger S (roundedPosition (1/N) B n₁ n₂ z) h := by
  obtain ⟨i,hi⟩ := exists_gridPosition hN hz hB0 hplane h
  refine ⟨⟨i,hi ▸ h⟩,?_⟩
  exact regionalLedger_congr S hi _ _

/-- Only a finite intersection of eventual thresholds is used. A new
threshold depending on every moving real source is never assumed. -/
theorem uniform_regional_threshold (S : RegionalStage) (N : ℕ)
    (P : RegionalIndex S N→ℝ→Prop)
    (h : ∀i, ∀ᶠ Z : ℝ in Filter.atTop, P i Z) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀i, P i Z := by
  exact Filter.eventually_all.2 h

end
end Cycle153

#print axioms Cycle153.roundedLedger_mem_family
#print axioms Cycle153.uniform_regional_threshold
