/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Q.2's full closed cutoff grid and finite first-short classification. -/
import Candidate.C092.transport.SharedCutoffZero
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetBank
noncomputable section
open scoped Classical BigOperators
abbrev Offset := Fin 65537

def offset (γ : ℝ) (j : Offset) : ℝ := (j.val:ℝ)*γ/65536
def cutoff (t₀ γ : ℝ) (j : Offset) : ℝ := t₀-offset γ j
def previous (j : Offset) : Offset := ⟨j.val-1,by omega⟩

@[simp] theorem offset_zero (γ : ℝ) : offset γ 0=0 := by simp [offset]
@[simp] theorem offset_last (γ : ℝ) : offset γ ⟨65536,by omega⟩=γ := by norm_num [offset]

theorem offset_bounds (γ : ℝ) (hγ : 0≤γ) (j : Offset) : 0≤offset γ j ∧ offset γ j≤γ := by
  have hj : (j.val:ℝ)≤65536 := by exact_mod_cast (show j.val≤65536 by omega)
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hγ) (by norm_num)
  · dsimp [offset]; nlinarith

theorem cutoff_bounds (t₀ γ : ℝ) (hγ : 0≤γ) (hlo : 1≤t₀-γ) (hhi : t₀≤3/2) (j : Offset) :
    1≤cutoff t₀ γ j ∧ cutoff t₀ γ j≤3/2 := by
  have h:=offset_bounds γ hγ j
  dsimp [cutoff]; constructor <;> linarith

theorem previous_offset (γ : ℝ) (hγ : 0≤γ) (j : Offset) :
    offset γ (previous j)=max 0 (offset γ j-γ/65536) := by
  by_cases hj : j.val=0
  · simp [offset,previous,hj]
    positivity
  · have he : ((j.val-1:ℕ):ℝ)=(j.val:ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
    rw [offset,previous,he]
    have hj1 : (1:ℝ)≤j.val := by exact_mod_cast (show 1≤j.val by omega)
    rw [max_eq_right (by dsimp [offset]; nlinarith [mul_nonneg (sub_nonneg.mpr hj1) hγ])]
    dsimp [offset]; ring

def shortIndices (r : Offset→ℝ) : Finset Offset := Finset.univ.filter (fun j=>r j<1)
def firstShort (r : Offset→ℝ) : Option Offset :=
  if h : (shortIndices r).Nonempty then some ((shortIndices r).min' h) else none

theorem firstShort_none (r : Offset→ℝ) : firstShort r=none ↔ ∀j,1≤r j := by
  unfold firstShort
  split_ifs with h
  · simp only [reduceCtorEq,false_iff]
    obtain ⟨j,hj⟩:=h
    exact fun hall=>not_lt_of_ge (hall j) (Finset.mem_filter.mp hj).2
  · simp only [true_iff]
    intro j
    by_contra hj
    exact h ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hj⟩⟩

theorem firstShort_some (r : Offset→ℝ) (j : Offset) (h : firstShort r=some j) :
    r j<1 ∧ ∀k : Offset,k<j → 1≤r k := by
  unfold firstShort at h
  split_ifs at h with hs
  · have he : (shortIndices r).min' hs=j := Option.some.inj h
    subst j
    refine ⟨(Finset.mem_filter.mp (Finset.min'_mem _ hs)).2,?_⟩
    intro k hk
    by_contra hr
    have hm := Finset.min'_le (shortIndices r) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_not_ge hr⟩)
    exact not_lt_of_ge hm hk

theorem previous_long (r : Offset→ℝ) (j : Offset) (h : firstShort r=some j) (hj : 0<j.val) :
    1≤r (previous j) :=
  (firstShort_some r j h).2 _ (by change j.val-1<j.val;omega)

end
end QRH.Cycle092.MixedOffsetBank
