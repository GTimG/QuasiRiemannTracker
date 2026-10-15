import Candidate.Cycle62.Marked.MarkedHeight
import Candidate.Cycle62.Marked.SlotPolarization

namespace OAI.SevenEighths.Cycle62MarkedHeight
noncomputable section
open scoped Classical BigOperators
open Set

/-- The fixed loss caused by recovering the derivative through common
profile interpolation. It depends only on the number of live slots. -/
def commonProfileCost (N : ℕ) : ℝ :=
  1+(∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1)

lemma commonProfileCost_ge_one (N : ℕ) : 1≤commonProfileCost N := by
  dsimp [commonProfileCost]
  have h : 0≤(∑j : Fin (N+1),‖derivativeWeight N j‖^2)*(N+1) := by positivity
  linarith

/-- Common-height maximization from finitely many common slot profiles.
Taking `B` to be the logarithmic derivative of the original prime slot
allows every row to choose a different height without losing a power of
its norm. The interpolation nodes are fixed independently of the scale. -/
theorem rowwise_common_profile_energy {Row Slot : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (A B : Row→Slot→ℝ→ℂ) (C : Row→ℂ)
    (hA : ∀u∈rows,∀s∈slots,Continuous (A u s))
    (hB : ∀u∈rows,∀s∈slots,Continuous (B u s))
    (hd : ∀u∈rows,∀s∈slots,∀t,HasDerivAt (A u s) (B u s t) t)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (henergy : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,(A u s t+(j.val:ℂ)*B u s t))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,A u s (choice u))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  let F (u : Row) (t : ℝ) := C u*(∏s∈slots,A u s t)
  let F' (u : Row) (t : ℝ) := C u*(∑s∈slots,(∏k∈slots.erase s,A u k t)*B u s t)
  have hc (u : Row) (hu : u∈rows) : Continuous (F u) := by
    exact (continuous_finsetProd slots (fun s hs=>hA u hu s hs)).const_mul _
  have hc' (u : Row) (hu : u∈rows) : Continuous (F' u) := by
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro s hs
    exact (continuous_finsetProd (slots.erase s) (fun k hk=>hA u hu k
      (Finset.mem_of_mem_erase hk))).mul (hB u hu s hs)
  have hderiv (u : Row) (hu : u∈rows) (t : ℝ) : HasDerivAt (F u) (F' u t) t := by
    have hh := (HasDerivAt.finsetProd (fun s hs=>hd u hu s hs t)).const_mul (C u)
    simpa only [F,F',Finset.prod_apply,smul_eq_mul] using hh
  have hk : 0≤commonProfileCost N := zero_le_one.trans (commonProfileCost_ge_one N)
  have h0 (t : ℝ) (ht : t∈Icc a b) : ∑u∈rows,‖F u t‖^2≤commonProfileCost N*E := by
    have he := henergy (0 : Fin (N+1)) t ht
    simp only [Fin.val_zero,Nat.cast_zero,zero_mul,add_zero] at he
    exact he.trans (le_mul_of_one_le_left hE (commonProfileCost_ge_one N))
  have h1 (t : ℝ) (ht : t∈Icc a b) : ∑u∈rows,‖F' u t‖^2≤commonProfileCost N*E := by
    have he := polarized_product_energy rows slots N hN (fun u s=>A u s t)
      (fun u s=>B u s t) C E (fun j=>henergy j t ht)
    apply he.trans
    apply mul_le_mul_of_nonneg_right _ hE
    dsimp only [commonProfileCost]
    linarith
  have he := rowwise_energy rows F F' hc hc' hderiv a b (commonProfileCost N*E)
    hab choice hchoice h0 h1
  simpa only [F,mul_assoc] using he

end
end OAI.SevenEighths.Cycle62MarkedHeight
#print axioms OAI.SevenEighths.Cycle62MarkedHeight.rowwise_common_profile_energy
