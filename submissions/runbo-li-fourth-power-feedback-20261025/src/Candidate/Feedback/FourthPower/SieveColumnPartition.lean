/- Copyright (c) 2026 Sil. Apache-2.0.
Place every actual sixth-power-free column in a controlled geometric box.
Only the radical length and the uniformly finite Gauss label are partitioned.
-/
import Candidate.Feedback.FourthPower.SieveBoxFamily

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.SieveColumnPartition
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open SexticSieve SieveCoupling SieveOperator SieveColumnGeometry SieveBoxFamily
local notation "Id" => Ideal ActualEisensteinCubic.O

abbrev Label (N : ℝ) := SieveRayCoupling.Label × Fin (columnDyadicLength N+1)

def label {n : Type*} (N : ℝ) (cols : n → Id) (hc : ∀ i, Supported (cols i)) (i : n) : Label N :=
  (SieveRayCoupling.label (cols i) (hc i),divisorDyadicLabel N (cols i).radical)

abbrev Fiber {n : Type*} (N : ℝ) (cols : n → Id) (hc : ∀ i, Supported (cols i)) (l : Label N) :=
  {i : n // label N cols hc i = l}

def scale {N : ℝ} (l : Label N) : ℝ := divisorDyadicScale l.2.val

theorem scale_pos {N : ℝ} (l : Label N) : 0 < scale l :=
  zero_lt_one.trans_le (divisorDyadicScale_ge_one l.2.val)

theorem fiber_radical_bounds {n : Type*} (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
    (l : Label N) (i : Fiber N cols hc l) :
    scale l ≤ (Ideal.absNorm (cols i.val).radical : ℝ) ∧
      (Ideal.absNorm (cols i.val).radical : ℝ) ≤ 2*scale l := by
  have hs := radical_supported (cols i.val) (hc i.val)
  have hd : (cols i.val).radical ∣ cols i.val := Ideal.dvd_iff_le.mpr (cols i.val).le_radical
  have hlo := CenteredExceptionalCount.norm_one_le hs.1
  have hhi := (CenteredExceptionalCount.norm_le_of_dvd (hc i.val).1 hd).trans (hn i.val)
  have hb := divisorDyadicLabel_bounds N (cols i.val).radical hlo hhi
  have he : divisorDyadicLabel N (cols i.val).radical = l.2 := congrArg Prod.snd i.property
  rw [he] at hb
  refine ⟨max_le hlo hb.1.le,?_⟩
  have hm : (2 : ℝ)^l.2.val/2 ≤ scale l := le_max_right _ _
  linarith [hb.2]

theorem fiber_sharp_bound {n : Type*} (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N)
    (l : Label N) (i : Fiber N cols hc l) :
    (Ideal.absNorm (sharp (cols i.val)) : ℝ) ≤ N/scale l := by
  apply (le_div_iff₀ (scale_pos l)).mpr
  calc
    _ ≤ (Ideal.absNorm (sharp (cols i.val)) : ℝ)*(Ideal.absNorm (cols i.val).radical : ℝ) :=
      mul_le_mul_of_nonneg_left (fiber_radical_bounds N cols hc hn l i).1 (by positivity)
    _ = (Ideal.absNorm (cols i.val) : ℝ) := by rw [mul_comm,norm_normal_form _ (hc i.val).1]
    _ ≤ N := hn i.val

def box {n : Type*} [Fintype n] (N : ℝ) (hN : 0 ≤ N) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N) (l : Label N) : ColumnBox where
  repeated := Finset.univ.image (fun i : Fiber N cols hc l => sharp (cols i.val))
  radical := Finset.univ.image (fun i : Fiber N cols hc l => (cols i.val).radical)
  scale := scale l
  upper := N/scale l
  scale_pos := scale_pos l
  upper_nonneg := div_nonneg hN (scale_pos l).le
  residue := l.1.2.2
  repeated_good := by
    intro U hU
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hU
    exact sharp_supported _ (hc i.val)
  repeated_le := by
    intro U hU
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hU
    exact fiber_sharp_bound N cols hc hn l i
  radical_good := by
    intro R hR
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
    exact ⟨radical_supported _ (hc i.val),SieveInitial.powerFree_dvd (hf i.val)
      (Ideal.dvd_iff_le.mpr (cols i.val).le_radical)⟩
  radical_bounds := by
    intro R hR
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
    exact fiber_radical_bounds N cols hc hn l i
  radical_ray := by
    intro R hR
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hR
    exact congrArg (fun p : Label N => p.1.2.2) i.property

def location {n : Type*} [Fintype n] (N : ℝ) (hN : 0 ≤ N) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (hf : ∀ i, PowerFree 6 (cols i))
    (hi : Function.Injective cols) (hn : ∀ i, (Ideal.absNorm (cols i) : ℝ) ≤ N) (l : Label N) :
    Location (box N hN cols hc hf hn l) (fun i : Fiber N cols hc l => cols i.val) where
  supported i := hc i.val
  free i := hf i.val
  injective := fun i j he => Subtype.ext (hi he)
  repeated_mem i := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  radical_mem i := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  label := l.1
  labels i := congrArg Prod.fst i.property

theorem labels_card (N : ℝ) : Fintype.card (Label N) = 576*(columnDyadicLength N+1) := by
  change Fintype.card (SieveRayCoupling.Label × Fin (columnDyadicLength N+1)) = _
  rw [Fintype.card_prod,SieveRayCoupling.labels_finite,Fintype.card_fin]

theorem labels_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → (Fintype.card (Label N) : ℝ) ≤ C*N^ε := by
  let C : ℝ := 576*(2+1/(ε*Real.log 2))
  have hc : 0 < C := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [C]
    positivity
  refine ⟨C,hc,?_⟩
  intro N hN
  have hb := mul_le_mul_of_nonneg_left (columnDyadicLength_small_power ε hε N hN) (by norm_num : (0 : ℝ) ≤ 576)
  simpa only [labels_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,C,mul_assoc] using hb

theorem fiber_masses {n : Type*} [Fintype n] (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (a : n → ℂ) :
    (∑ l : Label N, ∑ i : Fiber N cols hc l, ‖a i.val‖^2) = ∑ i, ‖a i‖^2 :=
  Fintype.sum_fiberwise (label N cols hc) (fun i => ‖a i‖^2)

theorem fiber_mass_le {n : Type*} [Fintype n] (N : ℝ) (cols : n → Id)
    (hc : ∀ i, Supported (cols i)) (a : n → ℂ) (l : Label N) :
    (∑ i : Fiber N cols hc l, ‖a i.val‖^2) ≤ ∑ i, ‖a i‖^2 := by
  rw [← fiber_masses N cols hc a]
  have hn (k : Label N) : 0 ≤ ∑ i : Fiber N cols hc k, ‖a i.val‖^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg ‖a i.val‖)
  exact Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ l)

end
end Candidate.Feedback.FourthPower.SieveColumnPartition
