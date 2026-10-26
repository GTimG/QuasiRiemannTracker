/- Copyright (c) 2026 Sil. Apache-2.0.
Lossless embedding of the actual columns into repeated-part/radical blocks.
The coefficient support is retained by zero extension; arbitrary free pairs
are not substituted for the canonical pairs of the original ideal family.
-/
import Candidate.FourthPower.SieveDualGeometry

set_option autoImplicit false
namespace Candidate.FourthPower.SieveColumnGeometry
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open SieveCoupling SexticSieve FiniteSieveRestriction
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem canonical_pair_injective (I J : Id) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs : sharp I = sharp J) (hr : I.radical = J.radical) : I = J := by
  rw [← normal_form I hI,← normal_form J hJ,hs,hr]

theorem coprime_radicals_iff (I J : Id) : IsCoprime I.radical J.radical ↔ IsCoprime I J := by
  constructor
  · intro h
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.radical_eq_top.mp
    rw [Ideal.radical_sup,h.sup_eq,Ideal.radical_top]
  · exact radical_coprime I J

theorem radical_geometry (I : Id) (hI : Supported I) (hf : PowerFree 6 I)
    (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    Supported I.radical ∧ PowerFree 6 I.radical ∧ (Ideal.absNorm I.radical : ℝ) ≤ N := by
  have hd : I.radical ∣ I := Ideal.dvd_iff_le.mpr I.le_radical
  exact ⟨radical_supported I hI,SieveInitial.powerFree_dvd hf hd,
    (CenteredExceptionalCount.norm_le_of_dvd hI.1 hd).trans hN⟩

theorem sharp_geometry (I : Id) (hI : Supported I) (N : ℝ)
    (hN : (Ideal.absNorm I : ℝ) ≤ N) : Supported (sharp I) ∧ (Ideal.absNorm (sharp I) : ℝ) ≤ N := by
  have hd : sharp I ∣ I := ⟨I.radical,by rw [mul_comm,normal_form I hI.1]⟩
  exact ⟨sharp_supported I hI,(CenteredExceptionalCount.norm_le_of_dvd hI.1 hd).trans hN⟩

def embedding {n : Type*} (cols : n → Id) (Us Rs : Finset Id)
    (hU : ∀ i, sharp (cols i) ∈ Us) (hR : ∀ i, (cols i).radical ∈ Rs) : n → ↥Us × ↥Rs :=
  fun i => (⟨sharp (cols i),hU i⟩,⟨(cols i).radical,hR i⟩)

theorem embedding_injective {n : Type*} (cols : n → Id) (hinj : Function.Injective cols)
    (hc : ∀ i, Supported (cols i)) (Us Rs : Finset Id)
    (hU : ∀ i, sharp (cols i) ∈ Us) (hR : ∀ i, (cols i).radical ∈ Rs) :
    Function.Injective (embedding cols Us Rs hU hR) := by
  intro i j he
  apply hinj
  exact canonical_pair_injective (cols i) (cols j) (hc i).1 (hc j).1
    (congrArg (fun p : ↥Us × ↥Rs => p.1.val) he)
    (congrArg (fun p : ↥Us × ↥Rs => p.2.val) he)

def coefficients {n : Type*} [Fintype n] (cols : n → Id) (Us Rs : Finset Id)
    (hU : ∀ i, sharp (cols i) ∈ Us) (hR : ∀ i, (cols i).radical ∈ Rs)
    (a : n → ℂ) : ↥Us × ↥Rs → ℂ := extendByZero Finset.univ (embedding cols Us Rs hU hR) a

theorem coefficients_mass {n : Type*} [Fintype n] (cols : n → Id) (hinj : Function.Injective cols)
    (hc : ∀ i, Supported (cols i)) (Us Rs : Finset Id)
    (hU : ∀ i, sharp (cols i) ∈ Us) (hR : ∀ i, (cols i).radical ∈ Rs) (a : n → ℂ) :
    (∑ p, ‖coefficients cols Us Rs hU hR a p‖^2) = ∑ i, ‖a i‖^2 := by
  exact extendByZero_energy Finset.univ (embedding cols Us Rs hU hR) a
    (embedding_injective cols hinj hc Us Rs hU hR).injOn

theorem sum_extend {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq p]
    (f : n → p) (a : n → ℂ) (F : p → ℂ) :
    (∑ k, extendByZero Finset.univ f a k*F k) = ∑ i, a i*F (f i) := by
  simpa only [mul_comm] using extendByZero_matrix Finset.univ f a (fun (_ : Unit) k => F k) ()

theorem sum_extend_star {n p : Type*} [Fintype n] [Fintype p]
    [DecidableEq p]
    (f : n → p) (a : n → ℂ) (F : p → ℂ) :
    (∑ k, star (extendByZero Finset.univ f a k)*F k) = ∑ i, star (a i)*F (f i) := by
  have hs := congrArg star (sum_extend f a (fun k => star (F k)))
  simpa only [star_sum,star_mul,star_star,mul_comm] using hs

theorem pair_extend {n m p q : Type*} [Fintype n] [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q]
    (f : n → p) (g : m → q) (a : n → ℂ) (b : m → ℂ) (F : p → q → ℂ) :
    (∑ r, ∑ s, star (extendByZero Finset.univ f a r)*extendByZero Finset.univ g b s*F r s) =
      ∑ i, ∑ j, star (a i)*b j*F (f i) (g j) := by
  simp only [mul_assoc,← Finset.mul_sum]
  rw [sum_extend_star]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_extend]

/-- Both vectors are reindexed exactly. Zero extension preserves the
canonical compatibility of the repeated part and radical. -/
theorem coefficients_pair {n m : Type*} [Fintype n] [Fintype m]
    (cols : n → Id) (cols' : m → Id) (Us Vs Rs Ts : Finset Id)
    (hU : ∀ i, sharp (cols i) ∈ Us) (hR : ∀ i, (cols i).radical ∈ Rs)
    (hV : ∀ j, sharp (cols' j) ∈ Vs) (hT : ∀ j, (cols' j).radical ∈ Ts)
    (a : n → ℂ) (b : m → ℂ) (F : Id → Id → Id → Id → ℂ) :
    (∑ p : ↥Us × ↥Rs, ∑ q : ↥Vs × ↥Ts,
      star (coefficients cols Us Rs hU hR a p)*coefficients cols' Vs Ts hV hT b q*
        F p.1.val q.1.val p.2.val q.2.val) =
      ∑ i, ∑ j, star (a i)*b j*F (sharp (cols i)) (sharp (cols' j)) (cols i).radical (cols' j).radical := by
  simpa only [coefficients,embedding] using
    pair_extend (embedding cols Us Rs hU hR) (embedding cols' Vs Ts hV hT) a b
      (fun p q => F p.1.val q.1.val p.2.val q.2.val)

theorem block_order {U V R T : Type*} [Fintype U] [Fintype V] [Fintype R] [Fintype T]
    (F : U × R → V × T → ℂ) :
    (∑ p, ∑ q, F p q) = ∑ u, ∑ v, ∑ r, ∑ s, F (u,r) (v,s) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

theorem blocks_triangle {U V R T K : Type*} [Fintype U] [Fintype V] [Fintype R]
    [Fintype T] [Fintype K] (F : K → U × R → V × T → ℂ) :
    (∑ k, ‖∑ p, ∑ q, F k p q‖) ≤ ∑ u, ∑ v, ∑ k, ‖∑ r, ∑ s, F k (u,r) (v,s)‖ := by
  have hk (k : K) : ‖∑ p, ∑ q, F k p q‖ ≤ ∑ u, ∑ v, ‖∑ r, ∑ s, F k (u,r) (v,s)‖ := by
    rw [block_order]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro u _
    exact norm_sum_le _ _
  calc
    _ ≤ ∑ k, ∑ u, ∑ v, ‖∑ r, ∑ s, F k (u,r) (v,s)‖ := Finset.sum_le_sum (fun k _ => hk k)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]

end
end Candidate.FourthPower.SieveColumnGeometry
