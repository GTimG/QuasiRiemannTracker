/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual extraction weights cancel H.15 before the common fixed-row count.
The constant counts anchor characters, independently of labels and rows. -/
import Candidate.C092.transport.FixedFramePacking
set_option autoImplicit false

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
namespace QRH.Cycle092.FixedFramePacking
local notation "O" => HeckeFamily.O
variable {L mesh Z : ℝ} {θ : GData L}

def prefixNorm (x : GLabel θ mesh Z) : ℝ :=
  (x.G.absNorm:ℝ)*x.D.absNorm*((x.d.1.absNorm:ℝ)*x.d.2.absNorm)

/-- H.17 for all labels and all dictionary anchors on the source. The
per-row input is the unnormalized H.15, including the genuine second
artificial divisor. Its reciprocal survives in gWeight's fibre sum. -/
theorem native_fixed_price (r : GSrc θ mesh Z) (η : Character) (Q : Ideal O)
    (hQ₀ : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m : O) (hm : m ≠ 0) (hlam : goodLambda ∣ m) (ht : (2:O) ∣ m)
    (labels : Finset (GLabel θ mesh Z)) (fit : ∀ x∈labels,Fits η r x)
    (rows : GLabel θ mesh Z → Finset O) (energy : GLabel θ mesh Z → O → ℝ)
    (A B M Lf : ℝ) (hA : 0≤A) (hB : 0≤B)
    (hfib : ∀ y:O,y≠0 → ((Ideal.span {y}).absNorm:ℝ) ≤ Z^M →
      ∑ x∈labels.filter (fun x=>x.twist ∣ y),gWeight x ≤ B)
    (num : ∀ x∈labels,∀ z∈rows x,z≠0 ∧ FixedInducingRow (x.char r) Q m 1 z)
    (cap : ∀ x∈labels,∀ z∈rows x,((Ideal.span {(r.V₀*x.twist)*z}).absNorm:ℝ) ≤ Z^M)
    (h15 : ∀ x∈labels,∀ z∈rows x,
      energy x z ≤ A*r.vol^2/(prefixNorm x*max 1 Lf)) :
    ∑ x∈labels,gWeight x*(prefixNorm x*r.norm*(∑ z∈rows x,energy x z)) ≤
      (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*
        A*B*Z^(r.kLog+M/6)/max 1 Lf := by
  classical
  let K : ℝ := 768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card
  let fee : ℝ := A*Z^r.kLog/max 1 Lf
  have hZ := zero_lt_one.trans r.hZ
  have hvol := r.vol_pos hZ
  have hmin : 0 < max 1 Lf := zero_lt_one.trans_le (le_max_left _ _)
  have hfee : 0 ≤ fee := div_nonneg (mul_nonneg hA (Real.rpow_nonneg hZ.le _)) hmin.le
  have hnorm : 0 ≤ r.norm := div_nonneg (Real.rpow_nonneg hZ.le _) (sq_nonneg _)
  have hp (x) (hx:x∈labels) : 0<prefixNorm x := by
    have hi (I:Ideal O) (h:I≠0) : 0<(I.absNorm:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h)
    have f:=fit x hx
    exact mul_pos (mul_pos (hi _ f.G_ne) (hi _ (Squarefree.ne_zero f.D_sq))) (mul_pos (hi _ f.d₁) (hi _ f.d₂))
  have henergy (x) (hx:x∈labels) :
      prefixNorm x*r.norm*(∑ z∈rows x,energy x z) ≤ fee*((rows x).card:ℝ) := by
    calc
      _ ≤ prefixNorm x*r.norm*(∑ _z∈rows x,A*r.vol^2/(prefixNorm x*max 1 Lf)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (h15 x hx)) (mul_nonneg (hp x hx).le hnorm)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,GSrc.norm,fee]; field_simp [hvol.ne', (hp x hx).ne',hmin.ne']
  have hmass (j:DictIdx) :
      ∑ x∈labels.filter (fun x=>x.anchor r=j),gWeight x*((rows x).card:ℝ) ≤ B*(K*Z^(M/6)) := by
    let S := labels.filter (fun x=>x.anchor r=j)
    have sub : S ⊆ labels := Finset.filter_subset _ _
    have H := packed_fibre_sum r η S (fun x hx=>fit x (sub hx)) rows B (Z^M) hB
      (fun y hy hR=>le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset_filter _ sub) (fun x _ _=>gWeight_nonneg x)) (hfib y hy hR))
      (fun x hx z hz=>(num x (sub hx) z hz).1) (fun x hx=>cap x (sub hx))
    exact H.trans (mul_le_mul_of_nonneg_left (fixed_anchor_count r η Q hQ₀ hQt hQ72 m hm hlam ht
      S (fun x hx=>fit x (sub hx)) j (fun _ hx=>(Finset.mem_filter.mp hx).2) rows
      (fun x hx=>num x (sub hx)) M (fun x hx=>cap x (sub hx))) hB)
  calc
    _ ≤ ∑ x∈labels,fee*(gWeight x*((rows x).card:ℝ)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (mul_le_mul_of_nonneg_left (henergy x hx) (gWeight_nonneg x)).trans_eq (by ring)
    _ = fee*∑ j:DictIdx,∑ x∈labels.filter (fun x=>x.anchor r=j),gWeight x*((rows x).card:ℝ) := by
      rw [←Finset.mul_sum,Finset.sum_fiberwise]
    _ ≤ fee*∑ _j:DictIdx,B*(K*Z^(M/6)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _=>hmass j)) hfee
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,fee,K,Real.rpow_add hZ]; ring

#print axioms native_fixed_price
end QRH.Cycle092.FixedFramePacking
