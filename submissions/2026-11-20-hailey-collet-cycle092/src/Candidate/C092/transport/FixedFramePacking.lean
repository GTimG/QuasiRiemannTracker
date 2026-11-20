/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed H.15--H.17 summation on the actual packed lattice of the grouped frame. -/
import Candidate.C092.transport.FixedPackedRows
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedFrame

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CenteredExceptionalProfile
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
namespace QRH.Cycle092.FixedFramePacking
local notation "O" => HeckeFamily.O
variable {L mesh Z : ℝ} {θ : GData L}

/-- Reindex each label on its actual multiplier V₀·twist, and sum its native
weight by the existing admissible divisor fibre estimate. -/
theorem packed_fibre_sum (r : GSrc θ mesh Z) (η : Character)
    (S : Finset (GLabel θ mesh Z)) (fit : ∀ x∈S, Fits η r x)
    (rows : GLabel θ mesh Z → Finset O) (B R : ℝ) (hB : 0 ≤ B)
    (hfib : ∀ y : O,y ≠ 0 → ((Ideal.span {y}).absNorm:ℝ) ≤ R →
      ∑ x∈S.filter (fun x=>x.twist ∣ y),gWeight x ≤ B)
    (nzero : ∀ x∈S,∀ z∈rows x,z ≠ 0)
    (cap : ∀ x∈S,∀ z∈rows x,((Ideal.span {(r.V₀*x.twist)*z}).absNorm:ℝ) ≤ R) :
    let Y := S.biUnion (fun x=>(rows x).image ((r.V₀*x.twist)* ·))
    ∑ x∈S,gWeight x*((rows x).card:ℝ) ≤ B*(Y.card:ℝ) := by
  classical
  intro Y
  let P := fun x:GLabel θ mesh Z=>(rows x).image ((r.V₀*x.twist)* ·)
  have hz (y) (hy:y∈Y) : y≠0 ∧ ((Ideal.span {y}).absNorm:ℝ)≤R := by
    obtain ⟨x,hx,hp⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨mul_ne_zero (mul_ne_zero r.hV₀ (fit x hx).twist_ne) (nzero x hx z hz),cap x hx z hz⟩
  calc
    _ = ∑ x∈S,∑ y∈Y,if y∈P x then gWeight x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter]
      have hfilter : Y.filter (· ∈ P x) = P x := by
        ext y
        exact ⟨fun h=>(Finset.mem_filter.mp h).2,fun h=>Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨x,hx,h⟩,h⟩⟩
      have hcard : (P x).card = (rows x).card :=
        Finset.card_image_of_injective _ (mul_right_injective₀ (mul_ne_zero r.hV₀ (fit x hx).twist_ne))
      rw [hfilter,Finset.sum_const,hcard,nsmul_eq_mul,mul_comm]
    _ = ∑ y∈Y,∑ x∈S,if y∈P x then gWeight x else 0 := Finset.sum_comm
    _ ≤ ∑ _y∈Y,B := by
      apply Finset.sum_le_sum
      intro y hy
      rw [←Finset.sum_filter]
      apply le_trans _ (fibre_packed r S gWeight gWeight_nonneg B R hB hfib y (hz y hy).1 (hz y hy).2)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨hs,hp⟩ := Finset.mem_filter.mp hx
        obtain ⟨z,_,he⟩ := Finset.mem_image.mp hp
        exact Finset.mem_filter.mpr ⟨hs,z,he.symm⟩
      · exact fun x _ _=>gWeight_nonneg x
    _ = _ := by simp [mul_comm]

/-- The original fixed classifier transports along the same packing map as
the norm bound. In a single anchor class this leaves the true sixth-power
exceptional count in the one common ball. -/
theorem fixed_anchor_count (r : GSrc θ mesh Z) (η : Character) (Q : Ideal O)
    (hQ₀ : Q ≠ 0) (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m : O) (hm : m ≠ 0) (hlam : goodLambda ∣ m) (ht : (2:O) ∣ m)
    (S : Finset (GLabel θ mesh Z)) (fit : ∀ x∈S, Fits η r x)
    (j : DictIdx) (hj : ∀ x∈S,x.anchor r=j) (rows : GLabel θ mesh Z → Finset O)
    (num : ∀ x∈S,∀ z∈rows x,z≠0 ∧ FixedInducingRow (x.char r) Q m 1 z)
    (M : ℝ) (cap : ∀ x∈S,∀ z∈rows x,((Ideal.span {(r.V₀*x.twist)*z}).absNorm:ℝ) ≤ Z^M) :
    let Y := S.biUnion (fun x=>(rows x).image ((r.V₀*x.twist)* ·))
    (Y.card:ℝ) ≤ (768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*Z^(M/6) := by
  classical
  intro Y
  have h (y : O) (hy:y∈Y) : y≠0 ∧ FixedInducingRow (anchors η j) Q m 1 y ∧
      ((Ideal.span {y}).absNorm:ℝ)≤Z^M := by
    obtain ⟨x,hx,hp⟩:=Finset.mem_biUnion.mp hy
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hp
    have hfit:=fit x hx
    have hnum:=num x hx z hz
    have hn:=mul_ne_zero r.hV₀ hfit.twist_ne
    refine ⟨mul_ne_zero hn hnum.1,?_,cap x hx z hz⟩
    rw [←hj x hx]
    exact (fixedInducingRow_transfer _ _ Q m _ _ z hm hlam ht hfit.mask_ne hn hnum.1 hfit.coef).mp hnum.2
  have hc := fixed_support_exceptional_count (anchors η j) Q hQ₀ hQt hQ72 m 1 hm one_ne_zero
    hlam ht Y (fun y hy=>(h y hy).1) (fun y hy=>(h y hy).2.1) 1
    squarefree_one (by rw [UniqueFactorizationMonoid.normalizedFactors_one]; simp) Z 1 M 0
    (zero_lt_one.trans r.hZ) zero_le_one (by simp) (fun y hy=>by simpa using (h y hy).2.2)
  simpa using hc

#print axioms packed_fibre_sum
#print axioms fixed_anchor_count
end QRH.Cycle092.FixedFramePacking
