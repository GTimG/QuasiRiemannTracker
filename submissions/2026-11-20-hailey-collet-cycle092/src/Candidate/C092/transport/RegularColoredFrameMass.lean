/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Actual native extracted label weights at the original packed row.
The native labelMass_extracted bound and original weighted divisor fibre
are charged once, with no label cardinality factor.
-/
import Candidate.C092.transport.RegularColoredFrameNative
import Submissions.sil_density_split_20261026.CubeFree.Packet.GroupedAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O
variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

def frameExtractionWeight (Cred ε δ : ℝ) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : ℝ :=
  gWeight x * ((x.G.absNorm:ℝ)*(x.D.absNorm:ℝ)*pairNorm x.d*
    labelMass Cred Z ε δ r.w r.X₁ r.X₂ x.G x.D x.d)

theorem frameExtractionWeight_nonneg (Cred ε δ : ℝ) (hCred : 0≤Cred)
    (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) : 0≤frameExtractionWeight Cred ε δ r x := by
  unfold frameExtractionWeight labelMass
  have hZ := r.hZ.le
  have hw := gWeight_nonneg x
  have hX₁ := r.hX₁
  have hX₂ := r.hX₂
  have hp : 0≤pairNorm x.d := by unfold pairNorm; positivity
  have hGδ := Real.rpow_nonneg (Nat.cast_nonneg x.G.absNorm) δ
  have hDδ := Real.rpow_nonneg (Nat.cast_nonneg x.D.absNorm) δ
  have hZε := Real.rpow_nonneg (zero_le_one.trans hZ) ε
  have hprod : 0≤∏i,Z^(r.w i) := Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (zero_le_one.trans hZ) _)
  positivity

theorem frameExtractionWeight_le (Cred ε δ : ℝ) (hCred : 0≤Cred) (hδ : 0≤δ)
    (η : Character) (r : GSrc θ mesh Z) (x : GLabel θ mesh Z) (hf : Fits η r x) :
    frameExtractionWeight Cred ε δ r x ≤ gWeight x*(Cred*Z^(ε+3*δ*θ.Bmask)*r.vol) := by
  have he := QRH.SilDensitySplit.CubeFree.Second.Concrete.labelMass_extracted Cred Z ε δ
    θ.Bmask hCred r.hZ.le hδ r.w r.X₁ r.X₂ r.hX₁ r.hX₂ x.G x.D hf.G_ne hf.D_sq.ne_zero (⊤,⊤)
    (top_ne_bot : (⊤ : Ideal O)≠⊥) (top_ne_bot : (⊤ : Ideal O)≠⊥) hf.G_cap hf.D_cap
  rw [←labelMass_pair Cred Z ε δ r.w r.X₁ r.X₂ x.G x.D x.d hf.d₁ hf.d₂,←mul_assoc] at he
  exact mul_le_mul_of_nonneg_left he (gWeight_nonneg x)

/-- The actual native weighted fibre, on the original label set. The same
labels and original sublattice divisibility remain in the conclusion. -/
theorem frameExtractionWeight_fibre (Cred ε δ D : ℝ) (hCred : 0≤Cred) (hδ : 0≤δ)
    (η : Character) (r : GSrc θ mesh Z) (labels : Finset (GLabel θ mesh Z))
    (hfit : ∀x∈labels,Fits η r x) (y : O)
    (hfibre : ∑x∈labels.filter (fun x=>x.twist∣y),gWeight x≤D) :
    ∑x∈labels.filter (fun x=>r.V₀*x.twist∣y),frameExtractionWeight Cred ε δ r x ≤
      Cred*Z^(ε+3*δ*θ.Bmask)*r.vol*D := by
  let A := Cred*Z^(ε+3*δ*θ.Bmask)*r.vol
  have hA : 0≤A := by
    dsimp only [A]
    exact mul_nonneg (mul_nonneg hCred (Real.rpow_nonneg (zero_lt_one.trans r.hZ).le _))
      (r.vol_pos (zero_lt_one.trans r.hZ)).le
  have hsub : labels.filter (fun x=>r.V₀*x.twist∣y) ⊆ labels.filter (fun x=>x.twist∣y) := by
    intro x hx
    obtain ⟨hx,hd⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hx,(dvd_mul_left x.twist r.V₀).trans hd⟩
  calc
    _ ≤ ∑x∈labels.filter (fun x=>r.V₀*x.twist∣y),gWeight x*A :=
      Finset.sum_le_sum (fun x hx=>frameExtractionWeight_le Cred ε δ hCred hδ η r x
        (hfit x (Finset.mem_filter.mp hx).1))
    _ ≤ ∑x∈labels.filter (fun x=>x.twist∣y),gWeight x*A :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _=>mul_nonneg (gWeight_nonneg x) hA)
    _ = A*∑x∈labels.filter (fun x=>x.twist∣y),gWeight x := by rw [Finset.mul_sum]; congr 1; funext x; ring
    _ ≤ A*D := mul_le_mul_of_nonneg_left hfibre hA

#print axioms frameExtractionWeight_nonneg
#print axioms frameExtractionWeight_le
#print axioms frameExtractionWeight_fibre
end
end QRH.Cycle092.RegularColoredForward
