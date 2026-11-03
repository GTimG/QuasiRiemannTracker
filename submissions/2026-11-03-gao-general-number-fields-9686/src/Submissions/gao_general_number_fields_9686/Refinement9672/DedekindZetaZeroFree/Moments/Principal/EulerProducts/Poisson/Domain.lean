/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Principal/EulerProducts/Poisson/Domain.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.EulerDomain

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open scoped Classical

abbrev Coordinates : Type := CorrectionFactors.Coordinates

def OmegaStar : Set Coordinates :=
  {p | 0 < p.1.re ∧ 0 < p.2.1.re ∧ 0 < p.2.2.re ∧
    1 < 6 * p.2.2.re + p.2.1.re ∧ 1 < p.1.re + 6 * p.2.2.re ∧ 1 < p.1.re + p.2.1.re ∧
    2 < p.1.re + p.2.1.re + 6 * p.2.2.re ∧ 5 < 6 * p.1.re + 6 * p.2.2.re ∧
    1 / 2 < p.1.re ∧ 2 < 3 * p.1.re ∧ 5 / 2 < 3 * p.1.re + p.2.1.re}

def OmegaStarMargin (δ : ℝ) : Set Coordinates :=
  {p | δ ≤ p.1.re ∧ δ ≤ p.2.1.re ∧ δ ≤ p.2.2.re ∧
    1 + δ ≤ 6 * p.2.2.re + p.2.1.re ∧ 1 + δ ≤ p.1.re + 6 * p.2.2.re ∧
    1 + δ ≤ p.1.re + p.2.1.re ∧
    2 + δ ≤ p.1.re + p.2.1.re + 6 * p.2.2.re ∧ 5 + δ ≤ 6 * p.1.re + 6 * p.2.2.re ∧
    1 / 2 + δ ≤ p.1.re ∧ 2 + δ ≤ 3 * p.1.re ∧ 5 / 2 + δ ≤ 3 * p.1.re + p.2.1.re}

theorem OmegaStarMargin_subset (δ : ℝ) (hδ : 0 < δ) : OmegaStarMargin δ ⊆ OmegaStar := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

def box (a b c : ℝ) : Set Coordinates :=
  {p | a ≤ p.1.re ∧ b ≤ p.2.1.re ∧ c ≤ p.2.2.re}

def pad : ℝ := 1 / 1000000

def box₁ : Set Coordinates := box Scales.goodLine (3 / 25) (2 / 5)

def box₂ : Set Coordinates := box Scales.rightLine (9 / 10) (1 / 6 + Scales.contourOffset)

def box₃ : Set Coordinates := box Scales.rightLine 1 (1 / 20)

def paddedBox₁ : Set Coordinates := box (Scales.goodLine - pad) (3 / 25 - pad) (2 / 5 - pad)

def paddedBox₂ : Set Coordinates :=
  box (Scales.rightLine - pad) (9 / 10 - pad) (1 / 6 + Scales.contourOffset - pad)

def paddedBox₃ : Set Coordinates := box (Scales.rightLine - pad) (1 - pad) (1 / 20 - pad)

def boxes : Set Coordinates := box₁ ∪ box₂ ∪ box₃

def paddedBoxes : Set Coordinates := paddedBox₁ ∪ paddedBox₂ ∪ paddedBox₃

theorem paddedBoxes_subset_OmegaStarMargin :
    ∃ δ : ℝ, 0 < δ ∧ paddedBoxes ⊆ OmegaStarMargin δ := by
  refine ⟨1 / 100000, by norm_num, ?_⟩
  intro p hp
  simp only [paddedBoxes, paddedBox₁, paddedBox₂, paddedBox₃, box, Set.mem_union,
    Set.mem_setOf_eq] at hp
  simp only [OmegaStarMargin, Set.mem_setOf_eq, pad, Scales.goodLine, Scales.rightLine, Scales.contourOffset] at hp ⊢
  rcases hp with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩ <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num at * <;> linarith

theorem boxes_subset_paddedBoxes : boxes ⊆ paddedBoxes := by
  intro p hp
  simp only [boxes, box₁, box₂, box₃, box, paddedBoxes, paddedBox₁, paddedBox₂, paddedBox₃,
    Set.mem_union, Set.mem_setOf_eq, pad] at hp ⊢
  rcases hp with (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩
  · exact Or.inl (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · exact Or.inl (Or.inr ⟨by linarith, by linarith, by linarith⟩)
  · exact Or.inr ⟨by linarith, by linarith, by linarith⟩

section Hu

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def HuDomain (u : D.Row) : Set Coordinates :=
  {p | Multipliable (fun pr : LocalFiniteSums.ExteriorPrime D.recipe.A =>
    CorrectionFactors.localFactor D.context u.toFrequency pr p.1 p.2.1 p.2.2)}

def Hu (u : D.Row) (ξ w z : ℂ) : ℂ :=
  ∏' pr : LocalFiniteSums.ExteriorPrime D.recipe.A,
    CorrectionFactors.localFactor D.context u.toFrequency pr ξ w z

end Hu

end

end DedekindZetaZeroFree.Quantitative.EulerDomain

end Refinement9672
