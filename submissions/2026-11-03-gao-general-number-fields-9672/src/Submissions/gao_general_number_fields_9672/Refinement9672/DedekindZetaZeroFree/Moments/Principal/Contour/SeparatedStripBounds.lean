/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Principal/Contour/SeparatedStripBounds.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Principal.Contour.ZetaStripGrowth

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.PrincipalSeparatedStripBounds

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

private theorem sep_dist (a b : ℝ) (hab : a ≤ b) (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ Set.Icc a b, r ≤ |x - 1| := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_refl a, hab⟩
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn hne
    (f := fun x : ℝ => |x - 1|) (by fun_prop)
  refine ⟨|x0 - 1|, abs_pos.mpr (sub_ne_zero.mpr (hsep x0 hx0)), fun x hx => hmin hx⟩

theorem zeta_on_real_interval (D : FixedData S η) (a b : ℝ) (ha : 0 < a)
    (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := by
  by_cases hab : a ≤ b
  · obtain ⟨r, hr, hd⟩ := sep_dist a b hab hsep
    obtain ⟨C, k, hC, hk, h⟩ :=
      PrincipalZetaStripGrowth.zetaSCont_strip_polynomial_bound D a b r ha hab hr
    refine ⟨C, k, hC, hk, fun s h1 h2 => h s h1 h2 ?_⟩
    calc r ≤ |s.re - 1| := hd _ ⟨h1, h2⟩
      _ ≤ ‖s - 1‖ := by
        have := Complex.abs_re_le_norm (s - 1)
        simpa using this
  · exact ⟨1, 0, one_pos, le_rfl, fun s h1 h2 => absurd (h1.trans h2) hab⟩

theorem Lpsi_principal_on_real_interval (D : FixedData S η) (u : D.Row)
    (hu : u.u = 1) (a b : ℝ) (ha : 0 < a)
    (hsep : ∀ x ∈ Set.Icc a b, x ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖D.Lpsi u s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ := zeta_on_real_interval D a b ha hsep
  refine ⟨C, k, hC, hk, fun s h1 h2 => ?_⟩
  have hs1 : s ≠ 1 := by
    intro h; apply hsep s.re ⟨h1, h2⟩; rw [h]; simp
  rw [PrincipalResidueFormulas.Lpsi_principal_eq D u hu s (lt_of_lt_of_le ha h1) hs1]
  exact h s h1 h2

end Refinement9672
