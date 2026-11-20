/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
   Genuine colored common-label multiplicity, uniformly for either column choice. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerAssembly
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeometry2
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
open QRH.SilDensitySplit.CubeFree.Second.ProviderGeometry
namespace QRH.Cycle092.ActualLabelFiniteCosts
local notation "Id" => Ideal HeckeFamily.O
local notation "O" => HeckeFamily.O

/-- A column chooser may choose a different side at each original label.
Its fibre is contained in the union of the two original side fibres. -/
lemma mixed_column_multiplicity (S : Finset Id) (m : ℕ)
    (hside : ∀ (side : Bool) (G : Id) (A : O),
      (Finset.filter (fun l : Lab S =>
        (if side then l.1.val.1 else l.1.val.2) = G ∧ lA S l = A) Finset.univ).card ≤ m)
    (g : Lab S→Id) (hg : IsColumn S g) (G : Id) (A : O) :
    ((Finset.univ : Finset (Lab S)).filter (fun l=>g l=G ∧ lA S l=A)).card≤2*m := by
  let lc := (Finset.univ : Finset (Lab S)).filter (fun l=>l.1.val.1=G ∧ lA S l=A)
  let ld := (Finset.univ : Finset (Lab S)).filter (fun l=>l.1.val.2=G ∧ lA S l=A)
  have hs : (Finset.univ : Finset (Lab S)).filter (fun l=>g l=G ∧ lA S l=A)⊆lc∪ld := by
    intro l hl
    obtain ⟨hu,hgG,hA⟩ := Finset.mem_filter.mp hl
    rcases hg l with hc|hd
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hu,hc ▸ hgG,hA⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hu,hd ▸ hgG,hA⟩
  have hleft : lc.card≤ m := by simpa only [lc,ite_true] using hside true G A
  have hright : ld.card≤ m := by simpa only [ld,Bool.false_eq_true,ite_false] using hside false G A
  calc
    _≤(lc∪ld).card := Finset.card_le_card hs
    _≤lc.card+ld.card := Finset.card_union_le _ _
    _≤ m+m := Nat.add_le_add hleft hright
    _=2*m := by omega

/-- Same C before Z and before every actual colored source. The cube-free
common-label hypotheses follow internally from actual original tuple witnesses. -/
theorem actual_multiplicity (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1≤Z → ∀ {ι : Type*} [Fintype ι] {a b : ℝ}
      (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Character),
      (∀I∈RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂),(I.absNorm:ℝ)≤Z^(8:ℝ)) →
      ∃ Mm : ℕ,(Mm:ℝ)≤C*Z^δ ∧
        ∀g : Lab (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂))→Id,
        IsColumn _ g → ∀G A,((Finset.univ : Finset (Lab
          (RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)))).filter
            (fun l=>g l=G ∧ lA _ l=A)).card≤Mm := by
  obtain ⟨C,hC,hms⟩ := mult_subpower 4 δ (by norm_num) hδ
  refine ⟨2*(C+1),by positivity,?_⟩
  intro Z hZ ι inst a b s ha ω₁ ω₂ hX
  let S := RootColoredSeed.active s ha (idealCoeff ω₁) (idealCoeff ω₂)
  have hcube := ColoredGaussFrameProvider.lab_cube_rad ω₁ ω₂ s ha
  have hnorm : ∀l:Lab S,(l.1.val.1.absNorm:ℝ)≤Z^(2*(4:ℝ)) ∧
      (l.1.val.2.absNorm:ℝ)≤Z^(2*(4:ℝ)) := by
    intro l
    norm_num only [show (2*(4:ℝ))=8 by norm_num]
    exact lab_cols_le S _ hX l
  have hm : ∀side : Bool,∀G A,((Finset.univ : Finset (Lab S)).filter (fun l=>
      (if side then l.1.val.1 else l.1.val.2)=G ∧ lA S l=A)).card≤⌈C*Z^δ⌉₊ := by
    intro side G A
    exact_mod_cast (hms Z hZ S side hcube hnorm G A).trans (Nat.le_ceil _)
  refine ⟨2*⌈C*Z^δ⌉₊,?_,fun g hg G A=>mixed_column_multiplicity S _ hm g hg G A⟩
  have hpow : 1≤Z^δ := Real.one_le_rpow hZ hδ.le
  have hceil := (Nat.ceil_lt_add_one (show 0≤C*Z^δ by positivity)).le
  push_cast
  nlinarith

#print axioms mixed_column_multiplicity
#print axioms actual_multiplicity
end QRH.Cycle092.ActualLabelFiniteCosts
