/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.PhysicalCertificate.Basic

/-!
# Original-return partition bridge

This checker bridges each of the actual original rectangles to either a direct
original-route terminal or a coarse Q root.  Direct-route margins are checked as
positive stored values; their pointwise price meaning remains an explicit gap.
-/

set_option autoImplicit false

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- A direct original-route terminal and its positive stored numerator at scale `10^15`. -/
structure DirectLeaf where
  box : Box
  route : String
  marginNumerator : ℕ
  deriving Repr

namespace DirectLeaf

/-- Exact stored original-route value, before separately charged padding. -/
def margin (leaf : DirectLeaf) : ℚ := leaf.marginNumerator / 1000000000000000

/-- A positive recorded numerator represents a positive rational number. -/
theorem margin_pos (leaf : DirectLeaf) (h : 0 < leaf.marginNumerator) : 0 < leaf.margin := by
  unfold margin
  positivity

end DirectLeaf

/-- A finite partition of an original cell into direct routes and actual Q roots. -/
inductive InitialTree where
  | direct (record : DirectLeaf)
  | central (rootIndex : ℕ)
  | uSplit (cut : ℚ) (lower upper : InitialTree)
  | vSplit (cut : ℚ) (lower upper : InitialTree)
  deriving Repr

namespace InitialTree

/-- Check every exact partition region against its direct leaf or selected Q root. -/
def check (owner : ℕ) (roots : List Root) (box : Box) : InitialTree → Bool
  | .direct record => decide (Box.Included box record.box ∧ 0 < record.marginNumerator)
  | .central index => match roots[index]? with
    | none => false
    | some root => decide (root.originalCell = owner ∧ Box.Included box root.box)
  | .uSplit cut lower upper =>
    check owner roots (Box.uLower box cut) lower && check owner roots (Box.uUpper box cut) upper
  | .vSplit cut lower upper =>
    check owner roots (Box.vLower box cut) lower && check owner roots (Box.vUpper box cut) upper

/-- All actual recorded direct terminals used by the initial partition. -/
def directRecords : InitialTree → List DirectLeaf
  | .direct record => [record]
  | .central _ => []
  | .uSplit _ lower upper => lower.directRecords ++ upper.directRecords
  | .vSplit _ lower upper => lower.directRecords ++ upper.directRecords

/-- Assemble checked first-coordinate subpartitions without recomputing them. -/
theorem check_uSplit (owner : ℕ) (roots : List Root) (box : Box) (cut : ℚ)
    (lower upper : InitialTree)
    (hl : lower.check owner roots (Box.uLower box cut) = true)
    (hu : upper.check owner roots (Box.uUpper box cut) = true) :
    (InitialTree.uSplit cut lower upper).check owner roots box = true := by
  simp only [check, hl, hu, Bool.and_self]

/-- Assemble checked second-coordinate subpartitions without recomputing them. -/
theorem check_vSplit (owner : ℕ) (roots : List Root) (box : Box) (cut : ℚ)
    (lower upper : InitialTree)
    (hl : lower.check owner roots (Box.vLower box cut) = true)
    (hu : upper.check owner roots (Box.vUpper box cut) = true) :
    (InitialTree.vSplit cut lower upper).check owner roots box = true := by
  simp only [check, hl, hu, Bool.and_self]

/-- A checked original partition covers every real point by either a positive
stored direct terminal or an actual coarse Q root, including every boundary. -/
theorem sound (tree : InitialTree) (owner : ℕ) (roots : List Root) (box : Box)
    (h : tree.check owner roots box = true) {p : Point} (hp : box.Contains p) :
    (∃ record ∈ tree.directRecords, record.box.Contains p ∧ 0 < record.margin) ∨
      (∃ root ∈ roots, root.originalCell = owner ∧ root.box.Contains p) := by
  induction tree generalizing box with
  | direct record =>
      have hh : Box.Included box record.box ∧ 0 < record.marginNumerator := by
        simpa [check] using h
      exact Or.inl ⟨record, by simp [directRecords], Box.contains_of_included hh.1 hp,
        record.margin_pos hh.2⟩
  | central index =>
      cases hr : roots[index]? with
      | none => simp [check, hr] at h
      | some root =>
          have hi : root.originalCell = owner ∧ Box.Included box root.box := by simpa [check, hr] using h
          exact Or.inr ⟨root, List.mem_of_getElem? hr, hi.1, Box.contains_of_included hi.2 hp⟩
  | uSplit cut lower upper hl hu =>
      simp only [check, Bool.and_eq_true] at h
      rcases Box.contains_u_child hp cut with hp | hp
      · rcases hl (Box.uLower box cut) h.1 hp with ⟨record, hm, hb, hv⟩ | hr
        · exact Or.inl ⟨record, by simp [directRecords, hm], hb, hv⟩
        · exact Or.inr hr
      · rcases hu (Box.uUpper box cut) h.2 hp with ⟨record, hm, hb, hv⟩ | hr
        · exact Or.inl ⟨record, by simp [directRecords, hm], hb, hv⟩
        · exact Or.inr hr
  | vSplit cut lower upper hl hu =>
      simp only [check, Bool.and_eq_true] at h
      rcases Box.contains_v_child hp cut with hp | hp
      · rcases hl (Box.vLower box cut) h.1 hp with ⟨record, hm, hb, hv⟩ | hr
        · exact Or.inl ⟨record, by simp [directRecords, hm], hb, hv⟩
        · exact Or.inr hr
      · rcases hu (Box.vUpper box cut) h.2 hp with ⟨record, hm, hb, hv⟩ | hr
        · exact Or.inl ⟨record, by simp [directRecords, hm], hb, hv⟩
        · exact Or.inr hr

end InitialTree

end QRH.PhysicalCertificate
