/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Coverage

/-!
# Soundness of the exported finite physical-certificate structure

The data modules contain the actual original 57 rectangles and the actual Q
refinement forest reconstructed by replaying the supplied pinned checker.  This
module proves soundness of their geometric and stored-value checkers.  A positive
stored margin is not asserted to be a lower bound for a physical price function:
that substantive pointwise implication remains a separate premise.
-/

set_option autoImplicit false

namespace QRH.PhysicalCertificate

open QRH.Coverage

/-- The three terminal routes distinguished by the exact Q replay. -/
inductive Route where
  | mixed
  | currentExterior
  | oldExterior
  deriving DecidableEq, Repr

/-- An exported terminal box with directed stored integers at scale `10^15`.
The physical numerator is zero for exterior routes, where no such value is stored. -/
structure StoredLeaf where
  box : Box
  route : Route
  normalizedNumerator : ℕ
  physicalNumerator : ℕ
  deriving DecidableEq, Repr

namespace StoredLeaf

/-- The replay's directed stored normalized value, interpreted as a rational. -/
def normalized (leaf : StoredLeaf) : ℚ := leaf.normalizedNumerator / 1000000000000000

/-- The replay's directed stored physical value, used only on mixed leaves. -/
def physical (leaf : StoredLeaf) : ℚ := leaf.physicalNumerator / 1000000000000000

/-- Check exact stored thresholds; this does not check their analytic meaning. -/
def accepted (leaf : StoredLeaf) : Bool :=
  match leaf.route with
  | .mixed => decide (500541 ≤ leaf.normalizedNumerator ∧ 174177 ≤ leaf.physicalNumerator)
  | .currentExterior => decide (19714351 ≤ leaf.normalizedNumerator ∧ leaf.physicalNumerator = 0)
  | .oldExterior => decide (0 < leaf.normalizedNumerator ∧ leaf.physicalNumerator = 0)

/-- Every accepted terminal has a strictly positive stored normalized number. -/
theorem normalized_pos (leaf : StoredLeaf) (h : leaf.accepted = true) :
    0 < leaf.normalized := by
  have hn : 0 < leaf.normalizedNumerator := by
    cases hr : leaf.route <;> simp [accepted, hr] at h <;> omega
  unfold normalized
  positivity

/-- Every accepted mixed terminal has a strictly positive stored physical number. -/
theorem physical_pos (leaf : StoredLeaf) (h : leaf.accepted = true)
    (hr : leaf.route = .mixed) : 0 < leaf.physical := by
  have hn : 0 < leaf.physicalNumerator := by
    simp [accepted, hr] at h
    omega
  unfold physical
  positivity

end StoredLeaf

/-- A complete midpoint quadtree annotated with the actual recorded leaf data. -/
inductive Tree where
  | leaf (record : StoredLeaf)
  | split (lowerLower upperLower lowerUpper upperUpper : Tree)
  deriving Repr

namespace Tree

/-- Forget numerical annotations and retain the `QRH.Coverage` quadtree. -/
def erase : Tree → QuadTree
  | .leaf _ => .leaf
  | .split a b c d => .split a.erase b.erase c.erase d.erase

/-- Recorded terminals in the same deterministic order as the Python replay. -/
def records : Tree → List StoredLeaf
  | .leaf record => [record]
  | .split a b c d => a.records ++ b.records ++ c.records ++ d.records

/-- Check every recorded box against its exact recursive midpoint position. -/
def check (box : Box) : Tree → Bool
  | .leaf record => decide (record.box = box) && record.accepted
  | .split a b c d => check box.lowerLower a &&
      (check box.upperLower b && (check box.lowerUpper c && check box.upperUpper d))

/-- Accepted annotated trees satisfy the existing geometric checker whenever
the selected leaf checker accepts each of their accepted recorded terminals. -/
theorem check_erase (tree : Tree) (box : Box) (h : tree.check box = true)
    {leafCheck : Box → Bool}
    (hLeaf : ∀ record ∈ tree.records, record.accepted = true → leafCheck record.box = true) :
    Coverage.check leafCheck box tree.erase = true := by
  induction tree generalizing box with
  | leaf record =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hbox, haccepted⟩
      simpa only [erase, Coverage.check, hbox] using hLeaf record (by simp [records]) haccepted
  | split a b c d ha hb hc hd =>
      simp only [check, Bool.and_eq_true] at h
      rcases h with ⟨hA, hB, hC, hD⟩
      simp only [erase, Coverage.check, Bool.and_eq_true]
      refine ⟨ha box.lowerLower hA ?_, hb box.upperLower hB ?_,
        hc box.lowerUpper hC ?_, hd box.upperUpper hD ?_⟩
      · intro record hm hp
        exact hLeaf record (by simp only [records, List.mem_append]; exact Or.inl (Or.inl (Or.inl hm))) hp
      · intro record hm hp
        exact hLeaf record (by simp only [records, List.mem_append]; exact Or.inl (Or.inl (Or.inr hm))) hp
      · intro record hm hp
        exact hLeaf record (by simp only [records, List.mem_append]; exact Or.inl (Or.inr hm)) hp
      · intro record hm hp
        exact hLeaf record (by simp only [records, List.mem_append]; exact Or.inr hm) hp

/-- Every point of an accepted annotated tree is covered by an accepted recorded
terminal, using the previously proved `QRH.Coverage.check_sound` theorem. -/
theorem covers_record (tree : Tree) (box : Box) (h : tree.check box = true)
    {p : Point} (hp : box.Contains p) :
    ∃ record ∈ tree.records, record.box.Contains p ∧ record.accepted = true := by
  let leafCheck : Box → Bool := fun b =>
    tree.records.any fun record => decide (record.box = b) && record.accepted
  have hc : Coverage.check leafCheck box tree.erase = true :=
    tree.check_erase box h (by
      intro record hm ha
      simp only [leafCheck, List.any_eq_true]
      exact ⟨record, hm, by simp [ha]⟩)
  apply Coverage.check_sound (P := fun p =>
    ∃ record ∈ tree.records, record.box.Contains p ∧ record.accepted = true) ?_ tree.erase box hc hp
  intro b hb p hp
  simp only [leafCheck, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
  rcases hb with ⟨record, hm, heq, ha⟩
  exact ⟨record, hm, heq ▸ hp, ha⟩

end Tree

/-- One actual coarse root paired with its complete annotated refinement tree. -/
structure Root where
  originalCell : ℕ
  box : Box
  tree : Tree
  deriving Repr

namespace Root

/-- Acceptance of the complete refinement beneath this recorded coarse box. -/
def accepted (root : Root) : Bool := root.tree.check root.box

/-- Convert an annotated root to the existing generic coverage representation. -/
def erase (root : Root) : Coverage.Root := ⟨root.box, root.tree.erase⟩

end Root

/-- Check every root of the actual finite forest. -/
def checkForest (forest : List Root) : Bool := forest.all Root.accepted

/-- Concatenate the accepted recorded terminals of the actual finite forest. -/
def forestRecords (forest : List Root) : List StoredLeaf := forest.flatMap (fun r => r.tree.records)

/-- Count recorded leaves following one of the three explicit replay routes. -/
def routeCount (route : Route) (forest : List Root) : ℕ :=
  (forestRecords forest).countP (fun record => record.route = route)

/-- Forest acceptance distributes over concatenation. -/
theorem checkForest_append (left right : List Root) :
    checkForest (left ++ right) = (checkForest left && checkForest right) := by
  simp [checkForest, List.all_append]

/-- Route counts add when independently checked root groups are concatenated. -/
theorem routeCount_append (route : Route) (left right : List Root) :
    routeCount route (left ++ right) = routeCount route left + routeCount route right := by
  simp [routeCount, forestRecords, List.flatMap_append, List.countP_append]

/-- Split counts of the erased geometry add across independent root groups. -/
theorem splits_append (left right : List Coverage.Root) :
    Coverage.forestSplits (left ++ right) = Coverage.forestSplits left + Coverage.forestSplits right := by
  induction left with
  | nil => simp [Coverage.forestSplits]
  | cons r rest ih => simp [Coverage.forestSplits, ih, Nat.add_assoc]

/-- The actual root union is covered by actual accepted terminals. -/
theorem forest_covers_record {forest : List Root} (h : checkForest forest = true)
    {p : Point} (hp : ∃ root ∈ forest, root.box.Contains p) :
    ∃ record ∈ forestRecords forest, record.box.Contains p ∧ record.accepted = true := by
  rcases hp with ⟨root, hr, hp⟩
  have hc : root.tree.check root.box = true := List.all_eq_true.mp h root hr
  rcases root.tree.covers_record root.box hc hp with ⟨record, hm, hb, ha⟩
  exact ⟨record, List.mem_flatMap.mpr ⟨root, hr, hm⟩, hb, ha⟩

/-- A scientific pointwise conclusion requires a sound interpretation of every
accepted recorded leaf; stored positive arithmetic alone does not supply it. -/
theorem forest_pointwise_of_leaf_sound {forest : List Root}
    (h : checkForest forest = true) {P : Point → Prop}
    (hLeaf : ∀ record ∈ forestRecords forest, record.accepted = true →
      ∀ p, record.box.Contains p → P p)
    {p : Point} (hp : ∃ root ∈ forest, root.box.Contains p) : P p := by
  rcases forest_covers_record h hp with ⟨record, hm, hb, ha⟩
  exact hLeaf record hm ha p hb

/-- One of the 57 exact rectangles in the original four-edge cover. -/
structure OriginalCell where
  edge : ℕ
  box : Box
  deriving DecidableEq, Repr

/-- A finite rectangle-cover proof permitting arbitrary rational axis cuts. -/
inductive CutTree where
  | leaf (cellIndex : ℕ)
  | uSplit (cut : ℚ) (lower upper : CutTree)
  | vSplit (cut : ℚ) (lower upper : CutTree)
  deriving Repr

namespace Box

/-- Keep the first coordinate below an arbitrary rational cut. -/
def uLower (b : Box) (cut : ℚ) : Box := ⟨b.uLo, cut, b.vLo, b.vHi⟩

/-- Keep the first coordinate above an arbitrary rational cut. -/
def uUpper (b : Box) (cut : ℚ) : Box := ⟨cut, b.uHi, b.vLo, b.vHi⟩

/-- Keep the second coordinate below an arbitrary rational cut. -/
def vLower (b : Box) (cut : ℚ) : Box := ⟨b.uLo, b.uHi, b.vLo, cut⟩

/-- Keep the second coordinate above an arbitrary rational cut. -/
def vUpper (b : Box) (cut : ℚ) : Box := ⟨b.uLo, b.uHi, cut, b.vHi⟩

/-- Exact rational endpoint containment of one rectangle in another. -/
def Included (small large : Box) : Prop :=
  large.uLo ≤ small.uLo ∧ small.uHi ≤ large.uHi ∧
    large.vLo ≤ small.vLo ∧ small.vHi ≤ large.vHi

instance (small large : Box) : Decidable (Included small large) := inferInstanceAs
  (Decidable (large.uLo ≤ small.uLo ∧ small.uHi ≤ large.uHi ∧
    large.vLo ≤ small.vLo ∧ small.vHi ≤ large.vHi))

/-- Endpoint inclusion implies inclusion for real points, including boundaries. -/
theorem contains_of_included {small large : Box} (h : Included small large)
    {p : Point} (hp : small.Contains p) : large.Contains p := by
  rcases h with ⟨hu, hu', hv, hv'⟩
  rcases hp with ⟨hpu, hpu', hpv, hpv'⟩
  exact ⟨(Rat.cast_le.mpr hu).trans hpu, hpu'.trans (Rat.cast_le.mpr hu'),
    (Rat.cast_le.mpr hv).trans hpv, hpv'.trans (Rat.cast_le.mpr hv')⟩

/-- Every point belongs to a closed lower or upper first-coordinate child. -/
theorem contains_u_child {b : Box} {p : Point} (hp : b.Contains p) (cut : ℚ) :
    (uLower b cut).Contains p ∨ (uUpper b cut).Contains p := by
  rcases le_total p.1 (cut : ℝ) with h | h
  · exact Or.inl ⟨hp.1, h, hp.2.2.1, hp.2.2.2⟩
  · exact Or.inr ⟨h, hp.2.1, hp.2.2.1, hp.2.2.2⟩

/-- Every point belongs to a closed lower or upper second-coordinate child. -/
theorem contains_v_child {b : Box} {p : Point} (hp : b.Contains p) (cut : ℚ) :
    (vLower b cut).Contains p ∨ (vUpper b cut).Contains p := by
  rcases le_total p.2 (cut : ℝ) with h | h
  · exact Or.inl ⟨hp.1, hp.2.1, hp.2.2.1, h⟩
  · exact Or.inr ⟨hp.1, hp.2.1, h, hp.2.2.2⟩

end Box

namespace CutTree

/-- Check that every partition leaf lies in an actual cell on the requested edge. -/
def check (cells : List OriginalCell) (edge : ℕ) (box : Box) : CutTree → Bool
  | .leaf index => match cells[index]? with
    | none => false
    | some cell => decide (cell.edge = edge ∧ Box.Included box cell.box)
  | .uSplit cut lower upper =>
    check cells edge (Box.uLower box cut) lower && check cells edge (Box.uUpper box cut) upper
  | .vSplit cut lower upper =>
    check cells edge (Box.vLower box cut) lower && check cells edge (Box.vUpper box cut) upper

/-- A checked cut tree proves complete coverage by the actual recorded cells. -/
theorem sound (tree : CutTree) (cells : List OriginalCell) (edge : ℕ) (box : Box)
    (h : tree.check cells edge box = true) {p : Point} (hp : box.Contains p) :
    ∃ cell ∈ cells, cell.edge = edge ∧ cell.box.Contains p := by
  induction tree generalizing box with
  | leaf index =>
      cases hc : cells[index]? with
      | none => simp [check, hc] at h
      | some cell =>
          have hh : cell.edge = edge ∧ Box.Included box cell.box := by
            simpa [check, hc] using h
          exact ⟨cell, List.mem_of_getElem? hc, hh.1, Box.contains_of_included hh.2 hp⟩
  | uSplit cut lower upper hl hu =>
      simp only [check, Bool.and_eq_true] at h
      rcases Box.contains_u_child hp cut with hp | hp
      · exact hl (Box.uLower box cut) h.1 hp
      · exact hu (Box.uUpper box cut) h.2 hp
  | vSplit cut lower upper hl hu =>
      simp only [check, Bool.and_eq_true] at h
      rcases Box.contains_v_child hp cut with hp | hp
      · exact hl (Box.vLower box cut) h.1 hp
      · exact hu (Box.vUpper box cut) h.2 hp

end CutTree

end QRH.PhysicalCertificate
