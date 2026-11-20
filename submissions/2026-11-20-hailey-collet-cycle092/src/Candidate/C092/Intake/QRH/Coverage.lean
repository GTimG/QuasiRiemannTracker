/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Sound certificates for closed rectangle covers

This module supplies the recursive geometric checker needed by the kind of finite
certificate described in manuscript Q.3. Rectangle endpoints are exact rationals;
the certified pointwise property is a predicate on real pairs. Every branch uses
all four closed midpoint children, so boundaries are retained.

The checker is sound only when its leaf checker has a proof of soundness. The
module does not provide the manuscript's physical leaf checker, tree, or interval
data. In particular, the cardinality identities below are bookkeeping facts and
do not imply that a proposed physical cover has been checked.
-/

namespace QRH.Coverage

/-- A point of the two-dimensional parameter plane, with real coordinates. -/
abbrev Point := ℝ × ℝ

/-- An exact rational closed rectangle, permitting empty or degenerate rectangles. -/
structure Box where
  uLo : ℚ
  uHi : ℚ
  vLo : ℚ
  vHi : ℚ
  deriving DecidableEq, Repr

namespace Box

/-- Membership in the closed rectangle after embedding its rational endpoints in `ℝ`. -/
def Contains (b : Box) (p : Point) : Prop :=
  (b.uLo : ℝ) ≤ p.1 ∧ p.1 ≤ (b.uHi : ℝ) ∧
    (b.vLo : ℝ) ≤ p.2 ∧ p.2 ≤ (b.vHi : ℝ)

/-- The exact midpoint of the first coordinate interval. -/
def uMid (b : Box) : ℚ := (b.uLo + b.uHi) / 2

/-- The exact midpoint of the second coordinate interval. -/
def vMid (b : Box) : ℚ := (b.vLo + b.vHi) / 2

/-- The lower first-coordinate, lower second-coordinate midpoint child. -/
def lowerLower (b : Box) : Box := ⟨b.uLo, b.uMid, b.vLo, b.vMid⟩

/-- The upper first-coordinate, lower second-coordinate midpoint child. -/
def upperLower (b : Box) : Box := ⟨b.uMid, b.uHi, b.vLo, b.vMid⟩

/-- The lower first-coordinate, upper second-coordinate midpoint child. -/
def lowerUpper (b : Box) : Box := ⟨b.uLo, b.uMid, b.vMid, b.vHi⟩

/-- The upper first-coordinate, upper second-coordinate midpoint child. -/
def upperUpper (b : Box) : Box := ⟨b.uMid, b.uHi, b.vMid, b.vHi⟩

/-- Every point of a closed parent rectangle belongs to at least one midpoint child. -/
theorem contains_child {b : Box} {p : Point} (hp : b.Contains p) :
    b.lowerLower.Contains p ∨ b.upperLower.Contains p ∨
      b.lowerUpper.Contains p ∨ b.upperUpper.Contains p := by
  rcases hp with ⟨huLo, huHi, hvLo, hvHi⟩
  rcases le_total p.1 (b.uMid : ℝ) with hu | hu
  · rcases le_total p.2 (b.vMid : ℝ) with hv | hv
    · exact Or.inl ⟨huLo, hu, hvLo, hv⟩
    · exact Or.inr (Or.inr (Or.inl ⟨huLo, hu, hv, hvHi⟩))
  · rcases le_total p.2 (b.vMid : ℝ) with hv | hv
    · exact Or.inr (Or.inl ⟨hu, huHi, hvLo, hv⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hu, huHi, hv, hvHi⟩))

end Box

/-- A finite full quadtree; every split has exactly four children in the stated order. -/
inductive QuadTree where
  | leaf : QuadTree
  | split (lowerLower upperLower lowerUpper upperUpper : QuadTree) : QuadTree
  deriving DecidableEq, Repr

namespace QuadTree

/-- The number of terminal boxes in a quadtree. -/
def leaves : QuadTree → ℕ
  | .leaf => 1
  | .split a b c d => a.leaves + b.leaves + c.leaves + d.leaves

/-- The number of four-way subdivision nodes in a quadtree. -/
def splits : QuadTree → ℕ
  | .leaf => 0
  | .split a b c d => 1 + a.splits + b.splits + c.splits + d.splits

/-- The total number of nodes, including terminal boxes and subdivision nodes. -/
def nodes : QuadTree → ℕ
  | .leaf => 1
  | .split a b c d => 1 + a.nodes + b.nodes + c.nodes + d.nodes

/-- A full quadtree gains exactly three leaves for every split. -/
theorem leaves_eq (t : QuadTree) : t.leaves = 1 + 3 * t.splits := by
  induction t with
  | leaf => simp [leaves, splits]
  | split a b c d ha hb hc hd =>
    simp only [leaves, splits, ha, hb, hc, hd]
    omega

/-- A full quadtree gains exactly four nodes for every split. -/
theorem nodes_eq (t : QuadTree) : t.nodes = 1 + 4 * t.splits := by
  induction t with
  | leaf => simp [nodes, splits]
  | split a b c d ha hb hc hd =>
    simp only [nodes, splits, ha, hb, hc, hd]
    omega

/-- All quadtree nodes are either leaves or subdivision nodes. -/
theorem nodes_eq_leaves_add_splits (t : QuadTree) :
    t.nodes = t.leaves + t.splits := by
  rw [nodes_eq, leaves_eq]
  omega

end QuadTree

/-- Recursively check every terminal closed box using deterministic midpoint subdivision. -/
def check (leafCheck : Box → Bool) (b : Box) : QuadTree → Bool
  | .leaf => leafCheck b
  | .split a c d e =>
    check leafCheck b.lowerLower a &&
      (check leafCheck b.upperLower c &&
        (check leafCheck b.lowerUpper d && check leafCheck b.upperUpper e))

/--
Every accepted tree certifies the pointwise property throughout its root rectangle,
provided each accepted leaf certifies that property throughout its own closed box.
-/
theorem check_sound {leafCheck : Box → Bool} {P : Point → Prop}
    (hLeaf : ∀ b, leafCheck b = true → ∀ p, b.Contains p → P p)
    (tree : QuadTree) (b : Box) (hcheck : check leafCheck b tree = true)
    {p : Point} (hp : b.Contains p) : P p := by
  induction tree generalizing b with
  | leaf => exact hLeaf b hcheck p hp
  | split a c d e ha hc hd he =>
    simp only [check, Bool.and_eq_true] at hcheck
    rcases hcheck with ⟨hA, hC, hD, hE⟩
    rcases Box.contains_child hp with h | h | h | h
    · exact ha b.lowerLower hA h
    · exact hc b.upperLower hC h
    · exact hd b.lowerUpper hD h
    · exact he b.upperUpper hE h

/-- A root rectangle paired with its complete finite subdivision certificate. -/
structure Root where
  box : Box
  tree : QuadTree
  deriving DecidableEq, Repr

/-- Accept a forest precisely when every root's complete tree is accepted. -/
def checkForest (leafCheck : Box → Bool) (forest : List Root) : Bool :=
  forest.all fun root => check leafCheck root.box root.tree

/-- Soundness of a checked forest on the union of its closed root rectangles. -/
theorem checkForest_sound {leafCheck : Box → Bool} {P : Point → Prop}
    (hLeaf : ∀ b, leafCheck b = true → ∀ p, b.Contains p → P p)
    {forest : List Root} (hcheck : checkForest leafCheck forest = true)
    {p : Point} (hp : ∃ root ∈ forest, root.box.Contains p) : P p := by
  rcases hp with ⟨root, hroot, hp⟩
  have hchecked : check leafCheck root.box root.tree = true :=
    (List.all_eq_true.mp hcheck) root hroot
  exact check_sound hLeaf root.tree root.box hchecked hp

/-- Total terminal-box count of a forest of quadtree certificates. -/
def forestLeaves : List Root → ℕ
  | [] => 0
  | r :: rs => r.tree.leaves + forestLeaves rs

/-- Total four-way subdivision count of a forest of quadtree certificates. -/
def forestSplits : List Root → ℕ
  | [] => 0
  | r :: rs => r.tree.splits + forestSplits rs

/-- Total node count of a forest of quadtree certificates. -/
def forestNodes : List Root → ℕ
  | [] => 0
  | r :: rs => r.tree.nodes + forestNodes rs

/-- For any actual forest, leaves equal root count plus three times split count. -/
theorem forestLeaves_eq (forest : List Root) :
    forestLeaves forest = forest.length + 3 * forestSplits forest := by
  induction forest with
  | nil => simp [forestLeaves, forestSplits]
  | cons root rest ih =>
    simp only [forestLeaves, forestSplits, List.length_cons, QuadTree.leaves_eq, ih]
    omega

/-- For any actual forest, nodes equal root count plus four times split count. -/
theorem forestNodes_eq (forest : List Root) :
    forestNodes forest = forest.length + 4 * forestSplits forest := by
  induction forest with
  | nil => simp [forestNodes, forestSplits]
  | cons root rest ih =>
    simp only [forestNodes, forestSplits, List.length_cons, QuadTree.nodes_eq, ih]
    omega

/-- The forest's node count is the sum of its leaf and split counts. -/
theorem forestNodes_eq_leaves_add_splits (forest : List Root) :
    forestNodes forest = forestLeaves forest + forestSplits forest := by
  rw [forestNodes_eq, forestLeaves_eq]
  omega

end QRH.Coverage
