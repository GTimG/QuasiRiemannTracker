import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/-!
Variable-κ conductor damping for the Cycle25 physical numerator.

The finite coefficient-removal argument is adapted from
akashlevy/QuasiRiemannTracker, commit
2fd60c0926b66ea18d7436f5ed55250fd006ab5d,
WeightedQRH/NumeratorDamping.lean (Apache-2.0).

These are scalar and finite-sum lemmas. Their use in a physical moment still
requires the actual coefficient/conductor dictionary, which is not an axiom
or an implicit hypothesis of this file.
-/

noncomputable section
open scoped BigOperators

namespace Cycle25.Numerator

def selectedCapacity (κ z t : ℝ) : ℝ := max 0 (z - t / (3 * κ))

end Cycle25.Numerator

end
end Record1252270103Bootstrap.PR67
