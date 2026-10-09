# Independent statement comparison

Status: all three literal specifications remain frozen; compiled specification parity PASSED for Dirichlet, zeta and Hecke. The corresponding transitive axiom audits use only propext, Classical.choice and Quot.sound (logs/StatementParityAxioms.log). Final theorem parity is **not passed**, because no final theorem witnesses exist. `FinalTargetsRequired.lean` is an explicit failing completion gate and is not imported by the accepted partial library.

OpenAI baseline: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`.

| Component | Original | Frozen target |
|---|---|---|
| Modulus | `{q : ℕ} [NeZero q]` | Identical; neither q=0 nor finite modulus restrictions introduced |
| Character | `(χ : DirichletCharacter ℂ q)` | Same root type, every character |
| Argument | `{s : ℂ}` | Identical, all heights and real arguments |
| Half-plane | `(7 / 8 : ℝ) < s.re` | `(874957019421 / 1000000000000 : ℝ) < s.re` |
| Pole exception | `¬ (χ = 1 ∧ s = 1)` | Identical |
| Conclusion | `_root_.DirichletCharacter.LFunction χ s ≠ 0` | Identical actual function |
| Zeta | `{s : ℂ}`, no exception at 1 | Identical actual `riemannZeta`, new exact threshold |

`QRH.Targets.AllDirichlet` and `QRH.Targets.Zeta` use `QRH.theta`; independently written `QRH.Independent` specifications spell out the rational literal and import no QRH geometry or proof module. `StatementParity.lean` compares their full proposition types by definitional equality. Such equality supplies no proof of either proposition.

For Hecke, the frozen type is every `OAI.SevenEighths.HeckeFamily.Character` and every complex `s`, with `s ≠ 1 ∨ χ.residue ≠ 1`. The conclusion uses the existing `HeckeFamily.LFunction`. The character field is `CyclotomicField 3 ℚ`, the Eisenstein quadratic field, and its integer ring. `Character` contains a nonzero ideal modulus, a complex residue multiplicative character, triviality on global units, and a positive integral period contained in the modulus. None of its fields assumes any analytic bound or nonvanishing. `Character.ofResidue` constructs such a period from the finite quotient. `IdealBridge.LFunction` is the existing continued lattice function divided by six, with an existing ideal Dirichlet-series identity for Re(s)>1. No definition is replaced or shadowed.

The independent Hecke specification repeats this complete quantification with the exact rational literal. The broader mathematical correspondence with all finite-order Hecke characters uses the established class-number-one/ray-character representation; the actual analytic theorem and its transfer obligations remain unfinished, so no completed all-Hecke claim is made.

Mathlib's total function assigns `riemannZeta 1 = (γ - log(4π))/2` with complex coercions. It proves that value nonzero. This is not the classical pole being removed: the meromorphic function still has residue one at its pole. Accordingly the zeta target has no extra `s ≠ 1` premise, while the Dirichlet target keeps OpenAI's precise exception.

Expected final names are `QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re`, `QRH.riemannZeta_ne_zero_of_theta_lt_re`, and `QRH.Hecke.LFunction_ne_zero_of_theta_lt_re`. All three are currently absent. Do not replace the completion gate with the much weaker specification-equality checks or a zeta-only Comparator configuration.

A separate checked intermediate result, `QRH.zeta_of_allDirichlet`, proves `Targets.AllDirichlet → Targets.Zeta` through the actual modulus-one L-function identity and Mathlib's nonzero value at one. Its premise is not discharged, so this implication is not a substitute for either required final theorem.
