import QRH
import QRH.IndependentTargets

/-! Each zero classification is equivalent to its independent literal target.
The reverse implications recover nonvanishing from the stated bound on zeros. -/

namespace QRH.ZeroBoundsEquivalence
open scoped _root_.DirichletCharacter

theorem zeta : Independent.zeta ↔
    ∀ {s : ℂ}, riemannZeta s = 0 → s.re ≤ theta := by
  constructor
  · intro h s hz
    exact le_of_not_gt fun hs => h hs hz
  · intro h s hs hz
    exact (not_le_of_gt hs) (h hz)

theorem dirichlet : Independent.allDirichlet ↔
    ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
      _root_.DirichletCharacter.LFunction χ s = 0 →
      s.re ≤ theta ∨ (χ = 1 ∧ s = 1) := by
  constructor
  · intro h q hq χ s hz
    by_cases hexc : χ = 1 ∧ s = 1
    · exact Or.inr hexc
    · exact Or.inl (le_of_not_gt fun hs => h χ hs hexc hz)
  · intro h q hq χ s hs hexc hz
    rcases h χ hz with hle | hpole
    · exact (not_le_of_gt hs) hle
    · exact hexc hpole

theorem hecke : Independent.allHecke ↔
    ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ},
      OAI.SevenEighths.HeckeFamily.LFunction χ s = 0 →
      s.re ≤ theta ∨ (s = 1 ∧ χ.residue = 1) := by
  constructor
  · intro h χ s hz
    by_cases hpole : s = 1 ∧ χ.residue = 1
    · exact Or.inr hpole
    · exact Or.inl (le_of_not_gt fun hs => h χ s hs (not_and_or.mp hpole) hz)
  · intro h χ s hs hpole hz
    rcases h χ hz with hle | hexc
    · exact (not_le_of_gt hs) hle
    · exact (not_and_or.mpr hpole) hexc

end QRH.ZeroBoundsEquivalence

#print axioms QRH.riemannZeta_zero_re_le
#print axioms QRH.DirichletCharacter.zero_re_le_or_exception
#print axioms QRH.DirichletCharacter.zero_re_le
#print axioms QRH.Hecke.zero_re_le_or_exception
#print axioms QRH.Hecke.zero_re_le
#print axioms QRH.ZeroBoundsEquivalence.zeta
#print axioms QRH.ZeroBoundsEquivalence.dirichlet
#print axioms QRH.ZeroBoundsEquivalence.hecke
