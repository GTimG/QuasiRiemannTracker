/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Cycle092 at the true shifted contact, with independent ordinary characters,
all finite heights and the principal-pole exception. -/
import Candidate.C092.transport.ActualStageFrameBudgetEarlierFamilyActual

set_option autoImplicit false
noncomputable section
open OAI OAI.SevenEighths HeckeFamily
namespace QRH.Cycle092

theorem hecke_and_dirichlet_record :
    HeckeZeroSupremum.beta ≤ Cycle090.theta ∧
    (∀ (η:Character) (s:ℂ),Cycle090.theta<s.re → (s≠1 ∨ η.residue≠1) → LFunction η s≠0) ∧
    Cycle090.OrdinaryTarget := by
  apply ActualStageFrameBudget.record_of_family_return
  intro n y l ε δ mesh hy0 hy1 hyn hn hl0 hl hε hδ hm hδloss hρ hmd hlm hm1 hm6
  exact ActualStageFrameBudget.actual_original_family_return n y l mesh ε δ hm6 hδ
    hy0 hy1 hn hl.le hρ hm hmd hm1

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (436666397/500000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  hecke_and_dirichlet_record.2.2 χ hs hpole

#print axioms hecke_and_dirichlet_record
#print axioms dirichlet_nonvanishing
end QRH.Cycle092
