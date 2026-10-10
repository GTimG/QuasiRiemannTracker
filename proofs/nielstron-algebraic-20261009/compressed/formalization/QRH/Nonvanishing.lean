import QRH.Detector.OptimizedSupremum
import QRH.ZetaTransfer

/-! Nonvanishing of the original L-functions at the exact manuscript threshold.
All analytic inputs are discharged in OptimizedSupremum. -/
namespace QRH
noncomputable section
open scoped _root_.DirichletCharacter

theorem Hecke.LFunction_ne_zero_of_theta_lt_re
    (χ:OAI.SevenEighths.HeckeFamily.Character) (s:ℂ)
    (hs:theta<s.re) (hpole:s≠1∨χ.residue≠1):
    OAI.SevenEighths.HeckeFamily.LFunction χ s≠0 :=
  OAI.SevenEighths.HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    (OAI.SevenEighths.QRHFinalAssembly.beta_le_theta.trans_lt hs) hpole

theorem DirichletCharacter.LFunction_ne_zero_of_theta_lt_re
    {q:ℕ} [NeZero q] (χ:_root_.DirichletCharacter ℂ q) {s:ℂ}
    (hs:theta<s.re) (hexc:¬(χ=1∧s=1)):
    _root_.DirichletCharacter.LFunction χ s≠0 := by
  by_cases hge:1≤s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1:s≠1:=by intro h;simp [h] at hge
  have hs0:s≠0:=by intro h;norm_num [h,theta] at hs
  have hh:=Hecke.LFunction_ne_zero_of_theta_lt_re
    (OAI.SevenEighths.HeckeDirichlet.character χ) s hs (Or.inl hs1)
  rw [OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product χ hs0 hs1] at hh
  exact (mul_ne_zero_iff.mp hh).1

theorem riemannZeta_ne_zero_of_theta_lt_re {s:ℂ} (hs:theta<s.re):riemannZeta s≠0 :=
  zeta_of_allDirichlet (@DirichletCharacter.LFunction_ne_zero_of_theta_lt_re) hs

end
end QRH
