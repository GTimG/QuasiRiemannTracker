import QRH.Geometry
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

/-! Frozen actual-object Hecke proposition; this file supplies no proof witness. -/
namespace QRH.Targets

def AllHecke : Prop :=
  ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    QRH.theta < s.re → (s ≠ 1 ∨ χ.residue ≠ 1) →
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0
end QRH.Targets
