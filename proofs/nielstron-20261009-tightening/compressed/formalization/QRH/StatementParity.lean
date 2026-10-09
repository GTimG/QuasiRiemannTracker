import QRH.DirichletTargets
import QRH.HeckeTargets
import QRH.IndependentTargets

/-! These equalities check proposition parity. They do not inhabit the propositions. -/
namespace QRH.StatementParity
 theorem dirichlet : Targets.AllDirichlet = Independent.allDirichlet := rfl
 theorem zeta : Targets.Zeta = Independent.zeta := rfl
 theorem hecke : Targets.AllHecke = Independent.allHecke := rfl
end QRH.StatementParity
