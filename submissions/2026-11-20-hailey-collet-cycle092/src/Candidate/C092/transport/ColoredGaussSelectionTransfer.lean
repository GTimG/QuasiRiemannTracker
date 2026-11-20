/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Kernel-checked coefficient-parametric lifting of Sil's fixed Fourier proof.
   Only coefficient, seed-mask, and actual colored PowerFree witnesses change. -/
import Candidate.C092.transport.ColoredGaussSelection
import Lean
set_option autoImplicit false
open Lean Meta Elab Command

private def liftSelection (src dst : Name) : CommandElabM Unit := do
  liftTermElabM do
    let ci ← getConstInfo src
    let cty ← Term.elabTerm (← `(Ideal OAI.SevenEighths.HeckeFamily.O → ℂ)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let cty ← instantiateMVars cty
    withLocalDeclD `ω₁ cty fun w1 => withLocalDeclD `ω₂ cty fun w2 => do
      let trans (e : Expr) : MetaM Expr := Core.transform e (post := fun e => do
        let f := e.getAppFn
        let args := e.getAppArgs
        let .const n ls := f | return .done e
        let p := `QRH.SilDensitySplit.CubeFree.Second.Concrete
        let replacements := #[
          (`QRH.SilDensitySplit.CubeFree.FP.MixedPrincipalWindow.sourceCoefficient,
            `QRH.Cycle092.TwistedRawSource.sourceColumn,6),
          (p ++ `sourceCoefficient_seed,`QRH.Cycle092.TwistedRawSource.sourceColumn_seed,6),
          (`QRH.SilDensitySplit.CubeFree.FP.MixedFirstAveragedWindow.source_fifth_free,
            `QRH.Cycle092.TwistedRawBall.source_fifth_free,6),
          (p ++ `Qenergy,`QRH.Cycle092.RootColoredSeed.energy,6),
          (p ++ `residual_transfer,`QRH.Cycle092.ColoredGaussSelection.residual_transfer,0),
          (p ++ `expansion_transfer,`QRH.Cycle092.ColoredGaussSelection.expansion_transfer,0),
          (p ++ `pointwise_cauchy,`QRH.Cycle092.ColoredGaussSelection.pointwise_cauchy,0),
          (p ++ `live_energy_le,`QRH.Cycle092.ColoredGaussSelection.live_energy_le,0),
          (p ++ `Qpoly,`QRH.Cycle092.ColoredGaussSelection.poly,6),
          (p ++ `selected_expansion,`QRH.Cycle092.ColoredGaussSelection.selected_expansion,8)]
        for (old,new,idx) in replacements do
          if n == old && args.size >= idx then
            return .done (mkAppN (.const new ls) (args[:idx].toArray ++ #[w1,w2] ++ args[idx:].toArray))
        return .done e)
      let ty ← trans ci.type
      unless (ty.find? (· == w1)).isSome && (ty.find? (· == w2)).isSome do
        throwError "coefficient lift failed to expose both colors in {src}"
      let some val := ci.value? true | throwError "no proof for {src}"
      let val ← trans val
      let ty ← mkForallFVars #[w1,w2] ty
      let val ← mkLambdaFVars #[w1,w2] val
      let ty ← instantiateMVars ty
      let val ← instantiateMVars val
      addDecl (.thmDecl {name:=dst,levelParams:=ci.levelParams,type:=ty,value:=val})

run_cmd do
  liftSelection `QRH.SilDensitySplit.CubeFree.Second.Concrete.residual_transfer
    `QRH.Cycle092.ColoredGaussSelection.residual_transfer

run_cmd do
  for n in #[`expansion_transfer,`pointwise_cauchy,`live_energy_le,`summed_live_energy_le] do
    liftSelection (`QRH.SilDensitySplit.CubeFree.Second.Concrete ++ n)
      (`QRH.Cycle092.ColoredGaussSelection ++ n)

#print axioms QRH.Cycle092.ColoredGaussSelection.residual_transfer
#print axioms QRH.Cycle092.ColoredGaussSelection.expansion_transfer
#print axioms QRH.Cycle092.ColoredGaussSelection.pointwise_cauchy
#print axioms QRH.Cycle092.ColoredGaussSelection.live_energy_le
#print axioms QRH.Cycle092.ColoredGaussSelection.summed_live_energy_le

