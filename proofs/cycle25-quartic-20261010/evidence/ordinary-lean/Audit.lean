import Cycle25.Assembly.Final.Endpoint
import Lean

#print axioms Cycle25.FinalAssembly.baseline_beta
#print axioms Cycle25.beta_le_theta
#print axioms Cycle25.hecke_nonzero
#print axioms Cycle25.dirichlet_nonzero
#print axioms Cycle25.zeta_nonzero

set_option maxHeartbeats 0

open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``Cycle25.FinalAssembly.baseline_beta, ``Cycle25.beta_le_theta, ``Cycle25.hecke_nonzero,
      ``Cycle25.dirichlet_nonzero, ``Cycle25.zeta_nonzero] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx + 1
      if seen.contains n then continue
      seen := seen.insert n
      if #["WeightedQRH.", "SevenEighths.WeightedProbeLow.",
          "SevenEighths.WeightedLowReflection.", "SevenEighths.WeightedLowReflected.",
          "SevenEighths.WeightedLowNormalizer.", "SevenEighths.WeightedHighFinalAssembly.",
          "weighted_background_beta", "weighted_terminal_certificate",
          "terminal_nonvanishing", "common_deleted_probe_estimates",
          "ZetaZeroFree.Final", "ZetaZeroFree.Analytic.Final",
          "twenty_nine_thirty_thirds", "beta_le_twenty_nine", "quartic_root_bound",
          "nonfixed_zero_at_of_beta_large", "nonfixed_mixed_at_of_beta_large",
          "all_natural_mixed_at_of_beta_large", "all_nonprincipal_at_of_beta_large",
          "UnconditionalOAI", "ZetaUnconditionalMoment", "ZetaPrunedUnconditionalMoment",
          "ZetaUnconditionalCore"].any (fun ban => (n.toString.splitOn ban).length > 1) then
        denied := denied.push n
      if n == ``sorryAx then denied := denied.push n
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          let s := dep.toString
          if #["OAI.", "ZetaZeroFree.", "Cycle25.", "_private.OAI.",
              "_private.ZetaZeroFree.", "_private.Cycle25."].any (fun banPrefix => s.startsWith banPrefix) then
            todo := todo.push dep
    logInfo m!"{root}: {seen.size} project constants; denied = {denied}; missing = {missing}"
    unless denied.isEmpty && missing.isEmpty do
      throwError "Dependency audit rejected {root}"
    Lean.Elab.Command.liftIO <| IO.FS.writeFile
      ("Cycle25/Assembly/Final/used-" ++ root.toString ++ ".txt")
      (String.intercalate "\n" (seen.toArray.toList.map Name.toString))
    -- The original low endpoints are authorized inside the coarse 7/8
    -- initialization; the new physical path must use the Cycle25 low proof.
    let mut newTodo : Array Name := #[root]
    let mut newSeen : NameSet := {}
    let mut newIdx := 0
    let mut oldLow : Array Name := #[]
    while newIdx < newTodo.size do
      let n := newTodo[newIdx]!
      newIdx := newIdx + 1
      if newSeen.contains n then continue
      newSeen := newSeen.insert n
      if n == ``Cycle25.FinalAssembly.baseline_beta then continue
      if #["OAI.SevenEighths.ProbePhysical.original_normalized_compensatedPhysicalProbe_low",
          "OAI.SevenEighths.ProbePhysical.original_ray_compensatedPhysicalProbe_low"].any
          (fun ban => (n.toString.splitOn ban).length > 1) then
        oldLow := oldLow.push n
      match env.find? n with
      | none => throwError "Missing constant on new physical path: {n}"
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          let s := dep.toString
          if #["OAI.", "ZetaZeroFree.", "Cycle25.", "_private.OAI.",
              "_private.ZetaZeroFree.", "_private.Cycle25."].any (fun banPrefix => s.startsWith banPrefix) then
            newTodo := newTodo.push dep
    logInfo m!"{root}: {newSeen.size} constants after coarse baseline cut; old low endpoints = {oldLow}"
    unless oldLow.isEmpty do
      throwError "New physical path uses a fixed-geometry old low endpoint"
