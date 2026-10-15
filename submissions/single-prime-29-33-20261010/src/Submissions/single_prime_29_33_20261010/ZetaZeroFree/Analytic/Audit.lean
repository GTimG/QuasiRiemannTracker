import Lean

/-! Verification of the actual proof terms, including their imported closure.
The caller chooses a frozen set of modules and required mathematical roots.
This module contains no mathematical assumptions or conclusions. -/

namespace ZetaZeroFree.AnalyticVerification
open Lean Elab Command

private def allowedAxiom (n : Name) : Bool :=
  n == `propext || n == `Classical.choice || n == `Quot.sound

private def forbiddenTerminal (env : Environment) (n : Name) : Bool :=
  let forbiddenModules : Array Name := #[
    `OAI.NumberTheory.DirichletL.Hecke.Nonvanishing,
    `OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional,
    `ZetaZeroFree.Nonvanishing]
  let s := n.toString
  let badName := (s.splitOn "beta_le_seven_eighths").length > 1 ||
    (s.splitOn "ne_zero_of_seven_eighths").length > 1
  let badModule := match env.getModuleIdxFor? n with
    | some m => forbiddenModules.contains env.header.moduleNames[m.toNat]!
    | none => false
  badName || badModule

/-- Every theorem in every requested module is checked, including private
helpers; required roots must be present and must be theorems. The dependency
walk visits types, values, opaque proofs, constructors and recursors. -/
def audit (modules roots : Array Name) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  for module in modules do
    unless env.header.moduleNames.contains module do
      throwError "missing audited module {module}"
  let mut declarations : Array Name := #[]
  let mut theorems : Array Name := #[]
  let mut customAxioms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let owned := match env.getModuleIdxFor? n with
      | some m => modules.contains env.header.moduleNames[m.toNat]!
      | none => false
    if owned then
      declarations := declarations.push n
      match ci with
      | .thmInfo _ => theorems := theorems.push n
      | .axiomInfo _ => customAxioms := customAxioms.push n
      | _ => pure ()
  unless customAxioms.isEmpty do
    throwError "analytic source declares axioms: {customAxioms}"
  unless !theorems.isEmpty do
    throwError "no analytic theorems were discovered"
  for root in roots do
    unless theorems.contains root do
      throwError "required theorem is missing from audited modules: {root}"
  let mut axiomReports : Array Json := #[]
  for root in declarations do
    let axioms ← collectAxioms root
    let forbidden := axioms.filter fun n => !allowedAxiom n
    unless forbidden.isEmpty do
      throwError "forbidden axioms in {root}: {forbidden}"
    axiomReports := axiomReports.push (Json.mkObj [
      ("declaration", toJson root.toString),
      ("axioms", toJson (axioms.map Name.toString))])
  let mut todo := declarations
  let mut seen : NameSet := {}
  let mut idx := 0
  let mut forbidden : Array Name := #[]
  let mut missing : Array Name := #[]
  while idx < todo.size do
    let n := todo[idx]!
    idx := idx + 1
    if seen.contains n then continue
    seen := seen.insert n
    if forbiddenTerminal env n then forbidden := forbidden.push n
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      for dep in ci.getUsedConstantsAsSet.toArray do
        todo := todo.push dep
  let report := Json.mkObj [
    ("modules", toJson (modules.map Name.toString)),
    ("required_roots", toJson (roots.map Name.toString)),
    ("declaration_count", toJson declarations.size),
    ("theorem_count", toJson theorems.size),
    ("theorems", toJson (theorems.map Name.toString)),
    ("axiom_reports", toJson axiomReports),
    ("all_reachable_constants", toJson seen.size),
    ("forbidden_terminal_dependencies", toJson (forbidden.map Name.toString)),
    ("missing_declarations", toJson (missing.map Name.toString))]
  logInfo m!"ANALYTIC_AUDIT {report.compress}"
  unless forbidden.isEmpty && missing.isEmpty do
    throwError "analytic dependency audit failed"

/-- The standalone mixed moment may not depend on either terminal zero-free
result, the former beta-lower-bound wrappers, or disposable extraction modules. -/
def auditD3Independence (roots : Array Name) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut idx := 0
  let mut forbidden : Array Name := #[]
  let mut missing : Array Name := #[]
  while idx < todo.size do
    let n := todo[idx]!
    idx := idx + 1
    if seen.contains n then continue
    seen := seen.insert n
    let badName := #["twenty_nine_thirty_thirds", "beta_le_twenty_nine",
      "common_deleted_probe_estimates", "_of_beta_large",
      "OAI.SevenEighths.CenteredMomentPrimeGlobal.ray_prime_global_squared",
      "UnconditionalOAI", "ZetaUnconditionalMoment", "ZetaPrunedUnconditionalMoment",
      "ZetaUnconditionalCore", "_private.Endpoint", "_private.PrunedLive"].any
        (fun ban => (n.toString.splitOn ban).length > 1)
    let finalModule := match env.getModuleIdxFor? n with
      | some m => env.header.moduleNames[m.toNat]! == `ZetaZeroFree.Analytic.Final
      | none => false
    if forbiddenTerminal env n || badName || finalModule then
      forbidden := forbidden.push n
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      for dep in ci.getUsedConstantsAsSet.toArray do
        todo := todo.push dep
  let report := Json.mkObj [
    ("roots", toJson (roots.map Name.toString)),
    ("reachable_constants", toJson seen.size),
    ("forbidden_dependencies", toJson (forbidden.map Name.toString)),
    ("missing_declarations", toJson (missing.map Name.toString))]
  logInfo m!"D3_INDEPENDENCE_AUDIT {report.compress}"
  unless !roots.isEmpty && forbidden.isEmpty && missing.isEmpty do
    throwError "standalone D3 independence audit failed"

end ZetaZeroFree.AnalyticVerification
