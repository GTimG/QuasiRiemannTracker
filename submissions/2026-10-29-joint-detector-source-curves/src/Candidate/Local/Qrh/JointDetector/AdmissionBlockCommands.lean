/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.ReturnCertificateCommands

open Lean

/-- Syntax compression only: emits the original fifteen `positive_poly`
commands and the finite-index aggregation theorem. All coefficients and
proofs are checked by the existing ordinary kernel proof commands. -/
declare_syntax_cat admission_block_row
syntax "|" "(" term "," term ")" term "coefficients" term : admission_block_row

macro "admission_block " name:ident " using " branch:ident
    " box(" a:term "," b:term "," c:term "," d:term ")" " where "
    rows:admission_block_row* " end_admission" : command => do
  unless rows.size == 15 do Macro.throwError "admission_block requires fifteen guards"
  let base := name.getId.eraseMacroScopes.toString
  let branchName := branch.getId.eraseMacroScopes.toString
  let ctor := mkIdent (Name.str (Name.mkSimple "CountBranch") branchName)
  let guardId := mkIdent (Name.mkSimple "admissionGuard")
  let mut commands : Array Syntax := #[]
  let mut proofs : Array (TSyntax `tactic) := #[]
  for i in [:rows.size] do
    let `(admission_block_row| | ($m,$n) $reserve coefficients $table) := rows[i]!
      | Macro.throwError "invalid admission guard row"
    let suffix := (if i < 10 then "0" else "") ++ toString i
    let nm := mkIdent (Name.mkSimple (base ++ "_" ++ suffix))
    let exp := mkIdent (Name.mkSimple ("admission_power_" ++ branchName ++ "_" ++ suffix ++ "_expanded"))
    let idx := quote i
    let cmd ← `(command| positive_poly $nm dims($m,$n)
      (fun δ p : ℝ => $guardId $ctor δ p $idx) via $exp
      margin $reserve box($a,$b,$c,$d) coefficients $table)
    commands := commands.push cmd.raw
    let pos := mkIdent (Name.mkSimple (base ++ "_" ++ suffix ++ "_pos"))
    proofs := proofs.push (← `(tactic| · exact $pos hδ hp))
  let all := mkIdent (Name.mkSimple (base ++ "_all"))
  let aggregate ← `(command| theorem $all {δ p : ℝ}
    (hδ : δ ∈ Set.Icc $a $b) (hp : p ∈ Set.Icc $c $d)
    (j : Fin 15) : 0 < $guardId $ctor δ p j := by
      fin_cases j
      $proofs:tactic*)
  return ⟨mkNullNode (commands.push aggregate.raw)⟩
