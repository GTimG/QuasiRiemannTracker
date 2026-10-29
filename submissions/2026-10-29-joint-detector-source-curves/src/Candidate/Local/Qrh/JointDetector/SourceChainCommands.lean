/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.StepMacro
import Candidate.Local.Qrh.JointDetector.CurvedSourceChains.Common

/-! Commands abbreviate repeated declarations only. Every emitted theorem and
application is checked by Lean; these commands add no proof axiom. -/
namespace Qrh.JointDetector.SourceChainCommands
open Lean Elab Command

private def suffix (n : Nat) : String :=
 let s := toString n
 String.ofList (List.replicate (5-s.length) '0') ++ s

private def compose (first last : Nat) (cores : Bool) : CommandElabM (TSyntax `term) := do
 if last < first then throwError "empty source chain"
 let hb := mkIdent `hβ
 let hc := mkIdent `hcores
 let mut proof : TSyntax `term := mkIdent `hp
 for n in List.range (last-first+1) do
  let step := mkIdent (Name.mkSimple ("step"++suffix (first+n)))
  proof ← if cores then `(term| $step $hc $hb $proof) else `(term| $step $hb $proof)
 return proof

syntax "linear_source_steps " ident num num : command
elab_rules : command
 | `(linear_source_steps $round:ident $first:num $last:num) => do
  if last.getNat < first.getNat then throwError "empty source steps"
  for n in List.range (last.getNat-first.getNat+1) do
   let k := first.getNat+n
   let step := mkIdent (Name.mkSimple ("step"++suffix k))
   let stage := mkIdent (((`Qrh.JointDetector.RestartSourceGeometry).append round.getId).str ("stage"++suffix k))
   let idx := Syntax.mkNumLit (toString k)
   elabCommand (← `(command| theorem $step : Qrh.JointDetector.RestartSourceChains.SourceStep $stage := by
    source_chain_step $round $idx))

syntax "curved_source_steps " ident num num term : command
elab_rules : command
 | `(curved_source_steps $chunk:ident $first:num $last:num $mode:term) => do
  if last.getNat < first.getNat then throwError "empty source steps"
  for n in List.range (last.getNat-first.getNat+1) do
   let k := first.getNat+n
   let step := mkIdent (Name.mkSimple ("step"++suffix k))
   let p := mkIdent (((`Qrh.JointDetector.CurvedSourceGeometry).append chunk.getId).str ("p"++toString k))
   let stage := mkIdent (((`Qrh.JointDetector.CurvedSourceHigh).append chunk.getId).str ("stage"++toString k))
   elabCommand (← `(command| theorem $step : Qrh.JointDetector.CurvedSourceChains.SourceStep $p :=
    Qrh.JointDetector.CurvedSourceChains.certified_step_of_stage (combined:=$mode) $stage
      (by norm_num [$p:ident]) (by norm_num [$p:ident])))

syntax "linear_source_compose " ident num num " [" term "," term "," term "," term "," term "," term "]" : command
elab_rules : command
 | `(linear_source_compose $name:ident $first:num $last:num [$pb:term,$pl:term,$pc:term,$cb:term,$cl:term,$cc:term]) => do
  let proof ← compose first.getNat last.getNat true
  let hc := mkIdent `hcores
  let hb := mkIdent `hβ
  let hp := mkIdent `hp
  elabCommand (← `(command| theorem $name
   ($hc : Qrh.JointDetector.RestartSourceChains.ParentCoreProvider)
   ($hb : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
   ($hp : QRH.Record1252270103Source.GlobalSource $pb $pl $pc) :
   QRH.Record1252270103Source.GlobalSource $cb $cl $cc := by exact $proof))

syntax "curved_source_compose " ident num num " [" term "," term "," term "," term "," term "," term "]" : command
elab_rules : command
 | `(curved_source_compose $name:ident $first:num $last:num [$pb:term,$pl:term,$pc:term,$cb:term,$cl:term,$cc:term]) => do
  let proof ← compose first.getNat last.getNat false
  let hb := mkIdent `hβ
  let hp := mkIdent `hp
  elabCommand (← `(command| theorem $name
   ($hb : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
   ($hp : QRH.Record1252270103Source.GlobalSource $pb $pl $pc) :
   QRH.Record1252270103Source.GlobalSource $cb $cl $cc := by exact $proof))
end Qrh.JointDetector.SourceChainCommands
