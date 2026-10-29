/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RestartSourceChains.Common
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionLiteral

syntax "source_chain_step " ident num : tactic
elab_rules : tactic
 | `(tactic| source_chain_step $round:ident $idx:num) => do
   let digits := toString idx.getNat
   let suffix := String.ofList (List.replicate (5-digits.length) '0') ++ digits
   let gb := (`Qrh.JointDetector.RestartSourceGeometry).append round.getId
   let hb := (`Qrh.JointDetector.RestartSourceHigh).append round.getId
   let geom := Lean.mkIdent (gb.str ("geometry"++suffix))
   let high := Lean.mkIdent (hb.str ("signs"++suffix))
   let stage := Lean.mkIdent (gb.str ("stage"++suffix))
   Lean.Elab.Tactic.evalTactic (← `(tactic| apply
     Qrh.JointDetector.RestartSourceChains.certified_step_of_signs $geom $high))
   Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $stage:ident))
   Lean.Elab.Tactic.evalTactic (← `(tactic| norm_num [
     Qrh.JointDetector.RestartSourceChains.SourceRanges,
     Qrh.JointDetector.RestartSourceChains.countFloor,
     Qrh.JointDetector.RepeatedMarks.FractionArithmetic.Fraction.evalR]))
