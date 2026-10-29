/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceFractionTransport
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionLiteral

syntax "source_fraction_high " ident num : tactic
elab_rules : tactic
 | `(tactic| source_fraction_high $round:ident $idx:num) => do
   let digits := toString idx.getNat
   let suffix := String.ofList (List.replicate (5-digits.length) '0') ++ digits
   let fracBase := (`Qrh.JointDetector.RestartSourceFractions).append round.getId
   let realBase := (`Qrh.JointDetector.RestartSourceGeometry).append round.getId
   let cert := Lean.mkIdent (fracBase.str ("certificate"++suffix))
   let rp := Lean.mkIdent (realBase.str ("stage"++suffix))
   Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $rp:ident))
   Lean.Elab.Tactic.evalTactic (← `(tactic|
     convert (($cert).sourceHighSigns) using 1 <;>
       norm_num [Qrh.JointDetector.RepeatedMarks.SourceFractionSigns.Params.real,
         Qrh.JointDetector.RepeatedMarks.FractionArithmetic.Fraction.evalR]))
