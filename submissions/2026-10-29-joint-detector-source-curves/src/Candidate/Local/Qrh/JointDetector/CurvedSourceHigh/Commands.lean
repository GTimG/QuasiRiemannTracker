/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Assembly

open Lean
namespace Qrh.JointDetector.CurvedSourceHigh

/-- Compact source syntax for the exact, kernel-checked stage composition.
The command only expands proof declarations; it reads no external data. -/
macro "curved_stage" geo:ident frac:ident number:num index:num kind:num mode:num r:term : command => do
  let n := number.getNat
  let k := kind.getNat
  let m := mode.getNat
  if k < 1 || 3 < k || 1 < m || (m == 0 && k != 1) then
    Macro.throwError "unsupported curved cell layout"
  let suffix := toString n
  let localId (s : String) := mkIdent (Name.mkSimple (s ++ suffix))
  let remoteId (ns : Name) (s : String) := mkIdent (ns ++ Name.mkSimple (s ++ suffix))
  let gp := remoteId geo.getId.eraseMacroScopes "p"
  let gg := remoteId geo.getId.eraseMacroScopes "geometry"
  let fp := remoteId frac.getId.eraseMacroScopes "p"
  let fr := remoteId frac.getId.eraseMacroScopes "ray"
  let fb := remoteId frac.getId.eraseMacroScopes "bank"
  let fs := remoteId frac.getId.eraseMacroScopes "signs"
  let params := mkIdent (frac.getId.eraseMacroScopes ++ `params)
  let b := mkIdent (frac.getId.eraseMacroScopes ++ `b)
  let bv := mkIdent (frac.getId.eraseMacroScopes ++ `bValues)
  let rays := mkIdent (frac.getId.eraseMacroScopes ++ `rays)
  let rn := localId "ray"
  let pn := localId "params_real"
  let rr := localId "ray_real"
  let ln := localId "layout"
  let cn := localId "cells"
  let sn := localId "stage"
  let flag ← if m == 1 then `(term| true) else `(term| false)
  let early ← if k == 3 then `(term| true) else `(term| false)
  let floor ← if m == 1 then `(term| (50001/100000:ℝ)) else `(term| (2/5:ℝ))
  let ray ← if k == 2 then
      `(term| RepeatedMarks.CurvedSourceStep.amplitudeFloor /
        RepeatedMarks.CurvedSourceStep.matchedCut $gp sourcePhi 0)
    else if m == 0 then `(term| (1:ℝ)) else pure r
  let factory := mkIdent (`Qrh.JointDetector.RepeatedMarks.CurvedSourceStep ++
    Name.mkSimple (if k == 1 then "oneCell" else if k == 2 then "twoCells" else "threeCells"))
  let builder := mkIdent (`Qrh.JointDetector.CurvedSourceHigh ++
    Name.mkSimple (if k == 1 then "stage_ray" else if k == 2 then "stage_two" else "stage_three"))
  let layout ← if k == 1 then `(term| RayLayout $gp $rn $flag)
    else `(term| ClipLayout $gp $floor $rn $early)
  let rayProof ← if k == 2 then `(tacticSeq|
      change (CurvedSourceFractions.clippedRay $fp).evalR = $rn
      rw [eval_clippedRay, $pn:term]
      rfl)
    else `(tacticSeq|
      dsimp only [$fr:term, $rays:term]
      norm_num [$rn:term,RepeatedMarks.FractionArithmetic.Fraction.evalR])
  let c1 ← `(command| noncomputable def $rn : ℝ := $ray)
  let c2 ← `(command|
    theorem $pn : RepeatedMarks.FractionCurveData.Params.toReal $fp = $gp := by
      norm_num [RepeatedMarks.FractionCurveData.Params.toReal,$fp:term,$params:term,$b:term,$bv:term,$gp:term,
        CurvedSourceFractions.point,CurvedSourceFractions.slope,CurvedSourceFractions.cap,
        RepeatedMarks.FractionArithmetic.Fraction.evalR])
  let c3 ← `(command|
    theorem $rr : RepeatedMarks.FractionArithmetic.Fraction.evalR $fr = $rn := by
      $rayProof:tacticSeq)
  let c4 ← `(command|
    theorem $ln : $layout := by
      unfold $rn $gp
      curved_layout)
  let c5 ← `(command| noncomputable def $cn := $factory $gp sourcePhi $rn)
  let c6 ← `(command|
    theorem $sn : RepeatedMarks.CurvedSourceStep.StageHighCertificate
        $gp sourcePhi $floor $rn $flag $cn := by
      simpa only [$cn:term] using
        $builder $gg $ln $fp $fr $pn $rr
          (by simpa only [$fb:term] using $fs))
  return ⟨mkNullNode #[c1.raw,c2.raw,c3.raw,c4.raw,c5.raw,c6.raw]⟩

end Qrh.JointDetector.CurvedSourceHigh
