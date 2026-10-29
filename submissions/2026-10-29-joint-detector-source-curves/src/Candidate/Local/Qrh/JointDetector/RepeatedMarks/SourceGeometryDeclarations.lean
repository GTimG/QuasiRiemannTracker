/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceGeometryMacro
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedGeometryTactic

open Lean
namespace Qrh.JointDetector.RepeatedMarks.SourceGeometryDeclarations

/- This DSL carries only literal term syntax. It performs no data evaluation
and emits the original parameter structures and ordinary geometry proofs. -/
declare_syntax_cat sourceGeometryRow
syntax "(" term "," term "," term "," term ")"
  (" geo_cap(" term ")")? (" geo_floor(" term ")")? : sourceGeometryRow

private def pad (k : Nat) : String :=
  String.ofList (List.replicate (5-k.repr.length) '0') ++ k.repr

private def render (curved : Bool) (start : Nat)
    (initialB initialL initialC phi initialFloor : TSyntax `term)
    (rows : Array (TSyntax `sourceGeometryRow)) : MacroM (TSyntax `command) := do
  let mut parentB := initialB
  let mut parentL := initialL
  let mut parentC := initialC
  let mut floor := initialFloor
  let mut commands := #[]
  for row in rows, offset in [:rows.size] do
    let `(sourceGeometryRow| ($b:term,$l:term,$a:term,$last:term)
        $[geo_cap($cap:term)]? $[geo_floor($newFloor:term)]?) := row
      | Macro.throwErrorAt row "invalid source geometry row"
    let childC := cap.getD parentC
    floor := newFloor.getD floor
    let n := start+offset
    let dn := mkIdent (Name.mkSimple (if curved then s!"p{n}" else s!"stage{pad n}"))
    let tn := mkIdent (Name.mkSimple (if curved then s!"geometry{n}" else s!"geometry{pad n}"))
    let decl ← if curved then
      `(command| noncomputable def $dn : CurvedSourceStep.Params :=
        ⟨$parentB,$parentL,$parentC,$b,$l,$childC,$a,$last⟩)
    else
      `(command| noncomputable def $dn : SourceStep.Params :=
        ⟨$parentB,$parentL,$parentC,$b,$l,$childC,$a,$last⟩)
    let proof ← if curved then
      `(command| theorem $tn : CurvedSourceStep.GeometryCertificate $dn $phi $floor := by
        unfold $dn; curved_geometry)
    else
      `(command| theorem $tn : SourceStep.GeometryCertificate $dn := by
        unfold $dn; source_geometry)
    commands := commands ++ #[decl.raw,proof.raw]
    parentB := b
    parentL := l
    parentC := childC
  return ⟨mkNullNode commands⟩

macro "linear_geometry_block " start:num
    " geo_parent(" b:term "," l:term "," c:term ")"
    " geo_rows[" rows:sourceGeometryRow,* "]" : command => do
  render false start.getNat b l c (← `((0:ℝ))) (← `((0:ℝ))) rows.getElems

macro "curved_geometry_block " start:num
    " geo_parent(" b:term "," l:term "," c:term ")"
    " geo_phi(" phi:term ")" " geo_base_floor(" floor:term ")"
    " geo_rows[" rows:sourceGeometryRow,* "]" : command => do
  render true start.getNat b l c phi floor rows.getElems

end Qrh.JointDetector.RepeatedMarks.SourceGeometryDeclarations
