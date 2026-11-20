/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite original-row coverage by the true band/label/dyad dictionaries.
No class is filled into a ball and no new physical row is introduced. -/
import Candidate.C092.transport.TerminalActualRowMedium
import Candidate.C092.transport.TerminalActualRowProfiles
import Candidate.C092.transport.WitnessRowSupActualReindex
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorWitnessRows HeckeDetectorSupportedWitness

/-- Bounded buffered i,k and the authentic ordinary/inverse dyad labels. -/
abbrev TicketKey (Label : Type*) (I K L : ℕ) :=
  Fin (I+1)×Fin (K+1)×Label×Fin L×Fin L

def classRows {Key : Type*} [DecidableEq Key] (rows : Finset FreeRow)
    (key : rows→Key) (tag : Key) : Finset FreeRow :=
  ((Finset.univ : Finset rows).filter (fun u=> key u=tag)).image Subtype.val

theorem classRows_mem {Key : Type*} [DecidableEq Key] (rows : Finset FreeRow)
    (key : rows→Key) (tag : Key) (u : FreeRow) :
    u∈classRows rows key tag ↔ ∃hu : u∈rows,key ⟨u,hu⟩=tag := by
  simp only [classRows,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v.property,hv⟩
  · rintro ⟨hu,hkey⟩
    exact ⟨⟨u,hu⟩,hkey,rfl⟩

theorem classRows_subset {Key : Type*} [DecidableEq Key] (rows : Finset FreeRow)
    (key : rows→Key) (tag : Key) : classRows rows key tag⊆rows := by
  intro u hu
  exact ((classRows_mem rows key tag u).mp hu).choose

theorem original_rows_coverage {Key : Type*} [Fintype Key] [DecidableEq Key]
    (rows : Finset FreeRow) (key : rows→Key) :
    (Finset.univ.biUnion (classRows rows key))=rows := by
  ext u
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,classRows_mem]
  constructor
  · rintro ⟨tag,hu,_⟩;exact hu
  · intro hu;exact ⟨key ⟨u,hu⟩,hu,rfl⟩

/-- Exact finite sum decomposition on the original retained rows, including
empty classes and without multiplicity. Applies directly to physical energy. -/
theorem original_sum_partition {Key : Type*} [Fintype Key] [DecidableEq Key]
    (rows : Finset FreeRow) (key : rows→Key) (f : FreeRow→ℝ) :
    (∑u∈rows,f u)=∑tag : Key,∑u : rows,if key u=tag then f u.val else 0 := by
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact Finset.sum_coe_sort rows f |>.symm

/-- On one true key class the witness labels and BOTH dyads are frozen.
Hence its actual r,m are the literal common logarithmic dyad lengths. -/
theorem witness_key_lengths {Label : Type*} [DecidableEq Label]
    (rows : Finset FreeRow) (chi : FreeRow→Label→Character)
    (U a epsilon cutoff T allowance : ℝ) (i : ℕ)
    (ws : ∀u : rows,SupportedWitness (chi u.val) U a epsilon cutoff T allowance i)
    (hU : 1< U) (label : Label) (left right : Fin (dyadicLength U))
    (u : rows) (hkey : ((ws u).label,(ws u).left,(ws u).right)=(label,left,right)) :
    (ws u).label=label ∧
    (ws u).r=Real.logb U ((2:ℝ)^left.val) ∧
    (ws u).m=Real.logb U ((2:ℝ)^right.val) ∧
    cutoff-(ws u).r-epsilon≤(ws u).m ∧
    (ws u).r≤ cutoff+epsilon ∧ 0≤(ws u).m ∧ (ws u).m≤1/2+75*epsilon := by
  have hl:=congrArg Prod.fst hkey
  have hleft:=congrArg (fun p : Label×Fin (dyadicLength U)×Fin (dyadicLength U)=> p.2.1) hkey
  have hright:=congrArg (fun p : Label×Fin (dyadicLength U)×Fin (dyadicLength U)=> p.2.2) hkey
  dsimp only at hl hleft hright
  exact ⟨hl,(ws u).toWitness.left_exponent hU |>.trans (by rw [hleft]),
    (ws u).toWitness.right_exponent hU |>.trans (by rw [hright]),
    (ws u).product_length_lower,(ws u).inverse_length_upper,(ws u).plain_length_lower,(ws u).plain_length_upper⟩

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.original_rows_coverage
#print axioms QRH.Cycle092.TerminalActualRow.original_sum_partition
#print axioms QRH.Cycle092.TerminalActualRow.witness_key_lengths
