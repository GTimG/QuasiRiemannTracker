/- Repeated marks: source validity of a node of the final graph.

`SourceValidC` is Collet's `SourceValid` (Record1252270103Finite/SourceFormulas.lean,
Apache-2.0) with the six HIGH facet gates of a HIGH parent replaced by the trivial gate `1`: the
scalar gates, the weak guard and the three special sectors are kept verbatim and in the same
positions, so every positional use of the LOW side carries over. The HIGH gate of the
repeated-mark gain is certified separately by `HighValid` (Finite/HighGate.lean). -/
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.UniformMargins
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.HighGate
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Finite
open Record1252270103Finite

def densityGate2 (n low : Source) (high : Option Source) (b ν : ℚ) (j : Fin 9) : ℚ :=
  match high with
  | none => densityGate n low none b ν j
  | some h => if j.val < 6 then 1 else densityGate n low (some h) b ν j

/-- Collet's `scalarGate` (Record1252270103Finite/SourceFormulas.lean, Apache-2.0) at the natural
cost `9/2`: the reference length `Lref = 49/100 - K b` and gate 10 carry the natural cost. -/
def scalarGate92 (n low : Source) (b : ℚ) (j : Fin 16) : ℚ :=
 let a := sourceA n low b
 let t := sourceT n b
 let T := t+b
 let F := sourceF n low b
 let e := n.allowance
 let Lref := 49/100-(9/2)*b
 ![sourceDen n low,b-2*e,a,1/75-a,F-T/2-4*e,
 low.B*F-t-b-4*e,1-n.q*low.cap,
 n.lowFee-(n.q*low.B/low.L+n.q*low.cap+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(9/2)*b-10*e,
 5/6+(499/1000)*Lref-T-9*a-n.highFee,
 1-T-5*a-n.highFee,1-1/50-T-4*a-n.highFee,
 1-1/50-T-(9/2)*a-n.highFee,Lref-7*a-n.highFee] j

theorem sourceScalarReal_rat92 (n low:Source) (b:ℚ) (j:Fin 16) :
 sourceScalarReal (9/2) n low (b:ℝ) j=(scalarGate92 n low b j:ℝ) := by
 fin_cases j <;> simp [sourceScalarReal,scalarGate92,sourceAReal_rat,sourceTReal_rat,sourceFReal_rat] <;> ring

/-- Collet's source validity with the six HIGH facets of a HIGH parent left to `HighValid`. -/
def SourceValidC (n low : Source) (high : Option Source) : Prop :=
 0<n.B ∧ n.B≤1 ∧ 1<n.L ∧ 0≤n.cap ∧ n.cap<1 ∧
 1/2≤n.q ∧ n.q≤3/4 ∧ n.L<low.L ∧
 0≤crossing n low ∧ crossing n low≤n.cap ∧ crossing n low≤low.cap ∧
 (∀ h ∈ high, 22/23≤h.B ∧ h.B≤1 ∧ 1<h.L ∧ 0≤h.cap ∧ h.cap<1) ∧
 (∀ b ∈ [crossing n low,n.cap],
  (∀ j : Fin 16, 0<scalarGate92 n low b j) ∧ 0≤weakCap n low b ∧
  ∀ j : Fin 9, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate2 n low high b ν j) n.q (3/4) i)

instance (n low : Source) (high : Option Source) : Decidable (SourceValidC n low high) := by
  unfold SourceValidC; infer_instance

/-- The cell condition of the common-width payment (Lemma C): `2S ≤ F` at both endpoints. -/
def CellRatio (n low : Source) : Prop :=
  ∀ b ∈ [crossing n low, n.cap], 2*(b - 2*n.allowance) ≤ sourceF n low b - n.allowance

instance (n low : Source) : Decidable (CellRatio n low) := by unfold CellRatio; infer_instance

/-- Validity of a step of the repeated-mark source chain (`copies = 8`). The HIGH gate enters through
its positivity on the cell (`HighPos`); a finite node proves it from Bernstein trees
(`highPos_of_valid`), a family of nodes from polynomial certificates (`Faceless`). -/
def SourceValid2 (n low : Source) (high : Option Source) : Prop :=
  SourceValidC n low high ∧ HighPos n low high 8 ∧ n.q < 3/4 ∧ CellRatio n low

/-- The gates a sector or natural facet uses are unchanged. -/
def KeptGate (high : Option Source) (j : Fin 9) : Prop := high = none ∨ 6 ≤ j.val

theorem densityGate2_kept (n low : Source) (high : Option Source) (b ν : ℚ) (j : Fin 9)
    (hj : KeptGate high j) : densityGate2 n low high b ν j = densityGate n low high b ν j := by
  cases high with
  | none => rfl
  | some h =>
    rcases hj with hj | hj
    · exact absurd hj (by simp)
    · simp only [densityGate2]
      rw [if_neg (by omega)]

theorem sourceC_density_endpoint_positive (n low : Source) (high : Option Source)
    (hv : SourceValidC n low high) {b : ℚ} (hb : b ∈ [crossing n low, n.cap]) {ν : ℝ}
    (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) (j : Fin 9) (hj : KeptGate high j) :
    0 < sourceDensityWidthReal n low high (b:ℝ) ν j := by
  have hq := hv.2.2.2.2.2.2.1
  have hcert := hv.2.2.2.2.2.2.2.2.2.2.2.2 b hb
  rw [sourceDensityWidthReal_rat, source_density_cubic_identity]
  apply cubic_cast_positive_closed _ hq (by simpa using hν)
  intro i
  have h := hcert.2.2 j i
  have he : (fun ν => densityGate2 n low high b ν j) = (fun ν => densityGate n low high b ν j) := by
    funext ν; exact densityGate2_kept n low high b ν j hj
  rw [he] at h
  exact h

theorem sourceC_full_width_gates (n low : Source) (high : Option Source)
    (hv : SourceValidC n low high) {b ν : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
    (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) :
    (∀ j, 0 < sourceScalarReal (9/2) n low b j) ∧
    0 ≤ sourceWeakReal n low b ∧
    ∀ j, KeptGate high j → 0 < sourceDensityWidthReal n low high b ν j := by
  have hleft := hv.2.2.2.2.2.2.2.2.2.2.2.2 (crossing n low) (by simp)
  have hright := hv.2.2.2.2.2.2.2.2.2.2.2.2 n.cap (by simp)
  constructor
  · intro j
    apply width_affine_positive (sourceScalarReal_affine (9/2) n low j) hb
    · rw [sourceScalarReal_rat92]
      exact_mod_cast hleft.1 j
    · rw [sourceScalarReal_rat92]
      exact_mod_cast hright.1 j
  constructor
  · apply width_affine_nonnegative (sourceWeakReal_affine n low) hb
    · rw [sourceWeakReal_rat]
      exact_mod_cast hleft.2.1
    · rw [sourceWeakReal_rat]
      exact_mod_cast hright.2.1
  · intro j hj
    apply width_affine_positive (sourceDensityWidthReal_affine n low high ν j) hb
    · exact sourceC_density_endpoint_positive n low high hv (by simp) hν j hj
    · exact sourceC_density_endpoint_positive n low high hv (by simp) hν j hj

/-- A single positive slack for the kept gates, uniform in the width and the density. -/
theorem nfC_uniform_margin (n low : Source) (high : Option Source)
    (hv : SourceValidC n low high) :
    ∃δ : ℝ,0<δ ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),
      (∀j,δ≤sourceScalarReal (9/2) n low b j) ∧
      0≤sourceWeakReal n low b ∧
      ∀j, KeptGate high j → δ≤sourceDensityWidthReal n low high b ν j := by
  classical
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ Set.Icc (n.q:ℝ) (3/4:ℝ)
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δs,hδs,hs⟩:=QRH.Record1252270103StepScalar.compact_finite_margin D hD
    (fun j : Fin 16=>fun x : ℝ×ℝ=>sourceScalarReal (9/2) n low x.1 j)
    (fun j=>(QRH.Record1252270103StepScalar.continuous_source_scalar _ n low j).continuousOn)
    (fun j x hx=>(sourceC_full_width_gates n low high hv hx.1 hx.2).1 j)
  let keep := {j : Fin 9 // KeptGate high j}
  obtain ⟨δd,hδd,hd⟩:=QRH.Record1252270103StepScalar.compact_finite_margin D hD
    (fun j : keep=>fun x : ℝ×ℝ=>sourceDensityWidthReal n low high x.1 x.2 j.1)
    (fun j=>(QRH.Record1252270103StepScalar.continuous_source_density n low high j.1).continuousOn)
    (fun j x hx=>(sourceC_full_width_gates n low high hv hx.1 hx.2).2.2 j.1 j.2)
  refine ⟨min δs δd,lt_min hδs hδd,?_⟩
  intro b hb ν hν
  exact ⟨fun j=>(min_le_left _ _).trans (hs j (b,ν) ⟨hb,hν⟩),
    (sourceC_full_width_gates n low high hv hb hν).2.1,
    fun j hj=>(min_le_right _ _).trans (hd ⟨j,hj⟩ (b,ν) ⟨hb,hν⟩)⟩

/-- `2S ≤ F` on the whole cell. -/
theorem cell_ratio_full (n low : Source) (hc : CellRatio n low) {b : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) :
    2*(b - 2*(n.allowance:ℝ)) ≤ sourceFReal n low b - (n.allowance:ℝ) := by
  have hl := hc (crossing n low) (by simp)
  have hr := hc n.cap (by simp)
  have haff : WidthAffine (fun b : ℝ => sourceFReal n low b - (n.allowance:ℝ) - 2*(b - 2*(n.allowance:ℝ))) := by
    intro x y t
    have := sourceFReal_affine n low x y t
    simp only at this ⊢
    rw [this]; ring
  have hf (c : ℚ) (hc' : 2*(c - 2*n.allowance) ≤ sourceF n low c - n.allowance) :
      0 ≤ sourceFReal n low (c:ℝ) - (n.allowance:ℝ) - 2*((c:ℝ) - 2*(n.allowance:ℝ)) := by
    rw [sourceFReal_rat]
    have hh : ((2*(c - 2*n.allowance) : ℚ) : ℝ) ≤ ((sourceF n low c - n.allowance : ℚ) : ℝ) := by
      exact_mod_cast hc'
    push_cast at hh
    linarith
  have := width_affine_nonnegative haff hb (hf _ hl) (hf _ hr)
  linarith

end QRH.RepeatedMarks.Finite
