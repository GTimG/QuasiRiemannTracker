/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
True descriptor repetition on the same supported inverse/ordinary zero pair.
Only prime metadata is repeated; rows, presentation, witness, masks and heights
are inherited unchanged from the original fiber. -/
import Candidate.C092.transport.MediumInversePriceGuards

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorPhysicalSelection HeckeDetectorWitnessRows

def restrictFiber {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (rows : Finset FreeRow) (hrows : rows ⊆ F.rows) (hne : rows.Nonempty) :
    Fiber M H Label Slot U a ε cutoff T allowance i :=
  { F with rows:=rows
           nonempty:=hne
           fixed_label:=fun u hu => F.fixed_label u (hrows hu)
           fixed_left:=fun u hu => F.fixed_left u (hrows hu)
           fixed_right:=fun u hu => F.fixed_right u (hrows hu)
           row_norm:=fun u hu => F.row_norm u (hrows hu)
           row_coeff:=fun u hu => F.row_coeff u (hrows hu)
           fixed_bin:=fun u hu => F.fixed_bin u (hrows hu) }

/-- The administrative total supply is filled with identical copies. A source
call uses only a selected subproduct within its actual rectangular quota. -/
def repeatedFiber {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (slot : Slot) (hslot : slot ∈ F.slots) (K : ℕ)
    (hsupply : (7/37 : ℝ) ≤ (K : ℝ)*F.widths slot) :
    Fiber M H Label (Fin K) U a ε cutoff T allowance i where
  rows:=F.rows
  nonempty:=F.nonempty
  family:=F.family
  witness:=F.witness
  label:=F.label
  left:=F.left
  right:=F.right
  fixed_label:=F.fixed_label
  fixed_left:=F.fixed_left
  fixed_right:=F.fixed_right
  row_norm:=F.row_norm
  rowData:=F.rowData
  reverse:=F.reverse
  row_coeff:=F.row_coeff
  slots:=Finset.univ
  profile:=fun _ => F.profile slot
  upper:=fun _ => F.upper slot
  widths:=fun _ => F.widths slot
  external:=fun _ => F.external slot
  bin:=fun _ => F.bin slot
  mesh:=F.mesh
  binWidth:=F.binWidth
  mesh_nonneg:=F.mesh_nonneg
  binWidth_pos:=F.binWidth_pos
  widths_pos:=fun _ _ => F.widths_pos slot hslot
  widths_mesh:=fun _ _ => F.widths_mesh slot hslot
  supply:=by simpa using hsupply
  fixed_bin:=by
    intro u hu j hj
    exact F.fixed_bin u hu slot hslot

theorem repeated_physical_product {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (slot : Slot) (hslot : slot ∈ F.slots) (K : ℕ)
    (hsupply : (7/37 : ℝ) ≤ (K : ℝ)*F.widths slot)
    (selected : Finset (Fin K)) (u : FreeRow) :
    (repeatedFiber F slot hslot K hsupply).physicalProduct selected u =
      (physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u slot)^selected.card := by
  simp [Fiber.physicalProduct,repeatedFiber,physical]

/-- The same actual inverse spike, multiplied by the repeated actual
attaining mark, gives the full e*k*w count credit. No amplitude-bin average
is substituted for the calibrated maximum e. -/
theorem repeated_inverse_count {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
    {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε cutoff T allowance i)
    (slot : Slot) (hslot : slot ∈ F.slots) (K : ℕ)
    (hsupply : (7/37 : ℝ) ≤ (K : ℝ)*F.widths slot)
    (selected : Finset (Fin K)) (e buffer εm C height : ℝ)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hattain : ∀ u∈F.rows,U^(e*F.widths slot-buffer) ≤
      ‖physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u slot‖^2)
    (hraw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      (∑ u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*(repeatedFiber F slot hslot K hsupply).physicalProduct selected u‖^2) ≤ C*U^(1+εm)) :
    (F.rows.card : ℝ) ≤ (12*(1+height)*C)*
      U^(1-(2*a-1)*F.r-e*((selected.card : ℝ)*F.widths slot)+
        2*ε+(selected.card : ℝ)*buffer+εm) := by
  let G := repeatedFiber F slot hslot K hsupply
  have hUp : 0 < U := zero_lt_one.trans hU
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes F.rows F.family U a ε cutoff T allowance i
    hU (by linarith) (fun u => (F.witness u).toWitness) F.label F.left F.right
    F.fixed_label F.fixed_left F.fixed_right
  have he := HeckeDetectorFiberEnergy.inverse_energy F.rows F.family U a ε cutoff T allowance i
    (by linarith) (fun u => (F.witness u).toWitness) F.label F.inverseProfile (U^F.r)
    (1/4) (9/4) (C*U^(1+εm)) (fun u => G.physicalProduct selected u)
    (Real.rpow_pos_of_pos hUp _) (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) (by positivity) height hh hfreq hraw
  have he' : (∑ u∈F.rows,‖polynomial (F.family u F.label) true F.inverseProfile (U^F.r)
      (F.witness u).zero.re (F.witness u).frequency*G.physicalProduct selected u‖^2) ≤
      (12*(1+height)*C)*U^(1+εm) := by convert he using 1 <;> ring
  have hproduct (u : FreeRow) (hu : u∈F.rows) :
      U^(2*(e/2)*((selected.card : ℝ)*F.widths slot)-(selected.card : ℝ)*buffer) ≤
        ‖G.physicalProduct selected u‖^2 := by
    dsimp only [G]
    rw [repeated_physical_product,norm_pow,←pow_mul]
    have h := pow_le_pow_left₀ (Real.rpow_pos_of_pos hUp _).le (hattain u hu) selected.card
    rw [←Real.rpow_mul_natCast hUp.le] at h
    convert h using 1
    · congr 1
      ring
    · rw [←pow_mul]
      congr 1
      omega
  have hc := HeckeDetectorRowCount.inverse_count F.rows (fun u => F.family u F.label)
    F.inverseProfile (U^F.r) (fun u => (F.witness u).zero.re) (fun u => (F.witness u).frequency)
    (fun u => G.physicalProduct selected u) U (2*a-1) F.r (e/2)
    ((selected.card : ℝ)*F.widths slot) (2*ε) ((selected.card : ℝ)*buffer) εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) hproduct he'
  convert hc using 1 <;> congr 2 <;> ring

#print axioms repeated_inverse_count
end
end QRH.Cycle092.MediumInversePrice
