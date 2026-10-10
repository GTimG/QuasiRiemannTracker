import WeightedQRH.RowConductor
import OAI.NumberTheory.DirichletL.PrimeRows.RowCount
import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
import OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource

/-! A fixed reflection presentation for each actual physical row. The same
combined conductor is used both in coefficient damping and in reflection. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace WeightedQRH.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

structure PhysicalReflectionData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) where
  presentation : Character
  primitive : Character
  phase : ℂ
  element_eq : ∀n:O,elementCoeff (rowCharacter S hS u) n=elementCoeff presentation n
  inverse_eq : ∀J:Ideal O,idealCoeff (rowCharacter S hS u).inverse J=idealCoeff presentation.inverse J
  phase_norm : ‖phase‖=1
  conductor_bound : primitive.modulus.absNorm*(redundantIdeal presentation.modulus primitive.modulus).absNorm≤
    fixedConductorConstant S*(Ideal.span {u.val}:Ideal O).radical.absNorm
  split : ∀(G:𝓢(ℝ,ℂ))(X R:ℝ),0<X→
    HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0=
      phase*(retainedSchwartz presentation primitive G X R+discardedSchwartz presentation primitive G X R)

theorem physical_reflection_data_exists (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue≠1) : Nonempty (PhysicalReflectionData S hS u) := by
  obtain ⟨τ,ψ,g,he,hi,hnτ,hp,hnp,hg,hτ,hcap,hdef,hsplit⟩ := RowConductor.row_original_split S hS u hn
  exact ⟨⟨τ,ψ,g,he,hi,hg,hcap.trans hτ,hsplit⟩⟩

namespace PhysicalReflectionData
variable {S : Finset (Ideal O)} {hS : ∀P∈S,Prime P} {u : FreeRow}

def combinedConductor (D : PhysicalReflectionData S hS u) : ℝ :=
  (D.primitive.modulus.absNorm:ℝ)*(redundantIdeal D.presentation.modulus D.primitive.modulus).absNorm

theorem combined_pos (D : PhysicalReflectionData S hS u) : 0<D.combinedConductor :=
  RowConductor.reflected_scale_pos D.presentation D.primitive

theorem combined_le_radical (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).radical.absNorm := by
  unfold combinedConductor
  exact_mod_cast D.conductor_bound

theorem radical_le_row (u : FreeRow) :
    (Ideal.span {u.val}:Ideal O).radical.absNorm≤(Ideal.span {u.val}:Ideal O).absNorm := by
  letI : Finite (O ⧸ (Ideal.span {u.val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
  exact FiniteConductor.absNorm_le_of_le (show (Ideal.span {u.val}:Ideal O)≤(Ideal.span {u.val}:Ideal O).radical from Ideal.le_radical)

theorem combined_le_row (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*rowNorm u := by
  exact D.combined_le_radical.trans (mul_le_mul_of_nonneg_left
    (by unfold rowNorm;exact_mod_cast radical_le_row u) (Nat.cast_nonneg _))

theorem redundant_le_combined (D : PhysicalReflectionData S hS u) :
    (Ideal.absNorm (∏P∈sourcePrimes D.presentation D.primitive,P):ℝ)≤D.combinedConductor := by
  have hp : (1:ℝ)≤D.primitive.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr D.primitive.modulus_ne_bot)
  exact le_mul_of_one_le_left (by positivity) hp

end PhysicalReflectionData

/-- A coefficient dilation bound gives the exact reflected length without
charging the redundant primes or repeated-prime conductor deficit twice. -/
theorem combined_scale_of_dilation (Cu Ccond Nu N Y U y v : ℝ)
    (hC : 0<Ccond) (hNu : 0<Nu) (hN : 0<N) (hU : 0<U)
    (hNuU : Nu≤U) (hY : Y=U^y)
    (hdilation : max 1 (Cu*N/(Ccond*Nu))≤U^v) :
    Cu≤Ccond*U^(1-y+v)*(Y/N) := by
  have hd := (le_max_right 1 (Cu*N/(Ccond*Nu))).trans hdilation
  have hm : Cu*N≤U^v*(Ccond*Nu) := (div_le_iff₀ (mul_pos hC hNu)).mp hd
  have hmul : Cu*N≤Ccond*U^(1+v) := by
    calc
      _ ≤ U^v*(Ccond*Nu) := hm
      _ ≤ U^v*(Ccond*U) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNuU hC.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one];ring
  rw [hY,←mul_div_assoc,le_div_iff₀ hN]
  apply hmul.trans_eq
  rw [mul_assoc,←Real.rpow_add hU]
  congr 2
  ring

end WeightedQRH.Numerator
end
