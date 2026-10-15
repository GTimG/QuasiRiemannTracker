import Candidate.Cycle62.Physical.InitialMass.SecondChildCaps
import Candidate.Cycle62.Physical.InitialMass.SecondRetainedAssembly

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstScale
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O

/-- Cancel the first selected ideal before taking a uniform puncture cap.
This keeps the source exponent independent of the slot count. -/
theorem actual_common_child_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤b)(hbs : 1≤bs)
    (s : Input ι)(hcard : Fintype.card ι≤N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(hC : C≠0)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (E : Ideal O)(hE : (E.absNorm:ℝ)≤sourceRadius (child s C R B χ t)) :
    ((R*C*E).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  have hc : 0<(C.absNorm:ℝ) := norm_pos C hC
  have h := (le_div_iff₀ hc).mp (hE.trans
    (actual_common_child_source_cap N b bs hb hbs s hcard he C R B χ t hne))
  have hr := mul_le_mul_of_nonneg_left h (show 0≤(R.absNorm:ℝ) by positivity)
  simpa only [map_mul,Nat.cast_mul,mul_assoc,mul_comm,mul_left_comm] using hr

/-- Both literal selected ideals in every second block have the same cap;
the choice of reflection introduces no additional source exponent. -/
theorem actual_second_block_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤b)(hbs : 1≤bs)
    (s : Input ι)(hcard : Fintype.card ι≤N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(hC : C≠0)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K T Z ξ : ℝ)(hK : 0<K)
    (q : ActualSecondBlockIndex (child s C R B χ t) (R*C) seed K T Z ξ)
    (reflected : Bool) :
    let d:=actualSecondBlockDatum (liveIndices B.val) (child s C R B χ t)
      (R*C) seed hseed hz₁ hz₂ K T Z ξ hK q
    (((R*C)*(if reflected then d.D else d.C)).absNorm:ℝ)≤
      (R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  intro d
  have hg:=actual_retained_block_gates (liveIndices B.val) (child s C R B χ t)
    (R*C) seed hseed hz₁ hz₂ K T Z ξ hK q
  apply actual_common_child_puncture_cap N b bs hb hbs s hcard he C R hC B χ t hne
  cases reflected
  · exact hg.2.2.1
  · exact hg.2.2.2

/-- The extracted prime power cancels together with the first selected
ideal. All prime powers are retained until this exact cancellation. -/
theorem actual_twice_child_puncture_cap {ι : Type*}[Fintype ι]
    (N : ℕ)(b bs : ℝ)(hb : 1≤b)(hbs : 1≤bs)
    (s : Input ι)(hcard : Fintype.card ι≤N)(he : Endpoints b bs bs s)
    (C R : Ideal O)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O)(hQ : Q≠0)(k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B χ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B χ t).pools (Q^k))
    (υ : Character)(v : ℝ)(E : Ideal O)
    (hE : (E.absNorm:ℝ)≤sourceRadius (twiceChild s C R B χ t Q k Bp υ v)) :
    ((((R*C)*(Q^k))*E).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b bs bs*volume s := by
  have hc : 0<(C.absNorm:ℝ) := norm_pos C (allocation_ne s C B)
  have hq : 0<(Q.absNorm:ℝ) := norm_pos Q hQ
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos hc (pow_pos hq k)
  have hh:=hE.trans (twice_caps N b bs bs hb hbs hbs s hcard he C R B χ t hne Q hQ k hslot Bp υ v).2.2.2
  rw [←mul_div_assoc] at hh
  have hp := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mp hh)
    (show 0≤(R.absNorm:ℝ) by positivity)
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,mul_assoc,mul_comm,mul_left_comm] using hp

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_common_child_puncture_cap
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_second_block_puncture_cap
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_twice_child_puncture_cap
