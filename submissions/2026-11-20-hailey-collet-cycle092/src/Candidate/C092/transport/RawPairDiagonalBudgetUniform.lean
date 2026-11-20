/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual colored allocation and selected-assignment masses for H.5. Native
Sil bounds are used only for nonnegative coefficient majorants. -/
import Candidate.C092.transport.RawPairDiagonalBudgetPrice
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QRH.Cycle092.RawPairDiagonalBudget
noncomputable section
local instance (priority := 2000) diagSubtypeDecEqUniform {κ : Type*} {p : κ→Prop} : DecidableEq (Subtype p) := Classical.decEq _
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open CenteredMomentFirstCanonicalAllowance
open MixedFirstLiveSource MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open QRH.SilDensitySplit.CubeFree.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}



lemma second_diagonal_cost_scaled (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s) (G : Id)
    (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val))
    (η₁ η₂ τ : Character) (t K Z Cz Ct Cc Kslot A : ℝ) (N : ℕ)
    (hJ : ∀B,Fintype.card (Js B)≤N)
    (hW : ∀B,slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤Z^(1/1000:ℝ))
    (hK : 0≤K) (hZ : 1<Z) (hCz : 0≤Cz) (hCt : 0≤Ct)
    (hcard : ((actualAllocations (tuplePools s) G).card:ℝ)^2≤Cc*Z^(1/1000:ℝ))
    (hCc : 0≤Cc) (hN : Fintype.card ι≤N) (hKs : 1≤Kslot) (hM : ∀i,s.M i≤Kslot)
    (hA : profileCap s^2≤A) :
    secondDiagonalCost s hb cover G Js η₁ η₂ τ t K Z Cz Ct ≤
      (Cc*shapeConstant N*(Kslot^N)^4)*A*Z^(3/1000:ℝ)*
        (Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hprod := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.prodM_le s Kslot N hN hM hKs
  have hp0 := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.prodM_ge s
  have hp := pow_le_pow_left₀ (zero_le_one.trans hp0) hprod 4
  have hA0 : 0≤A := (sq_nonneg _).trans hA
  have hbase := second_diagonal_cost_le s hb cover G Js η₁ η₂ τ t K Z Cz Ct (Z^(1/1000:ℝ)) N hJ hW hK hz.le hCz hCt
  apply hbase.trans
  calc
    _ ≤ (Cc*Z^(1/1000:ℝ))*shapeConstant N*(Kslot^N)^4*(Z^(1/1000:ℝ))^2*A*
        (Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) := by
      have := shapeConstant_nonneg N
      gcongr
    _ = _ := by
      rw [←Real.rpow_mul_natCast hz.le]
      have he : Z^(1/1000:ℝ)*Z^((1/1000:ℝ)*2)=Z^(3/1000:ℝ) := by rw [←Real.rpow_add hz];norm_num
      calc
        _ = (Cc*shapeConstant N*(Kslot^N)^4)*A*(Z^(1/1000:ℝ)*Z^((1/1000:ℝ)*2))*
          (Cz*K*Z^(93/100:ℝ)+Ct*Z^(-22:ℝ)) := by ring
        _ = _ := by rw [he]

/-- The complete numerical zero+discarded ledger is paid by an arbitrarily
prescribed positive share of the TRUE balanced source budget. The only lower
source requirement is explicit and genuine, V^-1<=Z^2. -/
theorem uniform_second_diagonal_share (N : ℕ) (Kslot Cz Ct θ : ℝ)
    (hKs : 1≤Kslot) (hCz : 0≤Cz) (hCt : 0≤Ct) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧
    ∀ (s : Source ι a b),Fintype.card ι≤N → (∀i,s.M i≤Kslot) →
    ∀ (hb : 0≤b) (cover : OriginalEnclosure s) (G opp : Id),G≠0 → opp≠0 →
    (G.absNorm:ℝ)≤Z^(8:ℝ) → (opp.absNorm:ℝ)≤Z^(8:ℝ) → (sourceVolume s)⁻¹≤Z^(2:ℝ) →
    ∀ (Js : ∀B:actualAllocations (tuplePools s) G,Finset (liveIndices B.val)),
    (∀B,slotWidth (allocatedLiveSource s hb cover G B) (Js B)≤Z^(1/1000:ℝ)) →
    ∀ (η₁ η₂ τ : Character) (t K A loss : ℝ),0≤K → profileCap s^2≤A → 0≤loss →
    K≤4*Z^(1/1000:ℝ)*balancedCore s τ G opp/Z →
    secondDiagonalCost s hb cover G Js η₁ η₂ τ t K Z Cz Ct ≤
      θ*balancedBudget s τ G opp A Z loss := by
  obtain ⟨Cc,hCc,hcount⟩ := MixedSourceAssembly.genuine_count_squared (N+2) (1/8000) (by norm_num)
  let M := Cc*shapeConstant N*(Kslot^N)^4
  have hM : 0≤M := by dsimp [M];have := shapeConstant_nonneg N;positivity
  have hz := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.absorb_scaled
    (4*M*Cz) (-33/500) 0 (θ/2) (half_pos hθ) (by norm_num)
  have ht := QRH.SilDensitySplit.CubeFree.Second.ProviderDiag.absorb_scaled
    (M*Ct) (-1997/1000) 0 (θ/2) (half_pos hθ) (by norm_num)
  filter_upwards [hz,ht,eventually_gt_atTop (1:ℝ)] with Z hz ht hZ
  refine ⟨hZ,?_⟩
  intro s hN hmarks hb cover G opp hG hopp hNG hNO hV Js hW η₁ η₂ τ t K A loss hK hA hloss hcore
  have hcard0 : Fintype.card (ι⊕Fin 2)≤N+2 := by rw [Fintype.card_sum,Fintype.card_fin];omega
  have hcard := hcount hcard0 (tuplePools s) G hG
  have hpow : (G.absNorm:ℝ)^(1/8000:ℝ)≤Z^(1/1000:ℝ) := by
    calc
      _ ≤ (Z^(8:ℝ))^(1/8000:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hNG (by norm_num)
      _ = _ := by rw [←Real.rpow_mul (zero_lt_one.trans hZ).le];norm_num
  have hcard' := hcard.trans (mul_le_mul_of_nonneg_left hpow hCc.le)
  have hJ (B : actualAllocations (tuplePools s) G) : Fintype.card (Js B)≤N := by
    exact (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans hN)
  have hscaled := second_diagonal_cost_scaled s hb cover G Js η₁ η₂ τ t K Z Cz Ct Cc Kslot A N
    hJ hW hK hZ hCz hCt hcard' hCc.le hN hKs hmarks hA
  have hlog : 1≤Real.log Z+1 := by have := Real.log_nonneg hZ.le;linarith
  have hzero : 4*M*Cz*Z^(-33/500:ℝ)≤θ/2 := by
    norm_num only [Real.rpow_zero,mul_one] at hz ⊢
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity : 0≤4*M*Cz) hlog) (by positivity)).trans hz
  have htail : M*Ct*Z^(-1997/1000:ℝ)≤θ/2 := by
    norm_num only [Real.rpow_zero,mul_one] at ht ⊢
    exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity : 0≤M*Ct) hlog) (by positivity)).trans ht
  exact hscaled.trans (coarse_price_of_core s τ G opp hG hopp A Z loss K M Cz Ct θ hZ
    ((sq_nonneg _).trans hA) hloss hK hM hCz hCt hV hNG hNO hcore hzero htail)
end
end QRH.Cycle092.RawPairDiagonalBudget
#print axioms QRH.Cycle092.RawPairDiagonalBudget.uniform_second_diagonal_share
