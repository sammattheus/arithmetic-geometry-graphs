module

public import CayleyProof.TorsionCharacters

@[expose] public section

open scoped BigOperators Classical

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

noncomputable def torsionCharacterGroup (F : Type*) [Field F] [Fintype F]
    (d : ℕ) : Subgroup (MulChar F ℂ) := (powMonoidHom d).ker

theorem powerRange_dual (d : ℕ) :
    (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ
      (powMonoidHom d : Fˣ →* Fˣ).range).ofDual = torsionCharacterGroup F d := by
  ext χ
  rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
  change (∀ u ∈ (powMonoidHom d : Fˣ →* Fˣ).range, χ u = 1) ↔ χ ^ d = 1
  constructor
  · intro h
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow]
    exact h (u ^ d) ⟨u, rfl⟩
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    change χ (↑v ^ d) = 1
    rw [map_pow, ← MulChar.pow_apply_coe, h, MulChar.one_apply_coe]

theorem torsion_character_sum_eq_fiber (d : ℕ) (y : Fˣ) :
    (∑ χ : torsionCharacterGroup F d, χ.val y) =
      (({x : Fˣ | x ^ d = y} : Finset _).card : ℂ) := by
  let H := (powMonoidHom d : Fˣ →* Fˣ).range
  have hdual := powerRange_dual (F := F) d
  have hcard : Nat.card (torsionCharacterGroup F d) =
      Nat.card (powMonoidHom d : Fˣ →* Fˣ).ker := by
    rw [← hdual, MulChar.card_subgroupOrderIsoSubgroupMulChar,
      ← Subgroup.index_eq_card, Subgroup.index_range]
  by_cases hy : y ∈ H
  · have hval : ∀ χ : torsionCharacterGroup F d, χ.val y = 1 := by
      intro χ
      have hm : χ.val ∈ (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ H).ofDual := by
        rw [hdual]; exact χ.property
      exact MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff.mp hm y hy
    simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hf := MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom d : Fˣ →* Fˣ)
      hy (show (1 : Fˣ) ∈ Set.range (powMonoidHom d : Fˣ →* Fˣ) from ⟨1, by simp⟩)
    apply congrArg Nat.cast
    rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact hf.symm
  · have hsep : ∃ χ : torsionCharacterGroup F d, χ.val y ≠ 1 := by
      by_contra! hn
      apply hy
      have hm : y ∈ (MulChar.subgroupOrderIsoSubgroupMulChar F ℂ).symm
          (OrderDual.toDual (torsionCharacterGroup F d)) := by
        rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff]
        exact fun χ hχ => hn ⟨χ, hχ⟩
      simpa only [← hdual, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using hm
    obtain ⟨χ, hχ⟩ := hsep
    have hz : (∑ η : torsionCharacterGroup F d, η.val y) = 0 := by
      apply eq_zero_of_mul_eq_self_left hχ
      rw [Finset.mul_sum]
      exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ (fun η => by simp)
    rw [hz]
    have hf : ({x : Fˣ | x ^ d = y} : Finset _) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hx
      exact hy ⟨x, hx⟩
    simp [hf]

/-- The finite Fourier expansion on the multiplicative group.  This is
proved from mathlib's character duality; it is not a sheaf-theoretic input. -/
theorem sum_over_powers_eq_character_sum (d : ℕ) (f : Fˣ → ℂ) :
    (∑ x : Fˣ, f (x ^ d)) =
      ∑ χ : torsionCharacterGroup F d, ∑ y : Fˣ, χ.val y * f y := by
  classical
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, torsion_character_sum_eq_fiber]
  rw [← Finset.sum_fiberwise Finset.univ (fun x : Fˣ => x ^ d) (fun x => f (x ^ d))]
  apply Finset.sum_congr rfl
  intro y _
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro x hx
  exact congrArg f (Finset.mem_filter.mp hx).2

theorem sum_field_eq_zero_add_units (f : F → ℂ) :
    (∑ x : F, f x) = f 0 + ∑ x : Fˣ, f x := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0]
  congr 1
  exact (Fintype.sum_equiv unitsEquivNeZero (fun x : Fˣ => f x)
    (fun x : {x : F // x ≠ 0} => f x.val) (fun _ => rfl)).symm

theorem gaussSum_eq_sum_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ y * ψ y := by
  rw [gaussSum, sum_field_eq_zero_add_units]
  simp [MulChar.map_zero]

/-- The monomial exponential sum, expanded using all and only nontrivial
d-torsion multiplicative characters.  The zero input and trivial character
cancel; neither is silently omitted. -/
theorem monomial_sum_eq_gauss (d : ℕ) (hd : 0 < d)
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (u : Fˣ) :
    (∑ t : F, ψ ((u : F) * t ^ d)) =
      ∑ χ ∈ nontrivialTorsionCharacters F d, (χ (u : F))⁻¹ * gaussSum χ ψ := by
  let U : Finset (MulChar F ℂ) := {χ | χ ^ d = 1}
  have hU : ∀ χ : MulChar F ℂ, χ ∈ U ↔ χ ∈ torsionCharacterGroup F d := by
    intro χ; simp [U, torsionCharacterGroup, MonoidHom.mem_ker]
  have he : U.erase 1 = nontrivialTorsionCharacters F d := by
    ext χ; simp [U, nontrivialTorsionCharacters, and_comm]
  have h1U : (1 : MulChar F ℂ) ∈ U := by simp [U]
  have hp : ψ.mulShift (u : F) ≠ 1 := AddChar.IsPrimitive.of_ne_one hψ (Units.ne_zero u)
  have hg : (∑ χ ∈ U, gaussSum χ (ψ.mulShift (u : F))) =
      (∑ χ ∈ nontrivialTorsionCharacters F d, gaussSum χ (ψ.mulShift (u : F))) - 1 := by
    rw [← Finset.sum_erase_add U _ h1U, he, gaussSum_one_left hp, sub_eq_add_neg]
  calc
    (∑ t : F, ψ ((u : F) * t ^ d)) =
        1 + ∑ x : Fˣ, ψ ((u : F) * (x : F) ^ d) := by
      rw [sum_field_eq_zero_add_units]
      simp [zero_pow hd.ne']
    _ = 1 + ∑ χ : torsionCharacterGroup F d,
          ∑ y : Fˣ, χ.val y * ψ ((u : F) * y) := by
      congr 1
      exact sum_over_powers_eq_character_sum d (fun y : Fˣ => ψ ((u : F) * y))
    _ = 1 + ∑ χ ∈ U, gaussSum χ (ψ.mulShift (u : F)) := by
      rw [Finset.sum_subtype U hU]
      congr 1
      apply Finset.sum_congr rfl
      intro χ _
      rw [gaussSum_eq_sum_units]
      rfl
    _ = ∑ χ ∈ nontrivialTorsionCharacters F d, gaussSum χ (ψ.mulShift (u : F)) := by
      rw [hg]; ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [gaussSum_mulShift_eq, MulChar.inv_apply_eq_inv']

end CayleyProof
