module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic

/-!
The moment-curve graph, using mathlib's `SimpleGraph.addCayley`.

Coordinates are indexed by `Fin s`, with exponents `i.val + 1`.
The generator set is exactly the union of the nonzero moment curve
and its negative. No spectral or geometric conclusion is assumed here.
-/

@[expose] public section

namespace CayleyProof

variable {F : Type*} [Field F] {s : ℕ}

def curve (s : ℕ) (t : F) : Fin s → F := fun i => t ^ (i.val + 1)

def generators (F : Type*) [Field F] (s : ℕ) : Set (Fin s → F) :=
  {v | ∃ t : F, t ≠ 0 ∧ (v = curve s t ∨ v = -curve s t)}

def curveGraph (F : Type*) [Field F] (s : ℕ) : SimpleGraph (Fin s → F) :=
  SimpleGraph.addCayley (generators F s)

noncomputable instance : DecidableRel (curveGraph F s).Adj := Classical.decRel _

@[simp] theorem curve_zero : curve s (0 : F) = 0 := by
  ext i
  simp [curve]

theorem curve_injective (hs : 0 < s) : Function.Injective (curve s (F := F)) := by
  intro t u h
  have h₀ := congrFun h ⟨0, hs⟩
  simpa [curve] using h₀

@[simp] theorem curve_eq_zero (hs : 0 < s) (t : F) : curve s t = 0 ↔ t = 0 := by
  constructor
  · intro h
    exact curve_injective hs (h.trans curve_zero.symm)
  · rintro rfl
    exact curve_zero

theorem curve_ne_neg_curve (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    {t u : F} (ht : t ≠ 0) : curve s t ≠ -curve s u := by
  intro h
  have h₁ : t = -u := by simpa [curve] using congrFun h ⟨0, by omega⟩
  have h₂ : t ^ 2 = -(u ^ 2) := by simpa [curve] using congrFun h ⟨1, by omega⟩
  have ht₂ : t ^ 2 = u ^ 2 := by rw [h₁]; ring
  have hu₂ : (2 : F) * u ^ 2 = 0 := by linear_combination h₂ - ht₂
  have hu : u = 0 := (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    ((mul_eq_zero.mp hu₂).resolve_left hchar)
  exact ht (by simpa [hu] using h₁)

@[simp] theorem neg_mem_generators (v : Fin s → F) :
    -v ∈ generators F s ↔ v ∈ generators F s := by
  constructor <;> rintro ⟨t, ht, h | h⟩
  · exact ⟨t, ht, Or.inr (by simpa using congrArg Neg.neg h)⟩
  · exact ⟨t, ht, Or.inl (by simpa using congrArg Neg.neg h)⟩
  · exact ⟨t, ht, Or.inr (by rw [h])⟩
  · exact ⟨t, ht, Or.inl (by rw [h]; simp)⟩

theorem zero_not_mem_generators (hs : 0 < s) :
    (0 : Fin s → F) ∉ generators F s := by
  rintro ⟨t, ht, h | h⟩
  · exact ht ((curve_eq_zero hs t).mp h.symm)
  · exact ht ((curve_eq_zero hs t).mp (neg_eq_zero.mp h.symm))

theorem curveGraph_adj (hs : 0 < s) (v w : Fin s → F) :
    (curveGraph F s).Adj v w ↔ w - v ∈ generators F s := by
  rw [curveGraph, SimpleGraph.addCayley_adj]
  simp only [← sub_eq_neg_add]
  have hneg : v - w ∈ generators F s ↔ w - v ∈ generators F s := by
    rw [← neg_sub w v, neg_mem_generators]
  rw [hneg, or_self]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    exact zero_not_mem_generators hs (by simpa using h)

/-- Translation is an automorphism of the actual graph. -/
def translation (a : Fin s → F) : curveGraph F s ≃g curveGraph F s where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := by
    intro v w
    exact SimpleGraph.addCayley_adj_add_iff_right

/-- Explicit vertex transitivity, without defining a second graph structure. -/
theorem vertex_transitive (v w : Fin s → F) :
    ∃ e : curveGraph F s ≃g curveGraph F s, e v = w := by
  refine ⟨translation (w - v), ?_⟩
  change w - v + v = w
  exact sub_add_cancel w v

omit [Field F] in
theorem card_vertices [Fintype F] :
    Fintype.card (Fin s → F) = Fintype.card F ^ s := by simp

/-- The sign and nonzero parameter give a unique generator. -/
def signedGenerator (z : Bool × {t : F // t ≠ 0}) : generators F s :=
  ⟨if z.1 then curve s z.2.val else -curve s z.2.val, by
    refine ⟨z.2.val, z.2.property, ?_⟩
    cases z.1 <;> simp⟩

theorem signedGenerator_bijective (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0) :
    Function.Bijective (signedGenerator (F := F) (s := s)) := by
  constructor
  · rintro ⟨b, t⟩ ⟨c, u⟩ h
    have hv := congrArg Subtype.val h
    cases b <;> cases c <;> simp only [signedGenerator, Bool.false_eq_true,
      ↓reduceIte] at hv
    · have htu := curve_injective (by omega : 0 < s) (neg_injective hv)
      exact Prod.ext rfl (Subtype.ext htu)
    · exact False.elim (curve_ne_neg_curve hs hchar u.property hv.symm)
    · exact False.elim (curve_ne_neg_curve hs hchar t.property hv)
    · have htu := curve_injective (by omega : 0 < s) hv
      exact Prod.ext rfl (Subtype.ext htu)
  · rintro ⟨v, t, ht, h | h⟩
    · exact ⟨(true, ⟨t, ht⟩), Subtype.ext h.symm⟩
    · exact ⟨(false, ⟨t, ht⟩), Subtype.ext h.symm⟩

/-- Translation identifies the generator set with any vertex's neighbors. -/
def generatorNeighborEquiv (hs : 0 < s) (v : Fin s → F) :
    generators F s ≃ (curveGraph F s).neighborSet v where
  toFun z := ⟨v + z.val, (curveGraph_adj hs v _).mpr (by simpa only [add_sub_cancel_left] using z.property)⟩
  invFun w := ⟨w.val - v, (curveGraph_adj hs v w.val).mp w.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

@[simp] theorem generatorNeighborEquiv_apply_val (hs : 0 < s)
    (v : Fin s → F) (z : generators F s) :
    (generatorNeighborEquiv hs v z).val = v + z.val := rfl

theorem degree_curveGraph [Fintype F] (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    (v : Fin s → F) : (curveGraph F s).degree v = 2 * (Fintype.card F - 1) := by
  classical
  let e := (Equiv.ofBijective (signedGenerator (F := F) (s := s))
    (signedGenerator_bijective hs hchar)).trans (generatorNeighborEquiv (by omega) v)
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Fintype.card_congr e]
  simp

theorem parameter_inequalities (k : ℕ) (hk : 5 ≤ k) :
    3 ≤ k / 2 + 1 ∧ k / 2 + 1 ≤ k - 2 ∧ k < 2 * (k / 2 + 1) := by
  omega

end CayleyProof
