module

public import CayleyProof.CurveGraph
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-! The combinatorial conclusion of the power-sum argument.

The hypothesis `hrep` below is explicitly a hypothesis, not a black-boxed
version of Cohen's theorem. The Newton/Cohen derivation of `hrep` is still
a separate obligation. Extended graph distance avoids any convention that
assigns distance zero to disconnected pairs.
-/

@[expose] public section

namespace CayleyProof

/-- The distance power, using extended distance to exclude disconnected pairs. -/
def distancePower {V : Type*} (G : SimpleGraph V) (k : ℕ) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.edist x y ≤ k
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [G.edist_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- The manuscript's `k`-independence number. -/
noncomputable def kIndepNum {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  (distancePower G k).indepNum

theorem distancePower_eq_top_of_ediam_le {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hdiam : G.ediam ≤ k) : distancePower G k = ⊤ := by
  ext x y
  simp only [distancePower, SimpleGraph.top_adj]
  exact and_iff_left (G.edist_le_ediam.trans hdiam)

theorem kIndepNum_eq_one_of_ediam_le {V : Type*} [Nonempty V] [Finite V]
    (G : SimpleGraph V) {k : ℕ} (hdiam : G.ediam ≤ k) : kIndepNum G k = 1 := by
  rw [kIndepNum, distancePower_eq_top_of_ediam_le G hdiam,
    ← SimpleGraph.cliqueNum_compl]
  simp [SimpleGraph.cliqueNum_bot]

variable {F : Type*} [Field F] {s : ℕ}

theorem edist_curve_step (hs : 0 < s) (x : Fin s → F) (t : F) :
    (curveGraph F s).edist x (x + curve s t) ≤ 1 := by
  by_cases ht : t = 0
  · simp [ht]
  · apply (SimpleGraph.edist_le_one_iff_adj_or_eq).mpr
    left
    apply (curveGraph_adj hs _ _).mpr
    simpa using (show curve s t ∈ generators F s from ⟨t, ht, Or.inl rfl⟩)

theorem edist_sum_curve (hs : 0 < s) (ts : List F) (x : Fin s → F) :
    (curveGraph F s).edist x (x + (ts.map (curve s)).sum) ≤ ts.length := by
  induction ts generalizing x with
  | nil => simp
  | cons t ts ih =>
    calc
      (curveGraph F s).edist x (x + ((t :: ts).map (curve s)).sum)
          ≤ (curveGraph F s).edist x (x + curve s t) +
            (curveGraph F s).edist (x + curve s t)
              (x + ((t :: ts).map (curve s)).sum) := SimpleGraph.edist_triangle
      _ ≤ 1 + (ts.length : ℕ∞) := by
        apply add_le_add (edist_curve_step hs x t)
        simpa [List.sum_cons, add_assoc] using ih (x + curve s t)
      _ = ((t :: ts).length : ℕ∞) := by simp [add_comm]

theorem ediam_le_of_curve_representations (hs : 0 < s) (k : ℕ)
    (hrep : ∀ x : Fin s → F, ∃ ts : List F,
      ts.length ≤ k ∧ (ts.map (curve s)).sum = x) :
    (curveGraph F s).ediam ≤ k := by
  apply SimpleGraph.ediam_le_of_edist_le
  intro x y
  obtain ⟨ts, hlen, hsum⟩ := hrep (y - x)
  have h := edist_sum_curve hs ts x
  rw [hsum, add_sub_cancel] at h
  exact h.trans (by exact_mod_cast hlen)

theorem kIndepNum_eq_one_of_curve_representations [Fintype F] (hs : 0 < s) (k : ℕ)
    (hrep : ∀ x : Fin s → F, ∃ ts : List F,
      ts.length ≤ k ∧ (ts.map (curve s)).sum = x) :
    kIndepNum (curveGraph F s) k = 1 :=
  kIndepNum_eq_one_of_ediam_le _ (ediam_le_of_curve_representations hs k hrep)

/-- No two distinct vertices can lie in a `k`-independent set. -/
theorem k_independent_subsingleton_of_ediam_le {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hdiam : G.ediam ≤ k) {S : Set V}
    (hS : S.Pairwise (fun x y => (k : ℕ∞) < G.edist x y)) : S.Subsingleton := by
  intro x hx y hy
  by_contra hne
  exact (not_lt_of_ge (G.edist_le_ediam.trans hdiam)) (hS hx hy hne)

end CayleyProof
