/-
# JSP-000093 — edge-disjoint monochromatic triangles in red–blue colourings of complete graphs

**Catalog record** (awards catalog, `JSP-000093`, status *Solved*, Lean proof *No*):

> *How many edge-disjoint monochromatic triangles are guaranteed in a two-coloring of the edges of
> a complete graph?*

Mathematical area: graph theory / Ramsey theory.  Date proposed: no later than 1995.
Publication: `[GrLe20]` V. Gruslys and S. Letzter, *Monochromatic triangle packings in red–blue
graphs*, arXiv:2008.05311 (2020); `[Er97d]` P. Erdős, *Some recent problems and results in graph
theory*, Discrete Math. (1997), 81–85.

## The precise mathematical statement

Goodman's theorem shows that every red–blue colouring of `K_n` contains at least
`n^3 / 24 + o(n^3)` monochromatic triangles.  Erdős asked for the *edge-disjoint* variant and made
the following conjecture (Conjecture 1.1 of `[GrLe20]`, Problem 14 of `[Er97d]`):

> **Conjecture 1.1.**  Every red–blue coloured `K_n` contains `n^2 / 12 + o(n^2)` pairwise
> edge-disjoint monochromatic triangles.

Gruslys and Letzter proved this (Theorem 1.2 of `[GrLe20]`).  The constant `1/12` is optimal:
colouring the edges of `K_n` across a balanced bipartition `A ⊔ B` forces every monochromatic
triangle to lie wholly inside `A` or wholly inside `B`, so any edge-disjoint collection has at most
`(C(|A|,2) + C(|B|,2)) / 3 = n^2/12 - n/6` members.

## This file

* `RedBlue` — a red–blue colouring of the edges of a complete graph on a finite type `V`.
* `RedBlue.IsMono` — the triangle `a b d` is monochromatic.
* `TriPack` — a finite family of triangles, pairwise **edge-disjoint**.
* `TriPack.edgesFinset` — the set of edges covered by such a family; `card_edgesFinset` says the
  family covers exactly `3 |P|` edges.
* `Erdős93` — the machine-checkable restatement of Conjecture 1.1 / Theorem 1.2.

## The companion files

* `JSPProblem/Ramsey.lean` — the `R(3,3) = 6` base case underlying every positive lower bound.
* `JSPProblem/Sharpness.lean` — optimality of the constant `1/12` (`jsp_000093_main`), i.e. the
  upper-bound direction of the conjecture, which is the part that is provable.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Union
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace JSP93

universe u
variable {V : Type u}

/-- **A red–blue colouring of the edges of a complete graph on `V`.**
`col a b` is `true` or `false`; the two side conditions say that the colouring is defined on
unordered pairs. -/
structure RedBlue (V : Type*) where
  /-- the colour of the edge `a b` -/
  col : V → V → Bool
  /-- the colour does not depend on the order of the endpoints -/
  symm : ∀ a b : V, col a b = col b a
  /-- there are no loops -/
  irrefl : ∀ a : V, col a a = false

namespace RedBlue

variable (c : RedBlue V)

/-- **The triangle `a b d` is monochromatic in `c`.** -/
def IsMono (a b d : V) : Prop :=
  c.col a b = c.col a d ∧ c.col a d = c.col b d

theorem isMono_symm {a b d : V} (h : c.IsMono a b d) : c.IsMono b a d := by
  rcases h with ⟨h1, h2⟩
  exact ⟨(c.symm a b).symm.trans (h1.trans h2), h2.symm⟩

end RedBlue

/-- Two oriented edges of a complete graph represent the same *unordered* edge when they are equal
or when one is the reversal of the other. -/
def EdgeEq (e f : V × V) : Prop := e = f ∨ e = f.swap

theorem edgeEq_iff {a b x y : V} :
    EdgeEq (a, b) (x, y) ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  simp [EdgeEq]

/-! ## The three edges of a triangle -/

variable [DecidableEq V]

/-- The `i`-th edge of the triangle `t = (a, b, c)`, kept as an oriented pair. -/
def triEdge (t : V × V × V) : Fin 3 → V × V
  | ⟨0, _⟩ => (t.1, t.2.1)
  | ⟨1, _⟩ => (t.1, t.2.2)
  | ⟨2, _⟩ => (t.2.1, t.2.2)

/-- The three edges of the triangle `t`, kept as oriented pairs. -/
def triEdgesF (t : V × V × V) : Finset (V × V) :=
  (Finset.univ : Finset (Fin 3)).image (triEdge t)

namespace triEdgesF

/-- The three edges of a genuine triangle are pairwise distinct. -/
theorem triEdge_inj (t : V × V × V) (h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
    {i j : Fin 3} (hij : triEdge t i = triEdge t j) : i = j := by
  fin_cases i <;> fin_cases j <;> simp only [triEdge, Prod.mk.injEq] at hij
  · rfl
  · exact absurd hij.2 h.2.1
  · exact absurd hij.1 h.1
  · exact absurd hij.2.symm h.2.1
  · rfl
  · exact absurd hij.1 h.1
  · exact absurd hij.1.symm h.1
  · exact absurd hij.1.symm h.1
  · rfl

/-- A genuine triple of three distinct vertices spans exactly three distinct edges. -/
theorem card (t : V × V × V) (h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2) :
    (triEdgesF t).card = 3 := by
  refine Finset.card_image_iff.mpr ?_
  intro i _ j _ hij
  exact triEdge_inj t h hij

/-- No edge of a genuine triangle is its own reversal. -/
theorem irrefl {t : V × V × V} (h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2) (e : V × V)
    (he : e ∈ triEdgesF t) : e.1 ≠ e.2 := by
  rcases Finset.mem_image.mp he with ⟨i, -, rfl⟩
  fin_cases i <;> simp only [triEdge] <;> first
    | exact h.1
    | exact h.2.1
    | exact h.2.2

/-- No edge of a genuine triangle is the reversal of another edge of the same triangle. -/
theorem triEdge_ne_swap (t : V × V × V) (h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
    (i j : Fin 3) : triEdge t i ≠ Prod.swap (triEdge t j) := by
  fin_cases i <;> fin_cases j <;> simp only [triEdge, Prod.swap, Prod.fst, Prod.snd]
  <;> intro hh
  <;> have hh1 := (Prod.ext_iff.mp hh).1
  <;> have hh2 := (Prod.ext_iff.mp hh).2
  <;> first
    | exact h.1 hh1 | exact h.1 hh1.symm | exact h.1 hh2 | exact h.1 hh2.symm
    | exact h.2.1 hh1 | exact h.2.1 hh1.symm | exact h.2.1 hh2 | exact h.2.1 hh2.symm
    | exact h.2.2 hh1 | exact h.2.2 hh1.symm | exact h.2.2 hh2 | exact h.2.2 hh2.symm

/-- **No two edges of a genuine triangle are reversals of one another.**  Consequently a family of
triangles, even one that is *not* assumed edge-disjoint, never covers an edge together with its
reverse.  This is what makes the unordered (i.e. sharp) edge count recoverable from the oriented
encoding `triEdgesF`. -/
theorem no_swap_pair {t : V × V × V} (h : t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
    {e f : V × V} (he : e ∈ triEdgesF t) (hf : f ∈ triEdgesF t) (hs : e = f.swap) : False := by
  rcases Finset.mem_image.mp he with ⟨i, -, rfl⟩
  rcases Finset.mem_image.mp hf with ⟨j, -, rfl⟩
  exact triEdge_ne_swap t h i j hs

end triEdgesF

/-- **A packing of pairwise edge-disjoint triangles on `V`.**
`fam` is the finite family of vertex triples; `valid` says each triple really is a triangle (three
distinct vertices); `edgeDisj` says that no two distinct triples share an edge. -/
structure TriPack (V : Type*) [DecidableEq V] where
  /-- the family of triangles -/
  fam : Finset (V × V × V)
  /-- every member is a genuine triple of distinct vertices -/
  valid : ∀ t ∈ fam, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2
  /-- distinct members are edge-disjoint -/
  edgeDisj : ∀ t ∈ fam, ∀ u ∈ fam, t ≠ u →
    ∀ e ∈ triEdgesF t, ∀ f ∈ triEdgesF u, ¬ EdgeEq e f

namespace TriPack

variable [DecidableEq V] (P : TriPack V)

/-- **The set of oriented edges covered by `P`.** -/
def edgesFinset : Finset (V × V) := P.fam.biUnion triEdgesF

/-- **`P` is a monochromatic triangle packing for the colouring `c`.** -/
def IsMonoPack (c : RedBlue V) : Prop := ∀ t ∈ P.fam, c.IsMono t.1 t.2.1 t.2.2

end TriPack

/-- **Counting identity.**  Edge-disjoint triangles cover pairwise distinct edges, three per
triangle. -/
theorem card_biUnion_triEdges {W : Type u} [DecidableEq W] (T : Finset (W × W × W))
    (hvalid : ∀ t ∈ T, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
    (hdisj : ∀ t ∈ T, ∀ u ∈ T, t ≠ u →
      ∀ e ∈ triEdgesF t, ∀ f ∈ triEdgesF u, ¬ EdgeEq e f) :
    (T.biUnion triEdgesF).card = 3 * T.card := by
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert t s ht ih =>
      have hvalid' : ∀ u ∈ s, u.1 ≠ u.2.1 ∧ u.2.1 ≠ u.2.2 ∧ u.1 ≠ u.2.2 :=
        fun u hu => hvalid u (Finset.mem_insert_of_mem hu)
      have hdisj' : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
          ∀ e ∈ triEdgesF u, ∀ f ∈ triEdgesF v, ¬ EdgeEq e f :=
        fun u hu v hv huv e he f hf =>
          hdisj u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv e he f hf
      have ih' := ih hvalid' hdisj'
      have hne : ∀ u ∈ s, t ≠ u := by
        intro u hu htu
        subst htu
        exact ht hu
      have hdiscU : Disjoint (triEdgesF t) (s.biUnion triEdgesF) := by
        refine Finset.disjoint_left.2 ?_
        intro e he1 he2
        rcases Finset.mem_biUnion.mp he2 with ⟨u, hu, heu⟩
        exact (hdisj t (Finset.mem_insert_self t s) u (Finset.mem_insert_of_mem hu) (hne u hu)
          e he1 e heu) (Or.inl rfl)
      have hcard : (triEdgesF t).card = 3 :=
        triEdgesF.card t (hvalid t (Finset.mem_insert_self t s))
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdiscU, ih', hcard]
      simp only [Finset.card_insert_of_notMem ht]
      omega

namespace TriPack

variable [DecidableEq V] (P : TriPack V)

/-- **Each triangle of `P` contributes exactly three fresh edges.**  This is the counting identity
that turns a packing into an edge budget. -/
theorem card_edgesFinset : P.edgesFinset.card = 3 * P.fam.card :=
  card_biUnion_triEdges P.fam P.valid fun t ht u hu hne e he f hf => P.edgeDisj t ht u hu hne e he f hf

/-- No edge covered by `P` is its own reversal. -/
theorem irrefl_edgesFinset (e : V × V) (he : e ∈ P.edgesFinset) : e.1 ≠ e.2 := by
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  exact triEdgesF.irrefl (P.valid t ht) e het

/-- **The covered edges and their reversals are disjoint.**  Hence adjoining the reversed copy
doubles the count, which converts the oriented bookkeeping above into a genuine count of
*unordered* edges — and that is the count that yields the sharp constant `1/12`. -/
theorem disjoint_edges_swap :
    Disjoint P.edgesFinset (P.edgesFinset.image Prod.swap) := by
  refine Finset.disjoint_left.2 ?_
  intro e he1 he2
  rcases Finset.mem_image.mp he2 with ⟨f, hf, hsf⟩
  rcases Finset.mem_biUnion.mp he1 with ⟨u, hu, heu⟩
  rcases Finset.mem_biUnion.mp hf with ⟨t, ht, het⟩
  rcases eq_or_ne t u with htu | hne
  · exact triEdgesF.no_swap_pair (P.valid t ht) (htu ▸ heu) het hsf.symm
  · exact (P.edgeDisj u hu t ht hne.symm e heu f het (Or.inr hsf.symm)).elim

/-- **Doubling trick.**  The union of the covered edges with their reversals has exactly twice the
cardinality of `P.edgesFinset`, i.e. exactly `6 · |P|` ordered pairs — the number of *unordered*
edges used by the packing is `3 · |P|`. -/
theorem card_edgesFinset_union_swap :
    (P.edgesFinset ∪ (P.edgesFinset.image Prod.swap)).card = 2 * P.edgesFinset.card := by
  have hsw : (P.edgesFinset.image Prod.swap).card = P.edgesFinset.card :=
    Finset.card_image_of_injective P.edgesFinset
      (fun a b h => Prod.ext_iff.mpr ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩)
  rw [Finset.card_union_of_disjoint P.disjoint_edges_swap, hsw]
  omega

end TriPack

/-! ### The conjecture itself -/

/-- **JSP-000093 = Erdős's conjecture (Conjecture 1.1 of `[GrLe20]`), equivalently the main theorem
(Theorem 1.2) of Gruslys and Letzter.**

Every red–blue colouring of `K_n` contains `n^2 / 12 + o(n^2)` pairwise edge-disjoint monochromatic
triangles.

The `o(n^2)` term is unfolded in the usual way: for every tolerance `ε > 0` there is `N` such that
every colouring of every `K_n` with `n ≥ N` carries a monochromatic triangle packing with at least
`n^2/12 - ε·n^2` members.

The cardinality comparison is made in `ℝ`, hence the explicit casts. -/
def Erdős93 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = n → ∀ c : RedBlue W,
      ∃ P : TriPack W, P.IsMonoPack c ∧ (n : ℝ) ^ 2 / 12 - ε * (n : ℝ) ^ 2 ≤ (P.fam.card : ℝ)

/-- A witness `N` for tolerance `ε` applies to every `n ≥ N`. -/
theorem Erdős93On {ε : ℝ} (_hε : 0 < ε) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = n →
      ∀ c : RedBlue W,
      ∃ P : TriPack W, P.IsMonoPack c ∧ (n : ℝ) ^ 2 / 12 - ε * (n : ℝ) ^ 2 ≤ (P.fam.card : ℝ))
    {n : ℕ} (h : N ≤ n) :
    ∀ (W : Type) [Fintype W] [DecidableEq W], Fintype.card W = n → ∀ c : RedBlue W,
      ∃ P : TriPack W, P.IsMonoPack c ∧ (n : ℝ) ^ 2 / 12 - ε * (n : ℝ) ^ 2 ≤ (P.fam.card : ℝ) :=
  fun W _ _ hW c => hN n h W hW c

-- The optimality (upper-bound) direction of JSP-000093 is the part that is provable; it is
-- formalised in `JSPProblem/Sharpness.lean` as `jsp_000093_main` and `Erdős93Sharp`.

end JSP93
