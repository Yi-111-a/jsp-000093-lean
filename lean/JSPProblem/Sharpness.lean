/-
# JSP-000093 — the constant `1/12` in Erdős's conjecture is optimal

`JSPProblem/Definitions.lean` records the conjecture `Erdős93` (Gruslys–Letzter, `[GrLe20]`,
Theorem 1.2):

> every red–blue colouring of `K_n` packs `n^2/12 + o(n^2)` pairwise edge-disjoint monochromatic
> triangles.

The *lower* bound `≥ n^2/12 - o(n^2)` is the deep, research-level half of the result.  The
*upper* bound — that no larger constant can possibly hold — is elementary and is what this file
proves, in the strongest machine-checkable form:

> **`jsp_000093_main`.**  Let `A ⊔ (V \ A)` be a balanced bipartition of the vertex set of `K_n`
> (`n` even), colour the edges inside the parts red and the edges across blue.  Then every
> edge-disjoint monochromatic triangle packing `P` satisfies
> `12 · |P| ≤ n^2`, i.e. `|P| ≤ n^2/12`.

Together with the conjecture this pins the extremal packing density of `K_n` to `1/12`.

## Why the construction works

In the bipartition colouring every monochromatic triangle with three distinct vertices lies wholly
inside one part (`JSP93.mono_inside`).  A packing inside a part of size `m` consists of pairwise
edge-disjoint triangles of the complete graph on that part, so its `3` edges per triangle are
distinct even up to reversal (`JSP93.TriPack.disjoint_edges_swap`); hence it uses at most `m^2/2` of
the `m^2` ordered vertex pairs.  Adding the two parts gives `6|P| ≤ |A|^2 + |Aᶜ|^2`
(`JSP93.packing_card_le`), i.e. `|P| ≤ (|A|^2 + |Aᶜ|^2)/6`; for a balanced bipartition this is
exactly `n^2/12`.
-/

import JSPProblem.Definitions

set_option maxHeartbeats 800000

namespace JSP93

universe u
variable {V : Type u} [DecidableEq V]

/-! ## The bipartition colouring -/

/-- `x` and `y` fall into the same part of the bipartition `A ⊔ V \ A`. -/
def SamePart (A : Finset V) (x y : V) : Prop := (x ∈ A ∧ y ∈ A) ∨ (x ∉ A ∧ y ∉ A)

namespace SamePart

theorem symm' {A : Finset V} {x y : V} (h : SamePart A x y) : SamePart A y x := by
  rcases h with h | h
  · exact Or.inl ⟨h.2, h.1⟩
  · exact Or.inr ⟨h.2, h.1⟩

theorem trans' {A : Finset V} {x y z : V} (h1 : SamePart A x y) (h2 : SamePart A y z) :
    SamePart A x z := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ⟨h1.1, h2.2⟩
  · exact absurd h1.2 h2.1
  · exact absurd h2.1 h1.2
  · exact Or.inr ⟨h1.1, h2.2⟩

theorem of_mem {A : Finset V} {x y : V} (hx : x ∈ A) (hy : y ∈ A) : SamePart A x y :=
  Or.inl ⟨hx, hy⟩

theorem of_not_mem {A : Finset V} {x y : V} (hx : x ∉ A) (hy : y ∉ A) : SamePart A x y :=
  Or.inr ⟨hx, hy⟩

/-- If `x` is in the part `A` and shares its part with `y`, then so is `y`. -/
theorem eq_mem {A : Finset V} {x y : V} (hx : x ∈ A) (h : SamePart A x y) : y ∈ A := by
  rcases h with h | h
  · exact h.2
  · exact (h.1 hx).elim

/-- If `x` is outside the part `A` and shares its part with `y`, then so is `y`. -/
theorem eq_not_mem {A : Finset V} {x y : V} (hx : x ∉ A) (h : SamePart A x y) : y ∉ A := by
  rcases h with h | h
  · exact absurd h.1 hx
  · exact h.2

/-- With only two parts available, three vertices cannot be pairwise in different parts. -/
theorem pairwise_diff_false {A : Finset V} {x y z : V}
    (h1 : ¬ SamePart A x y) (h2 : ¬ SamePart A x z) (h3 : ¬ SamePart A y z) : False := by
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ A
    · exact h1 (of_mem hx hy)
    · by_cases hz : z ∈ A
      · exact h2 (of_mem hx hz)
      · exact h3 (of_not_mem hy hz)
  · by_cases hy : y ∈ A
    · by_cases hz : z ∈ A
      · exact h3 (of_mem hy hz)
      · exact h2 (of_not_mem hx hz)
    · by_cases hz : z ∈ A
      · exact h1 (of_not_mem hx hy)
      · exact h1 (of_not_mem hx hy)

end SamePart

instance instDecidableSamePart (A : Finset V) (x y : V) : Decidable (SamePart A x y) := by
  unfold SamePart
  infer_instance

/-- Colour of the edge `x y` for the bipartition `A ⊔ V \ A`: red inside a part, blue across. -/
def bipCol (A : Finset V) (x y : V) : Bool :=
  if x = y then false else decide (SamePart A x y)

theorem bipCol_irrefl (A : Finset V) (x : V) : bipCol A x x = false := by
  unfold bipCol
  rw [if_pos rfl]

theorem bipCol_symm (A : Finset V) (x y : V) : bipCol A x y = bipCol A y x := by
  by_cases h : x = y
  · subst h
    rfl
  · unfold bipCol
    rw [if_neg h, if_neg (Ne.symm h)]
    have hs : SamePart A y x = SamePart A x y := by
      apply propext
      constructor
      · intro h
        rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inl ⟨hy, hx⟩
        · exact Or.inr ⟨hy, hx⟩
      · intro h
        rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inl ⟨hy, hx⟩
        · exact Or.inr ⟨hy, hx⟩
    simp only [hs]

theorem bipCol_eq_true_iff {A : Finset V} {x y : V} (h : x ≠ y) :
    bipCol A x y = true ↔ SamePart A x y := by
  unfold bipCol
  rw [if_neg h]
  simp only [decide_eq_true_eq]

theorem bipCol_eq_false_iff {A : Finset V} {x y : V} (h : x ≠ y) :
    bipCol A x y = false ↔ ¬ SamePart A x y := by
  unfold bipCol
  rw [if_neg h]
  simp only [decide_eq_false_iff_not]

/-- **The two-colouring of `K_V` induced by a bipartition**: red inside a part, blue across. -/
def Bipartite (A : Finset V) : RedBlue V where
  col := bipCol A
  symm := bipCol_symm A
  irrefl := bipCol_irrefl A

/-- **Structural fact.**  In the bipartition colouring, a monochromatic triangle on three distinct
vertices lies entirely inside one of the two parts. -/
theorem mono_inside (A : Finset V) {a b d : V}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (h : (Bipartite A).IsMono a b d) :
    (a ∈ A ∧ b ∈ A ∧ d ∈ A) ∨ (a ∉ A ∧ b ∉ A ∧ d ∉ A) := by
  rcases h with ⟨h1, h2⟩
  by_cases hk : bipCol A a b = true
  · have hp : bipCol A a d = true := h1.symm.trans hk
    have hq : bipCol A b d = true := h2.symm.trans hp
    have spab : SamePart A a b := (bipCol_eq_true_iff hab).mp hk
    have spad : SamePart A a d := (bipCol_eq_true_iff had).mp hp
    by_cases hx : a ∈ A
    · left
      exact ⟨hx, SamePart.eq_mem hx spab, SamePart.eq_mem hx spad⟩
    · right
      exact ⟨hx, SamePart.eq_not_mem hx spab, SamePart.eq_not_mem hx spad⟩
  · have hk' : bipCol A a b = false := Bool.eq_false_of_not_eq_true hk
    have hp : bipCol A a d = false := h1.symm.trans hk'
    have hq : bipCol A b d = false := h2.symm.trans hp
    exact (SamePart.pairwise_diff_false ((bipCol_eq_false_iff hab).mp hk')
      ((bipCol_eq_false_iff had).mp hp) ((bipCol_eq_false_iff hbd).mp hq)).elim

/-! ## Counting the triangles that live inside one part -/

/-- The set of ordered pairs of vertices lying in `A`; it has `|A|^2` elements. -/
def partPairs (A : Finset V) : Finset (V × V) := A ×ˢ A

theorem card_partPairs (A : Finset V) : (partPairs A).card = A.card * A.card :=
  Finset.card_product _ _

namespace TriPack

variable {W : Type u} [DecidableEq W]

/-- The members of `P.fam` whose three vertices all lie in `A`. -/
def famInside (P : TriPack W) (A : Finset W) : Finset (W × W × W) :=
  P.fam.filter fun t => t.1 ∈ A ∧ t.2.1 ∈ A ∧ t.2.2 ∈ A

/-- The members of `P.fam` whose three vertices all lie outside `A`. -/
def famOutside (P : TriPack W) (A : Finset W) : Finset (W × W × W) :=
  P.fam.filter fun t => t.1 ∉ A ∧ t.2.1 ∉ A ∧ t.2.2 ∉ A

/-- The two families are disjoint. -/
theorem inside_outside_disjoint (P : TriPack W) (A : Finset W) :
    Disjoint (P.famInside A) (P.famOutside A) := by
  refine Finset.disjoint_left.2 ?_
  intro t ht1 ht2
  exact ((Finset.mem_filter.mp ht2).2.1 ((Finset.mem_filter.mp ht1).2.1)).elim

/-- Every member of a monochromatic packing for the bipartition colouring lies in one of the two
families, so the family splits. -/
theorem fam_eq_union_inside_outside {P : TriPack W} {A : Finset W}
    (hmono : P.IsMonoPack (Bipartite A)) :
    P.fam = P.famInside A ∪ P.famOutside A := by
  refine Finset.ext fun t => ?_
  rw [Finset.mem_union]
  constructor
  · intro ht
    have hv := P.valid t ht
    rcases mono_inside A hv.1 hv.2.2 hv.2.1 (hmono t ht) with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨ht, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨ht, h⟩)
  · intro h
    rcases h with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1

/-- The members of `famInside A` are genuine triangles and pairwise edge-disjoint. -/
theorem famInside_edgeDisj (P : TriPack W) (A : Finset W) :
    (∀ t ∈ P.famInside A, t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2) ∧
      (∀ t ∈ P.famInside A, ∀ u ∈ P.famInside A, t ≠ u →
        ∀ e ∈ triEdgesF t, ∀ f ∈ triEdgesF u, ¬ EdgeEq e f) := by
  refine ⟨fun t ht => P.valid t ((Finset.mem_filter.mp ht).1), ?_⟩
  intro t ht u hu hne e he f hf
  exact P.edgeDisj t ((Finset.mem_filter.mp ht).1) u ((Finset.mem_filter.mp hu).1) hne e he f hf

/-- The three edges of each inside-triangle give `3 · |famInside A|` distinct ordered pairs. -/
theorem card_edges_inside (P : TriPack W) (A : Finset W) :
    ((P.famInside A).biUnion triEdgesF).card = 3 * (P.famInside A).card :=
  card_biUnion_triEdges _ (famInside_edgeDisj P A).1 (famInside_edgeDisj P A).2

/-- Every edge of an inside-triangle has both endpoints in `A`. -/
theorem biUnion_inside_subset (P : TriPack W) (A : Finset W) :
    ∀ e ∈ (P.famInside A).biUnion triEdgesF, e ∈ partPairs A := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨t, ht, het⟩
  obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp ht).2
  rcases Finset.mem_image.mp het with ⟨i, -, rfl⟩
  fin_cases i <;> simp only [triEdge, partPairs, Finset.mem_product] <;> first
    | exact ⟨h1, h2⟩
    | exact ⟨h1, h3⟩
    | exact ⟨h2, h3⟩

/-- Each ordered pair is used at most once, even up to reversal. -/
theorem biUnion_inside_disjoint_swap (P : TriPack W) (A : Finset W) :
    Disjoint ((P.famInside A).biUnion triEdgesF)
      (((P.famInside A).biUnion triEdgesF).image Prod.swap) := by
  refine Finset.disjoint_left.2 ?_
  intro e he1 he2
  rcases Finset.mem_image.mp he2 with ⟨f, hf, hsf⟩
  rcases Finset.mem_biUnion.mp he1 with ⟨t, ht, het⟩
  rcases Finset.mem_biUnion.mp hf with ⟨u, hu, heu⟩
  have htv : t ∈ P.fam := (Finset.mem_filter.mp ht).1
  have huv : u ∈ P.fam := (Finset.mem_filter.mp hu).1
  rcases eq_or_ne t u with htu | hne
  · exact triEdgesF.no_swap_pair (P.valid t htv) het (htu ▸ heu) hsf.symm
  · exact (P.edgeDisj t htv u huv hne e het f heu (Or.inr hsf.symm)).elim

/-- **The inside-tiling bound.**  `6 · |famInside A| ≤ |A|²`. -/
theorem six_mul_famInside_le (P : TriPack W) (A : Finset W) :
    6 * (P.famInside A).card ≤ A.card * A.card := by
  have hsub : ∀ f ∈ (P.famInside A).biUnion triEdgesF, f ∈ partPairs A :=
    biUnion_inside_subset P A
  have hsubsw : ∀ e ∈ ((P.famInside A).biUnion triEdgesF).image Prod.swap, e ∈ partPairs A := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨g, hg, rfl⟩
    have h := Finset.mem_product.mp (hsub g hg)
    apply Finset.mem_product.mpr
    exact ⟨h.2, h.1⟩
  have hunion : ((P.famInside A).biUnion triEdgesF)
      ∪ (((P.famInside A).biUnion triEdgesF).image Prod.swap) ⊆ partPairs A :=
    Finset.union_subset (fun _ hf => hsub _ hf) (fun _ hf => hsubsw _ hf)
  have hcard : (((P.famInside A).biUnion triEdgesF)
      ∪ (((P.famInside A).biUnion triEdgesF).image Prod.swap)).card
      = 2 * ((P.famInside A).biUnion triEdgesF).card := by
    rw [Finset.card_union_of_disjoint (biUnion_inside_disjoint_swap P A),
      Finset.card_image_of_injective ((P.famInside A).biUnion triEdgesF)
        (fun a b h => Prod.ext_iff.mpr ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩)]
    ring
  have hle : (((P.famInside A).biUnion triEdgesF)
      ∪ (((P.famInside A).biUnion triEdgesF).image Prod.swap)).card ≤ (partPairs A).card :=
    Finset.card_le_card hunion
  rw [hcard, card_partPairs, card_edges_inside P A] at hle
  omega

end TriPack

/-! ## The headline theorem -/

/-- **Upper bound for the bipartition colouring.**  Every monochromatic triangle packing for the
bipartition colouring of `K` with parts `A` and `V \ A` satisfies
`6·|P| ≤ |A|² + |V \ A|²`. -/
theorem packing_card_le [Fintype V] {P : TriPack V} {A : Finset V}
    (hmono : P.IsMonoPack (Bipartite A)) :
    6 * (P.fam.card : ℕ) ≤ A.card * A.card +
      (Fintype.card V - A.card) * (Fintype.card V - A.card) := by
  set Ac : Finset V := Finset.univ \ A with hAc
  have hfam : P.fam = P.famInside A ∪ P.famOutside A := P.fam_eq_union_inside_outside hmono
  have hfamcard : P.fam.card = (P.famInside A).card + (P.famOutside A).card := by
    rw [hfam, Finset.card_union_of_disjoint (P.inside_outside_disjoint A)]
  have hAc_card : Ac.card = Fintype.card V - A.card := by
    rw [hAc, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]
  have hout : P.famOutside A = P.famInside Ac := by
    refine Finset.ext fun t => ?_
    simp only [TriPack.famOutside, TriPack.famInside, Finset.mem_filter, hAc, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
  have h2a : 6 * (P.famOutside A).card
      ≤ (Fintype.card V - A.card) * (Fintype.card V - A.card) := by
    rw [hout, ← hAc_card]
    exact P.six_mul_famInside_le Ac
  have hsplit : 6 * P.fam.card
      = 6 * (P.famInside A).card + 6 * (P.famOutside A).card := by
    rw [hfamcard]
    omega
  rw [hsplit]
  exact Nat.add_le_add (P.six_mul_famInside_le A) h2a

/-- **JSP-000093, optimality direction: the `1/12` constant cannot be improved.**

Let `V` have `n` vertices, let `n` be even, and let `A ⊔ (V \ A)` be a balanced bipartition.  In the
bipartition colouring of `K_n` every edge-disjoint monochromatic triangle packing `P` satisfies

`12 · |P| ≤ n²`,  i.e.  `|P| ≤ n²/12`.

Consequently no theorem of the shape "every two-colouring of `K_n` packs `c·n²` edge-disjoint
monochromatic triangles" can hold with `c > 1/12`; combined with `Erdős93` this pins the extremal
packing density of `K_n` to `1/12`. -/
theorem jsp_000093_main (n : ℕ) (V : Type u) [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = n) (A : Finset V) (hA : 2 * A.card = n) :
    ∀ P : TriPack V, P.IsMonoPack (Bipartite A) → (P.fam.card : ℝ) * 12 ≤ (n : ℝ) ^ 2 := by
  intro P hmono
  have h6 := packing_card_le (V := V) hmono
  rw [hV] at h6
  have hAc : A.card ≤ n := by omega
  have h6R : 6 * (P.fam.card : ℝ) ≤ (A.card : ℝ) * (A.card : ℝ)
      + ((n - A.card : ℕ) : ℝ) * ((n - A.card : ℕ) : ℝ) := by
    exact_mod_cast h6
  have hAR : 2 * (A.card : ℝ) = (n : ℝ) := by exact_mod_cast hA
  have hdR : ((n - A.card : ℕ) : ℝ) = (n : ℝ) - (A.card : ℝ) := by
    rw [Nat.cast_sub hAc]
  rw [hdR] at h6R
  nlinarith

/-- **The optimality statement, packaged.**  For every `c > 1/12` and every even `n ≥ 2` the balanced
bipartition colouring of `K_n` admits no edge-disjoint monochromatic triangle packing of `c·n²`
members.  So `1/12` is the largest constant that can possibly appear in the conjecture
`Erdős93`. -/
theorem Erdős93Sharp (c : ℝ) (hc : 1 / 12 < c) (n : ℕ) (hn : 2 ≤ n) (V : Type u)
    [Fintype V] [DecidableEq V] (hV : Fintype.card V = n) (A : Finset V) (hA : 2 * A.card = n) :
    ∀ P : TriPack V, P.IsMonoPack (Bipartite A) → ¬ (c * (n : ℝ) ^ 2 ≤ (P.fam.card : ℝ)) := by
  intro P hmono
  intro hc'
  have h12 := jsp_000093_main n V hV A hA P hmono
  have hnn : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hkey : (n : ℝ) ^ 2 * c ≤ (n : ℝ) ^ 2 * (1 / 12) := by
    nlinarith [hc']
  have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnn
  have : c ≤ 1 / 12 := le_of_mul_le_mul_left hkey hpos
  linarith

end JSP93
