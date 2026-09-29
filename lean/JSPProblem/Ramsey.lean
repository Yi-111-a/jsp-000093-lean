/-
# JSP-000093 — the base case `R(3,3) = 6` underlying every positive lower bound

`JSPProblem/Definitions.lean` restates Erdős's conjecture (`Erdős93`): every red–blue colouring of
`K_n` packs `n^2/12 + o(n^2)` pairwise edge-disjoint monochromatic triangles.

Nothing can be said about the *asymptotic* constant without first settling that a single
monochromatic triangle exists at all.  This file proves the classical Erdős–Szekeres fact

> **`R(3,3) = 6`.**  Every two-colouring of the edges of a complete graph on at least six vertices
> contains a monochromatic triangle,

and derives the packing-level consequence

> every two-colouring of `K_n`, `n ≥ 6`, has an edge-disjoint monochromatic triangle packing of
> cardinality `≥ 1`.
-/

import JSPProblem.Definitions

set_option maxHeartbeats 800000

namespace JSP93

universe u
variable {V : Type u} [DecidableEq V]

/-! ## Small finset combinatorics -/

/-- A `Finset` of cardinality at least `3` contains three pairwise distinct elements. -/
theorem three_of_card_ge_three {S : Finset V} (h : 3 ≤ S.card) :
    ∃ a b d : V, a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ b ≠ d ∧ a ≠ d := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show (0 : ℕ) < S.card by omega)
  have hSa : 2 ≤ (S.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show (0 : ℕ) < (S.erase a).card by omega)
  have hSab : 1 ≤ ((S.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb]
    omega
  obtain ⟨e, he⟩ :=
    Finset.card_pos.mp (show (0 : ℕ) < ((S.erase a).erase b).card by omega)
  obtain ⟨hbne, hbS⟩ := Finset.mem_erase.mp hb
  obtain ⟨heb, heSa⟩ := Finset.mem_erase.mp he
  obtain ⟨hea, heS⟩ := Finset.mem_erase.mp heSa
  refine ⟨a, b, e, ha, hbS, heS, ?_, ?_, ?_⟩
  · exact Ne.symm hbne
  · exact Ne.symm heb
  · exact Ne.symm hea

/-- `a ∈ s.erase b` forces `a ≠ b`. -/
theorem ne_of_mem_erase' {s : Finset V} {a b : V} (h : a ∈ s.erase b) : a ≠ b :=
  (Finset.mem_erase.mp h).1

/-- A member of a filtered copy of `s` differs from every element that was removed from `s`. -/
theorem ne_of_mem_filter_erase {s : Finset V} {p : V → Prop} [DecidablePred p] {a b : V}
    (h : a ∈ s.filter p) (hb : b ∉ s) : a ≠ b := by
  have hmem : a ∈ s := (Finset.mem_filter.mp h).1
  intro hab
  exact hb (hab ▸ hmem)

/-- **Pigeonhole at a vertex.**  The two colour classes at a vertex partition the neighbourhood.  If
the vertex has at least five neighbours, three of them send the *same* colour to that vertex.  This
is the first step of the classical proof of `R(3,3) = 6`. -/
theorem three_same_colour (c : RedBlue V) (v : V) (nb : Finset V) (hnb : 5 ≤ nb.card) :
    (3 ≤ (nb.filter fun x => c.col v x = true).card ∧
        ∀ x ∈ nb.filter fun x => c.col v x = true, c.col v x = true) ∨
    (3 ≤ (nb.filter fun x => ¬ c.col v x = true).card ∧
        ∀ x ∈ nb.filter fun x => ¬ c.col v x = true, c.col v x = false) := by
  set R := nb.filter fun x => c.col v x = true with hR
  set B := nb.filter fun x => ¬ c.col v x = true with hB
  have hsplit : nb = R ∪ B := by
    refine Finset.ext fun x => ?_
    simp only [Finset.mem_filter, Finset.mem_union, hR, hB]
    constructor
    · intro hx
      by_cases h : c.col v x = true
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, fun h2 => h h2⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
  have hdisj : Disjoint R B := by
    refine Finset.disjoint_left.2 ?_
    intro x hxR hxB
    exact ((Finset.mem_filter.mp hxB).2 (Finset.mem_filter.mp hxR).2)
  have hcard : R.card + B.card = nb.card := by
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
  by_cases h3 : 3 ≤ R.card
  · exact Or.inl ⟨h3, fun x hx => (Finset.mem_filter.mp hx).2⟩
  refine Or.inr ⟨by omega, fun x hx => ?_⟩
  exact Bool.eq_false_of_not_eq_true (Finset.mem_filter.mp hx).2

/-- Two different `Bool`s differ by complementation. -/
theorem Bool.ne_eq_not {b k : Bool} (h : b ≠ k) : b = !k := by
  cases b <;> cases k <;> simp_all

/-- **The second step of the proof of `R(3,3) = 6`.**  If `a`, `b`, `d` are three vertices joined to
`v` in the same colour and are pairwise distinct, then some monochromatic triangle exists: either
`v` together with one of the three pairs closes a triangle in that colour, or — failing that — the
three of them span a triangle in the opposite colour. -/
theorem three_same_colour_mono (c : RedBlue V) (k : Bool) {v a b d : V}
    (hav : a ≠ v) (hbv : b ≠ v) (hdv : d ≠ v)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hca : c.col v a = k) (hcb : c.col v b = k) (hcd : c.col v d = k) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ c.IsMono x y z := by
  by_cases h1 : c.col a b = k
  · exact ⟨v, a, b, Ne.symm hav, hab, Ne.symm hbv, by rw [hca, hcb], by rw [hcb, h1]⟩
  by_cases h2 : c.col a d = k
  · exact ⟨v, a, d, Ne.symm hav, had, Ne.symm hdv, by rw [hca, hcd], by rw [hcd, h2]⟩
  by_cases h3 : c.col b d = k
  · exact ⟨v, b, d, Ne.symm hbv, hbd, Ne.symm hdv, by rw [hcb, hcd], by rw [hcd, h3]⟩
  have e1 : c.col a b = !k := Bool.ne_eq_not h1
  have e2 : c.col a d = !k := Bool.ne_eq_not h2
  have e3 : c.col b d = !k := Bool.ne_eq_not h3
  exact ⟨a, b, d, hab, hbd, had, by rw [e1, e2], by rw [e2, e3]⟩

/-! ## `R(3,3) = 6` -/

/-- **Erdős–Szekeres `R(3,3) = 6`.**  Every two-colouring of the edges of a complete graph on at least
six vertices contains a monochromatic triangle. -/
theorem exists_mono_triangle [Fintype V] (hV : 6 ≤ Fintype.card V) (c : RedBlue V) :
    ∃ x y z : V, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ c.IsMono x y z := by
  have hne : Nonempty V := Fintype.card_pos_iff.mp (show (0 : ℕ) < Fintype.card V by omega)
  let _ : Fintype V := inferInstance
  let v : V := hne.some
  have hmem : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
  have huniv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have hnb : 5 ≤ (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), huniv]
    omega
  rcases three_same_colour c v (Finset.univ.erase v) hnb with hR | hB
  · obtain ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩ := three_of_card_ge_three hR.1
    exact three_same_colour_mono c true
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := a) (b := v) ha
        (by simp : v ∉ (Finset.univ.erase v)))
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := b) (b := v) hb
        (by simp : v ∉ (Finset.univ.erase v)))
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := d) (b := v) hd
        (by simp : v ∉ (Finset.univ.erase v))) hab had hbd
      (hR.2 a ha) (hR.2 b hb) (hR.2 d hd)
  · obtain ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩ := three_of_card_ge_three hB.1
    exact three_same_colour_mono c false
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := a) (b := v) ha
        (by simp : v ∉ (Finset.univ.erase v)))
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := b) (b := v) hb
        (by simp : v ∉ (Finset.univ.erase v)))
      (ne_of_mem_filter_erase (s := Finset.univ.erase v) (a := d) (b := v) hd
        (by simp : v ∉ (Finset.univ.erase v))) hab had hbd
      (hB.2 a ha) (hB.2 b hb) (hB.2 d hd)

/-! ### Packing-level consequence -/

namespace TriPack

variable [DecidableEq V]

/-- The packing consisting of a single genuine triangle. -/
def single (x y z : V) (h : x ≠ y ∧ y ≠ z ∧ x ≠ z) : TriPack V where
  fam := {(x, y, z)}
  valid := by
    intro t ht
    have h1 : t = (x, y, z) := Finset.mem_singleton.mp ht
    subst h1
    exact h
  edgeDisj := by
    intro t ht u hu htu
    have h1 : t = (x, y, z) := Finset.mem_singleton.mp ht
    have h2 : u = (x, y, z) := Finset.mem_singleton.mp hu
    subst h1
    subst h2
    exact absurd rfl htu

end TriPack

/-- **`R(3,3) = 6`, at the level of packings.**  Every two-colouring of `K_n`, `n ≥ 6`, carries a
monochromatic triangle packing of cardinality at least `1`.  This is the small-`n` shadow of
`Erdős93`. -/
theorem exists_mono_pack [Fintype V] (hV : 6 ≤ Fintype.card V) (c : RedBlue V) :
    ∃ P : TriPack V, P.IsMonoPack c ∧ 1 ≤ P.fam.card := by
  obtain ⟨x, y, z, hxy, hyz, hxz, hm⟩ := exists_mono_triangle hV c
  refine ⟨TriPack.single x y z ⟨hxy, hyz, hxz⟩, ?_, by simp [TriPack.single]⟩
  intro t ht
  have h1 : t = (x, y, z) := Finset.mem_singleton.mp ht
  subst h1
  exact hm

end JSP93
