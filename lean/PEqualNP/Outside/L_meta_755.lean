import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private def adj (i j : Fin 6) : Prop :=
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
  ((i = 1 ∨ i = 2 ∨ i = 3) ∧ j = 0) ∨
  (i = 4 ∧ j = 5) ∨
  (i = 5 ∧ j = 4)

private def G : SimpleGraph (Fin 6) where
  Adj := adj
  symm := ⟨fun i j h => by
    rcases h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl | rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [adj]⟩
  loopless := ⟨fun i h => by
    rcases h with ⟨rfl, h | h | h⟩ | ⟨h | h | h, rfl⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
      simp at h⟩

private def adjDec : DecidableRel G.Adj := fun i j => by
  change Decidable (adj i j)
  unfold adj
  infer_instance

private lemma G_has_edge : ∃ i j : Fin 6, G.Adj i j :=
  ⟨0, 1, Or.inl ⟨rfl, Or.inl rfl⟩⟩

private lemma G_cover_min :
    ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have h1 : (0 : Fin 6) ∈ T ∨ (1 : Fin 6) ∈ T := hT 0 1 (Or.inl ⟨rfl, Or.inl rfl⟩)
  have h2 : (4 : Fin 6) ∈ T ∨ (5 : Fin 6) ∈ T := hT 4 5 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  rcases h1 with h0 | h1 <;> rcases h2 with h4 | h5
  · exact Finset.one_lt_card.2 ⟨0, h0, 4, h4, by decide⟩
  · exact Finset.one_lt_card.2 ⟨0, h0, 5, h5, by decide⟩
  · exact Finset.one_lt_card.2 ⟨1, h1, 4, h4, by decide⟩
  · exact Finset.one_lt_card.2 ⟨1, h1, 5, h5, by decide⟩

private lemma G_cover_04 :
    ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
  intro i j h
  rcases h with ⟨rfl, _⟩ | ⟨_, rfl⟩ | ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> simp

private lemma G_edge_eq :
    let _ : DecidableRel G.Adj := adjDec
    G.edgeFinset = {s((0 : Fin 6), 1), s(0, 2), s(0, 3), s(4, 5)} := by
  let _ : DecidableRel G.Adj := adjDec
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff]
    fin_cases a <;> fin_cases b <;> simp [G, adj]

private lemma G_edge_card :
    let _ : DecidableRel G.Adj := adjDec
    G.edgeFinset.card = 4 := by
  dsimp only
  rw [G_edge_eq]
  decide

private lemma adj_unique_of_ne_zero (u x y : Fin 6) (hx : G.Adj u x) (hy : G.Adj u y) (hu : u ≠ 0) :
    x = y := by
  fin_cases u <;> fin_cases x <;> fin_cases y <;> simp_all [G, adj]

private lemma G_acyclic : G.IsAcyclic := by
  intro v p hp
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hed : p.edges.Nodup := hp.edges_nodup
  cases p with
  | nil => simp at hlen
  | cons h1 p1 =>
    rename_i u
    cases p1 with
    | nil => simp at hlen
    | cons h2 p2 =>
      rename_i w
      cases p2 with
      | nil => simp at hlen
      | cons h3 p3 =>
        rename_i z
        simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons] at hed
        have h12 : s(v, u) ≠ s(u, w) := fun h => hed.1 (Or.inl h)
        have h23 : s(u, w) ≠ s(w, z) := fun h => hed.2.1 (Or.inl h)
        have hvw : v ≠ w := by
          intro h; subst h; exact h12 Sym2.eq_swap
        have huz : u ≠ z := by
          intro h; subst h; exact h23 Sym2.eq_swap
        have hu0 : u = 0 := by
          by_contra h
          exact hvw (adj_unique_of_ne_zero u v w (G.symm.symm _ _ h1) h2 h)
        have hw0 : w = 0 := by
          by_contra h
          exact huz (adj_unique_of_ne_zero w u z (G.symm.symm _ _ h2) h3 h)
        subst hu0; subst hw0
        exact G.loopless.irrefl 0 h2

private lemma target_eq_edgeFun :
    let _ : DecidableRel G.Adj := adjDec
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  let _ : DecidableRel G.Adj := adjDec
  funext x
  apply Bool.eq_iff_iff.2
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h0, h3⟩) | ⟨h4, h5⟩)
    · exact ⟨0, 1, Or.inl ⟨rfl, Or.inl rfl⟩, h0, h1⟩
    · exact ⟨0, 2, Or.inl ⟨rfl, Or.inr (Or.inl rfl)⟩, h0, h2⟩
    · exact ⟨0, 3, Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩, h0, h3⟩
    · exact ⟨4, 5, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)), h4, h5⟩
  · rintro ⟨i, j, hadj, hi, hj⟩
    rcases hadj with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl | rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hi, hj⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hi, hj⟩))
    · exact Or.inl (Or.inr ⟨hi, hj⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨hj, hi⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hj, hi⟩))
    · exact Or.inl (Or.inr ⟨hj, hi⟩)
    · exact Or.inr ⟨hi, hj⟩
    · exact Or.inr ⟨hj, hi⟩

end PEqualNP.Outside.L_meta_755_aux

theorem PEqualNP.Outside.L_meta_755 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔
      5 ≤ s := by
  intro s
  open PEqualNP.Outside.L_meta_755_aux in
  let _ : DecidableRel G.Adj := adjDec
  constructor
  · intro hs
    rw [target_eq_edgeFun] at hs
    have hlow := PEqualNP.MetaComplexity.L104 6 2 s G G_acyclic G_has_edge G_cover_min hs
    have hcard : G.edgeFinset.card = 4 := G_edge_card
    omega
  · intro hs
    rw [target_eq_edgeFun]
    have hup := PEqualNP.MetaComplexity.L105 6 G ({0, 4} : Finset (Fin 6)) G_has_edge G_cover_04
    have hcard : G.edgeFinset.card = 4 := G_edge_card
    have hT : ({0, 4} : Finset (Fin 6)).card = 2 := by decide
    rcases hup with ⟨C, hF, hsz, hev⟩
    exact ⟨C, hF, by omega, hev⟩
