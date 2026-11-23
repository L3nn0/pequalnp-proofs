import PEqualNP.Defs
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_666_aux

open PEqualNP.CircuitLowerBounds

private def fanoLine (w : Fin 7) : Finset (Fin 7) :=
  ({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)

private lemma fano_card (w : Fin 7) : (fanoLine w).card = 3 := by
  fin_cases w <;> decide

private lemma fano_inter_le_one (w₁ w₂ : Fin 7) (h : w₁ ≠ w₂) :
    (fanoLine w₁ ∩ fanoLine w₂).card ≤ 1 := by
  revert h; fin_cases w₁ <;> fin_cases w₂ <;> decide

private lemma fano_union3_ge6 (w₁ w₂ w₃ : Fin 7) (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) :
    6 ≤ (fanoLine w₁ ∪ fanoLine w₂ ∪ fanoLine w₃).card := by
  revert h12 h13 h23; fin_cases w₁ <;> fin_cases w₂ <;> fin_cases w₃ <;> decide

private lemma fano_card4 (A : Finset (Fin 7)) (hA : A.card = 4) :
    (Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro w₁ hw₁ w₂ hw₂
  by_contra hne
  have h1 : fanoLine w₁ ⊆ A := (Finset.mem_filter.1 hw₁).2
  have h2 : fanoLine w₂ ⊆ A := (Finset.mem_filter.1 hw₂).2
  have hun : fanoLine w₁ ∪ fanoLine w₂ ⊆ A := Finset.union_subset h1 h2
  have hle := Finset.card_le_card hun
  have hiu := Finset.card_union_add_card_inter (fanoLine w₁) (fanoLine w₂)
  have hc1 := fano_card w₁
  have hc2 := fano_card w₂
  have hi := fano_inter_le_one w₁ w₂ hne
  omega

private lemma fano_card5 (A : Finset (Fin 7)) (hA : A.card = 5) :
    (Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).card ≤ 2 := by
  by_contra hgt
  have h3 : 2 < (Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).card := by omega
  obtain ⟨w₁, hw₁⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).card)
  obtain ⟨w₂, hw₂, h21⟩ := Finset.exists_mem_ne (by omega : 1 < (Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).card) w₁
  have h3' : 0 < ((Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ A)).erase w₁ |>.erase w₂).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨h21, hw₂⟩), Finset.card_erase_of_mem hw₁]
    omega
  obtain ⟨w₃, hw₃⟩ := Finset.card_pos.1 h3'
  have h32 : w₃ ≠ w₂ := (Finset.mem_erase.1 hw₃).1
  have hw₃' := (Finset.mem_erase.1 hw₃).2
  have h31 : w₃ ≠ w₁ := (Finset.mem_erase.1 hw₃').1
  have hw₃_mem := (Finset.mem_erase.1 hw₃').2
  have hsub : fanoLine w₁ ∪ fanoLine w₂ ∪ fanoLine w₃ ⊆ A :=
    Finset.union_subset (Finset.union_subset (Finset.mem_filter.1 hw₁).2 (Finset.mem_filter.1 hw₂).2)
      (Finset.mem_filter.1 hw₃_mem).2
  have hle := Finset.card_le_card hsub
  have hge := fano_union3_ge6 w₁ w₂ w₃ h21.symm h31.symm h32.symm
  omega

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def val (gs : List Gate) (x : Fin 7 → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

private lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [step]; omega)]
    simp [step, List.getD, List.getElem?_append_left hi]

private lemma val_input (gs : List Gate) (x : Fin 7 → Bool) (i : ℕ) (hi : i < 7) :
    val gs x i = x ⟨i, hi⟩ := by
  unfold val
  rw [fold_getD_lt gs (List.ofFn x) i (by simp [hi])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]

private lemma val_oob (gs : List Gate) (x : Fin 7 → Bool) (i : ℕ) (hi : 7 + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  rw [List.getD_eq_default _ _ (by rw [fold_length, List.length_ofFn]; omega)]

private lemma val_gate (gs : List Gate) (x : Fin 7 → Bool) (j : ℕ) (hj : j < gs.length) :
    val gs x (7 + j) = gs[j].op.eval (gs[j].inputs.map fun i => if i < 7 + j then val gs x i else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    have h1 : gs.take (j + 1) ++ gs.drop (j + 1) = gs := List.take_append_drop (j + 1) gs
    rw [List.take_succ_eq_append_getElem hj, List.append_assoc, List.singleton_append] at h1
    exact h1.symm
  have hl : ((gs.take j).foldl step (List.ofFn x)).length = 7 + j := by
    rw [fold_length, List.length_ofFn, List.length_take]; omega
  unfold val
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [fold_getD_lt _ _ _ (by simp only [step, List.length_append, List.length_singleton, hl]; omega)]
  have hstep_get :
      (step ((gs.take j).foldl step (List.ofFn x)) gs[j]).getD (7 + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step (List.ofFn x)).getD i false) := by
    rw [step, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : ((gs.take j).foldl step (List.ofFn x)).length ≤ 7 + j),
      hl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hstep_get]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 7 + j
  · simp only [hi, ↓reduceIte]
    conv_rhs => rw [hsplit, List.foldl_append, fold_getD_lt _ _ _ (by omega)]
  · simp only [hi, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by omega)]

private def e1 (v : Fin 7) : Fin 7 → Bool := fun i => decide (i = v)

private def wireSet (gs : List Gate) (i : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter (fun v : Fin 7 => val gs (e1 v) i = true)

private lemma wireSet_input (gs : List Gate) (i : ℕ) (hi : i < 7) :
    wireSet gs i = {⟨i, hi⟩} := by
  ext v
  simp only [wireSet, Finset.mem_filter, Finset.mem_univ, true_and, val_input gs (e1 v) i hi,
    e1, decide_eq_true_eq, Finset.mem_singleton, Fin.ext_iff]
  exact eq_comm

private lemma wireSet_oob (gs : List Gate) (i : ℕ) (hi : 7 + gs.length ≤ i) :
    wireSet gs i = ∅ := by
  ext v
  simp [wireSet, val_oob gs (e1 v) i hi]

private lemma wireSet_gate_cases (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hg : (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧ gs[j].inputs.length ≤ 2) :
    wireSet gs (7 + j) = ∅ ∨
    wireSet gs (7 + j) = Finset.univ ∨
    (∃ a, a < 7 + j ∧ wireSet gs (7 + j) = wireSet gs a) ∨
    (∃ a b, a < 7 + j ∧ b < 7 + j ∧ wireSet gs (7 + j) = wireSet gs a ∪ wireSet gs b) ∨
    (∃ a b, a < 7 + j ∧ b < 7 + j ∧ wireSet gs (7 + j) = wireSet gs a ∩ wireSet gs b) := by
  obtain ⟨hop, hlen⟩ := hg
  rcases hins : gs[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · rcases hop with h | h
    · right; left; ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, GateOp.eval]
    · left; ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, GateOp.eval]
  · by_cases ha : a < 7 + j
    · right; right; left; refine ⟨a, ha, ?_⟩
      ext v; rcases hop with h | h <;> simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, GateOp.eval]
    · left; ext v
      rcases hop with h | h <;> simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, GateOp.eval]
  · by_cases ha : a < 7 + j <;> by_cases hb : b < 7 + j
    · rcases hop with h | h
      · right; right; right; right; refine ⟨a, b, ha, hb, ?_⟩
        ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
      · right; right; right; left; refine ⟨a, b, ha, hb, ?_⟩
        ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
    · rcases hop with h | h
      · left; ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
      · right; right; left; refine ⟨a, ha, ?_⟩
        ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
    · rcases hop with h | h
      · left; ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
      · right; right; left; refine ⟨b, hb, ?_⟩
        ext v; simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
    · left; ext v; rcases hop with h | h <;> simp [wireSet, val_gate gs (e1 v) j hj, hins, h, ha, hb, GateOp.eval]
  · rw [hins] at hlen; simp at hlen

private lemma main_bound (gates : List Gate) (out : Fin 7 → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (w : Fin 7) (x : Fin 7 → Bool),
      (∀ i j : Fin 7, x i = true → x j = true → i = j) →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ fanoLine w, x v = true)) :
    14 ≤ gates.length := by
  classical
  have hout_set : ∀ w : Fin 7, wireSet gates (out w) = fanoLine w := by
    intro w
    ext v
    simp only [wireSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hlight : ∀ i j : Fin 7, e1 v i = true → e1 v j = true → i = j := by
      intro i j hi hj; simp [e1] at hi hj; rw [hi, hj]
    have h1 := hev w (e1 v) hlight
    change val gates (e1 v) (out w) = decide (∃ u ∈ fanoLine w, e1 v u = true) at h1
    rw [h1, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, hvu⟩; simp [e1] at hvu; rwa [hvu] at hu
    · intro hv; exact ⟨v, hv, by simp [e1]⟩
  -- For each w : Fin 7, there is a FIRST gate j < gates.length with wireSet (7 + j) = fanoLine w
  have hex_j : ∀ w : Fin 7, ∃ j : ℕ, j < gates.length ∧ wireSet gates (7 + j) = fanoLine w := by
    intro w
    have hout_ge7 : 7 ≤ out w := by
      by_contra hlt
      have h1 := wireSet_input gates (out w) (by omega)
      rw [hout_set w] at h1
      have hc := congrArg Finset.card h1
      rw [fano_card w, Finset.card_singleton] at hc
      omega
    have hout_lt : out w < 7 + gates.length := by
      by_contra hge
      have h1 := wireSet_oob gates (out w) (by omega)
      rw [hout_set w] at h1
      have hc := congrArg Finset.card h1
      rw [fano_card w, Finset.card_empty] at hc
      omega
    exact ⟨out w - 7, by omega, by rw [show 7 + (out w - 7) = out w by omega]; exact hout_set w⟩
  let firstG (w : Fin 7) : ℕ := Nat.find (hex_j w)
  have hfg_lt (w : Fin 7) : firstG w < gates.length := (Nat.find_spec (hex_j w)).1
  have hfg_set (w : Fin 7) : wireSet gates (7 + firstG w) = fanoLine w := (Nat.find_spec (hex_j w)).2
  have hfg_min (w : Fin 7) (j : ℕ) (hj : j < firstG w) : wireSet gates (7 + j) ≠ fanoLine w := by
    intro heq
    have := hfg_lt w
    exact Nat.find_min (hex_j w) hj ⟨by omega, heq⟩
  have hfg_ne_lt (w : Fin 7) (a : ℕ) (ha : a < 7 + firstG w) : wireSet gates a ≠ fanoLine w := by
    by_cases ha7 : a < 7
    · rw [wireSet_input gates a ha7]
      intro h; have := congrArg Finset.card h; rw [Finset.card_singleton, fano_card w] at this; omega
    · have := hfg_min w (a - 7) (by omega)
      rwa [show 7 + (a - 7) = a by omega] at this
  -- Classify each w : Fin 7 into Type U (has a size-2 gate), Type I4 (has a size-4 gate), or Type I5 (has 2 distinct size-5 gates)
  let P2 : Finset ℕ := (Finset.range gates.length).filter (fun j => (wireSet gates (7 + j)).card = 2)
  let Q4 : Finset ℕ := (Finset.range gates.length).filter (fun j => (wireSet gates (7 + j)).card = 4)
  let Q5 : Finset ℕ := (Finset.range gates.length).filter (fun j => (wireSet gates (7 + j)).card = 5)
  let F3 : Finset ℕ := (Finset.range gates.length).filter (fun j => (wireSet gates (7 + j)).card = 3)
  have hF3_ge7 : 7 ≤ F3.card := by
    have hinj : Function.Injective firstG := by
      intro w₁ w₂ h
      have hs : fanoLine w₁ = fanoLine w₂ := by rw [← hfg_set w₁, h, hfg_set w₂]
      by_contra hne
      have hi := fano_inter_le_one w₁ w₂ hne
      rw [hs, Finset.inter_self, fano_card w₂] at hi
      omega
    have hsub : (Finset.univ : Finset (Fin 7)).image firstG ⊆ F3 := by
      intro j hj
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hfg_lt w), by rw [hfg_set w, fano_card w]⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hclass : ∀ w : Fin 7,
      (∃ j ∈ P2, wireSet gates (7 + j) ⊆ fanoLine w) ∨
      (∃ j ∈ Q4, fanoLine w ⊆ wireSet gates (7 + j)) ∨
      (∃ j₁ ∈ Q5, ∃ j₂ ∈ Q5, j₁ ≠ j₂ ∧ fanoLine w ⊆ wireSet gates (7 + j₁) ∧ fanoLine w ⊆ wireSet gates (7 + j₂)) := by
    intro w
    have hcases := wireSet_gate_cases gates (firstG w) (hfg_lt w) (hg _ (List.getElem_mem (hfg_lt w)))
    rw [hfg_set w] at hcases
    rcases hcases with h0 | huniv | ⟨a, ha, heq⟩ | ⟨a, b, ha, hb, hun⟩ | ⟨a, b, ha, hb, hint⟩
    · have := congrArg Finset.card h0; rw [fano_card w, Finset.card_empty] at this; omega
    · have := congrArg Finset.card huniv; rw [fano_card w, Finset.card_univ, Fintype.card_fin] at this; omega
    · exact absurd heq.symm (hfg_ne_lt w a ha)
    · -- OR gate: fanoLine w = wireSet a ∪ wireSet b
      have hsa : wireSet gates a ⊆ fanoLine w := by rw [hun]; exact Finset.subset_union_left
      have hsb : wireSet gates b ⊆ fanoLine w := by rw [hun]; exact Finset.subset_union_right
      have hca_lt : (wireSet gates a).card < 3 := by
        by_contra hge
        have hle := Finset.card_le_card hsa
        rw [fano_card w] at hle
        exact hfg_ne_lt w a ha (Finset.eq_of_subset_of_card_le hsa (by rw [fano_card w]; omega))
      have hcb_lt : (wireSet gates b).card < 3 := by
        by_contra hge
        have hle := Finset.card_le_card hsb
        rw [fano_card w] at hle
        exact hfg_ne_lt w b hb (Finset.eq_of_subset_of_card_le hsb (by rw [fano_card w]; omega))
      have hsum : 3 ≤ (wireSet gates a).card + (wireSet gates b).card := by
        have := Finset.card_union_le (wireSet gates a) (wireSet gates b)
        rw [← hun, fano_card w] at this; exact this
      left
      by_cases h2a : (wireSet gates a).card = 2
      · have ha7 : 7 ≤ a := by
          by_contra hlt; rw [wireSet_input gates a (by omega), Finset.card_singleton] at h2a; omega
        refine ⟨a - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩, ?_⟩
        · rw [show 7 + (a - 7) = a by omega]; exact h2a
        · rw [show 7 + (a - 7) = a by omega]; exact hsa
      · have h2b : (wireSet gates b).card = 2 := by omega
        have hb7 : 7 ≤ b := by
          by_contra hlt; rw [wireSet_input gates b (by omega), Finset.card_singleton] at h2b; omega
        refine ⟨b - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩, ?_⟩
        · rw [show 7 + (b - 7) = b by omega]; exact h2b
        · rw [show 7 + (b - 7) = b by omega]; exact hsb
    · -- AND gate: fanoLine w = wireSet a ∩ wireSet b
      have hsa : fanoLine w ⊆ wireSet gates a := by rw [hint]; exact Finset.inter_subset_left
      have hsb : fanoLine w ⊆ wireSet gates b := by rw [hint]; exact Finset.inter_subset_right
      have hca_gt : 3 < (wireSet gates a).card := by
        by_contra hle
        exact hfg_ne_lt w a ha (Finset.eq_of_subset_of_card_le hsa (by rw [fano_card w]; omega)).symm
      have hcb_gt : 3 < (wireSet gates b).card := by
        by_contra hle
        exact hfg_ne_lt w b hb (Finset.eq_of_subset_of_card_le hsb (by rw [fano_card w]; omega)).symm
      have ha7 : 7 ≤ a := by
        by_contra hlt; rw [wireSet_input gates a (by omega), Finset.card_singleton] at hca_gt; omega
      have hb7 : 7 ≤ b := by
        by_contra hlt; rw [wireSet_input gates b (by omega), Finset.card_singleton] at hcb_gt; omega
      by_cases h4a : (wireSet gates a).card = 4
      · right; left
        refine ⟨a - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩, ?_⟩
        · rw [show 7 + (a - 7) = a by omega]; exact h4a
        · rw [show 7 + (a - 7) = a by omega]; exact hsa
      · by_cases h4b : (wireSet gates b).card = 4
        · right; left
          refine ⟨b - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩, ?_⟩
          · rw [show 7 + (b - 7) = b by omega]; exact h4b
          · rw [show 7 + (b - 7) = b by omega]; exact hsb
        · -- Both have card ≥ 5; since their intersection has card 3, both MUST have card = 5 and be distinct!
          have hsum : (wireSet gates a).card + (wireSet gates b).card ≤ 10 := by
            have hiu := Finset.card_union_add_card_inter (wireSet gates a) (wireSet gates b)
            have hun : (wireSet gates a ∪ wireSet gates b).card ≤ 7 := by
              have := Finset.card_le_univ (wireSet gates a ∪ wireSet gates b); simpa using this
            rw [← hint, fano_card w] at hiu; omega
          have h5a : (wireSet gates a).card = 5 := by omega
          have h5b : (wireSet gates b).card = 5 := by omega
          have hab : a ≠ b := by
            intro h; subst h; rw [Finset.inter_self] at hint
            have := congrArg Finset.card hint; rw [fano_card w, h5a] at this; omega
          right; right
          refine ⟨a - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩,
            b - 7, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := hfg_lt w; omega), ?_⟩,
            by omega, ?_, ?_⟩
          · rw [show 7 + (a - 7) = a by omega]; exact h5a
          · rw [show 7 + (b - 7) = b by omega]; exact h5b
          · rw [show 7 + (a - 7) = a by omega]; exact hsa
          · rw [show 7 + (b - 7) = b by omega]; exact hsb
  -- Partition Fin 7 into U, I4, I5
  let U : Finset (Fin 7) := Finset.univ.filter (fun w => ∃ j ∈ P2, wireSet gates (7 + j) ⊆ fanoLine w)
  let I4 : Finset (Fin 7) := Finset.univ.filter (fun w => ∃ j ∈ Q4, fanoLine w ⊆ wireSet gates (7 + j))
  let I5 : Finset (Fin 7) := Finset.univ.filter (fun w =>
    ∃ j₁ ∈ Q5, ∃ j₂ ∈ Q5, j₁ ≠ j₂ ∧ fanoLine w ⊆ wireSet gates (7 + j₁) ∧ fanoLine w ⊆ wireSet gates (7 + j₂))
  have hcover : (Finset.univ : Finset (Fin 7)) ⊆ U ∪ I4 ∪ I5 := by
    intro w _
    simp only [Finset.mem_union, U, I4, I5, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hclass w with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h7_le : 7 ≤ U.card + I4.card + I5.card := by
    have h1 := Finset.card_le_card hcover
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_union_le (U ∪ I4) I5
    have h3 := Finset.card_union_le U I4
    omega
  -- 1. U.card ≤ P2.card
  have hU_le : U.card ≤ P2.card := by
    have hchoose : ∀ w : Fin 7, w ∈ U → ∃ j ∈ P2, wireSet gates (7 + j) ⊆ fanoLine w :=
      fun w hw => (Finset.mem_filter.1 hw).2
    let f : Fin 7 → ℕ := fun w => if h : w ∈ U then (hchoose w h).choose else 0
    have hmaps : Set.MapsTo f (U : Set (Fin 7)) (P2 : Set ℕ) := by
      intro w hw
      simp only [Finset.mem_coe] at hw ⊢
      simp only [f, hw, ↓reduceDIte]
      exact (hchoose w hw).choose_spec.1
    have hinj : Set.InjOn f (U : Set (Fin 7)) := by
      intro w₁ hw₁ w₂ hw₂ heq
      simp only [Finset.mem_coe] at hw₁ hw₂
      simp only [f, hw₁, hw₂, ↓reduceDIte] at heq
      by_contra hne
      have hsub1 : wireSet gates (7 + (hchoose w₁ hw₁).choose) ⊆ fanoLine w₁ := (hchoose w₁ hw₁).choose_spec.2
      have hsub2 : wireSet gates (7 + (hchoose w₁ hw₁).choose) ⊆ fanoLine w₂ := heq ▸ (hchoose w₂ hw₂).choose_spec.2
      have hsub : wireSet gates (7 + (hchoose w₁ hw₁).choose) ⊆ fanoLine w₁ ∩ fanoLine w₂ :=
        Finset.subset_inter hsub1 hsub2
      have hc2 : (wireSet gates (7 + (hchoose w₁ hw₁).choose)).card = 2 :=
        (Finset.mem_filter.1 (hchoose w₁ hw₁).choose_spec.1).2
      have hle := Finset.card_le_card hsub
      have hi := fano_inter_le_one w₁ w₂ hne
      omega
    exact Finset.card_le_card_of_injOn f hmaps hinj
  -- 2. I4.card ≤ Q4.card
  have hI4_le : I4.card ≤ Q4.card := by
    have hchoose : ∀ w : Fin 7, w ∈ I4 → ∃ j ∈ Q4, fanoLine w ⊆ wireSet gates (7 + j) :=
      fun w hw => (Finset.mem_filter.1 hw).2
    let f : Fin 7 → ℕ := fun w => if h : w ∈ I4 then (hchoose w h).choose else 0
    have hmaps : Set.MapsTo f (I4 : Set (Fin 7)) (Q4 : Set ℕ) := by
      intro w hw
      simp only [Finset.mem_coe] at hw ⊢
      simp only [f, hw, ↓reduceDIte]
      exact (hchoose w hw).choose_spec.1
    have hinj : Set.InjOn f (I4 : Set (Fin 7)) := by
      intro w₁ hw₁ w₂ hw₂ heq
      simp only [Finset.mem_coe] at hw₁ hw₂
      simp only [f, hw₁, hw₂, ↓reduceDIte] at heq
      set j := (hchoose w₁ hw₁).choose
      have hj4 : (wireSet gates (7 + j)).card = 4 := (Finset.mem_filter.1 (hchoose w₁ hw₁).choose_spec.1).2
      have hle1 := fano_card4 (wireSet gates (7 + j)) hj4
      have h1 : w₁ ∈ Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ wireSet gates (7 + j)) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, (hchoose w₁ hw₁).choose_spec.2⟩
      have h2 : w₂ ∈ Finset.univ.filter (fun w : Fin 7 => fanoLine w ⊆ wireSet gates (7 + j)) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, heq ▸ (hchoose w₂ hw₂).choose_spec.2⟩
      exact Finset.card_le_one.1 hle1 w₁ h1 w₂ h2
    exact Finset.card_le_card_of_injOn f hmaps hinj
  -- 3. I5.card ≤ Q5.card (by double counting pairs (w, j) with w ∈ I5, j ∈ Q5, fanoLine w ⊆ wireSet (7 + j))
  have hI5_le : I5.card ≤ Q5.card := by
    have hdouble :
        ∑ w ∈ I5, (Q5.filter (fun j => fanoLine w ⊆ wireSet gates (7 + j))).card =
        ∑ j ∈ Q5, (I5.filter (fun w => fanoLine w ⊆ wireSet gates (7 + j))).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    have hLHS : 2 * I5.card ≤ ∑ w ∈ I5, (Q5.filter (fun j => fanoLine w ⊆ wireSet gates (7 + j))).card := by
      calc 2 * I5.card = ∑ _w ∈ I5, 2 := by simp [mul_comm]
        _ ≤ ∑ w ∈ I5, (Q5.filter (fun j => fanoLine w ⊆ wireSet gates (7 + j))).card := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨j₁, hj₁, j₂, hj₂, h12, hsub1, hsub2⟩ := (Finset.mem_filter.1 hw).2
          have hsub : ({j₁, j₂} : Finset ℕ) ⊆ Q5.filter (fun j => fanoLine w ⊆ wireSet gates (7 + j)) := by
            intro j hj; simp at hj
            rcases hj with rfl | rfl
            · exact Finset.mem_filter.2 ⟨hj₁, hsub1⟩
            · exact Finset.mem_filter.2 ⟨hj₂, hsub2⟩
          have := Finset.card_le_card hsub
          rwa [Finset.card_pair h12] at this
    have hRHS : ∑ j ∈ Q5, (I5.filter (fun w => fanoLine w ⊆ wireSet gates (7 + j))).card ≤ 2 * Q5.card := by
      calc ∑ j ∈ Q5, (I5.filter (fun w => fanoLine w ⊆ wireSet gates (7 + j))).card
          ≤ ∑ _j ∈ Q5, 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hj5 : (wireSet gates (7 + j)).card = 5 := (Finset.mem_filter.1 hj).2
            have hle := fano_card5 (wireSet gates (7 + j)) hj5
            refine le_trans (Finset.card_le_card ?_) hle
            intro w hw; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hw).2⟩
        _ = 2 * Q5.card := by simp [mul_comm]
    omega
  -- Combine pairwise disjoint sets F3, P2, Q4, Q5 ⊆ Finset.range gates.length!
  have hsub_all : F3 ∪ P2 ∪ Q4 ∪ Q5 ⊆ Finset.range gates.length := by
    intro j hj
    simp only [Finset.mem_union, F3, P2, Q4, Q5, Finset.mem_filter] at hj
    rcases hj with ((h | h) | h) | h <;> exact h.1
  have hdisj1 : Disjoint F3 P2 := by
    rw [Finset.disjoint_left]; intro j h1 h2
    have c1 := (Finset.mem_filter.1 h1).2; have c2 := (Finset.mem_filter.1 h2).2; omega
  have hdisj2 : Disjoint (F3 ∪ P2) Q4 := by
    rw [Finset.disjoint_left]; intro j h1 h2
    have c2 := (Finset.mem_filter.1 h2).2
    rcases Finset.mem_union.1 h1 with h | h <;> have := (Finset.mem_filter.1 h).2 <;> omega
  have hdisj3 : Disjoint (F3 ∪ P2 ∪ Q4) Q5 := by
    rw [Finset.disjoint_left]; intro j h1 h2
    have c2 := (Finset.mem_filter.1 h2).2
    rcases Finset.mem_union.1 h1 with h | h
    · rcases Finset.mem_union.1 h with h' | h' <;> have := (Finset.mem_filter.1 h').2 <;> omega
    · have := (Finset.mem_filter.1 h).2; omega
  have hcard_all : (F3 ∪ P2 ∪ Q4 ∪ Q5).card = F3.card + P2.card + Q4.card + Q5.card := by
    rw [Finset.card_union_of_disjoint hdisj3, Finset.card_union_of_disjoint hdisj2,
      Finset.card_union_of_disjoint hdisj1]
  have hle_len := Finset.card_le_card hsub_all
  rw [hcard_all, Finset.card_range] at hle_len
  omega

end PEqualNP.Outside.L_meta_666_aux

theorem PEqualNP.Outside.L_meta_666 :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 7 → ℕ),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ (w : Fin 7) (x : Fin 7 → Bool), (∀ i j : Fin 7, x i = true → x j = true → i = j) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3} : Finset (Fin 7)).image (fun u => u + w)), x v = true)) →
      14 ≤ gates.length :=
  PEqualNP.Outside.L_meta_666_aux.main_bound
