import PEqualNP.Defs
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def val (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) : Bool :=
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
    rw [ih _ (by simp only [step, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma val_input (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  unfold val
  rw [fold_getD_lt gs (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]

private lemma val_oob (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  rw [List.getD_eq_default _ _ (by rw [fold_length, List.length_ofFn]; omega)]

private lemma val_gate (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map fun i => if i < n + j then val gs x i else false) := by
  have hsplit : gs = gs.take j ++ (gs[j] :: gs.drop (j + 1)) := by
    have h1 : gs.take (j + 1) ++ gs.drop (j + 1) = gs := List.take_append_drop (j + 1) gs
    rw [List.take_succ_eq_append_getElem hj, List.append_assoc, List.singleton_append] at h1
    exact h1.symm
  have hl : ((gs.take j).foldl step (List.ofFn x)).length = n + j := by
    rw [fold_length, List.length_ofFn, List.length_take]; omega
  unfold val
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [fold_getD_lt _ _ _ (by simp only [step, List.length_append, List.length_cons, List.length_nil, hl]; omega)]
  have hstep_get :
      (step ((gs.take j).foldl step (List.ofFn x)) gs[j]).getD (n + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step (List.ofFn x)).getD i false) := by
    rw [step, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : ((gs.take j).foldl step (List.ofFn x)).length ≤ n + j),
      hl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hstep_get]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]
    conv_rhs => rw [hsplit, List.foldl_append, fold_getD_lt _ _ _ (by omega)]
  · simp only [hi, ↓reduceIte]
    rw [List.getD_eq_default _ _ (by omega)]

private lemma val_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ i : ℕ, val gs x i = true → val gs y i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hx
    by_cases hin : i < n
    · rw [val_input gs x i hin] at hx
      rw [val_input gs y i hin]
      exact hxy ⟨i, hin⟩ hx
    · by_cases hiend : i < n + gs.length
      · set j := i - n
        have hj : j < gs.length := by omega
        have hij : i = n + j := by omega
        rw [hij] at hx ⊢
        rw [val_gate gs x j hj] at hx
        rw [val_gate gs y j hj]
        have hop := (hg gs[j] (List.getElem_mem hj)).1
        rcases hop with hop | hop
        · rw [hop] at hx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hx ⊢
          intro a ha
          have hxa := hx a ha
          by_cases halt : a < n + j
          · simp only [halt, ↓reduceIte] at hxa ⊢
            exact ih a (by omega) hxa
          · simp only [halt, ↓reduceIte] at hxa
            cases hxa
        · rw [hop] at hx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
          rcases hx with ⟨_, ⟨a, ha, rfl⟩, hxa⟩
          by_cases halt : a < n + j
          · simp only [halt, ↓reduceIte] at hxa
            exact ⟨true, ⟨a, ha, by simp only [halt, ↓reduceIte]; exact ih a (by omega) hxa⟩, rfl⟩
          · simp only [halt, ↓reduceIte] at hxa
            cases hxa
      · rw [val_oob gs x i (by omega)] at hx
        cases hx

private def ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ A)

private lemma filter_ind_card {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => ind A i = true)).card = A.card := by
  congr 1
  ext i
  simp [ind]

private lemma ind_mono {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B) :
    ∀ v : Fin n, ind A v = true → ind B v = true := by
  intro v hv
  simp only [ind, decide_eq_true_eq] at hv ⊢
  exact h hv

private def Spec {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (w : Fin m) (j : ℕ) : Prop :=
  val gs (ind (S w)) (n + j) = true ∧ ∀ v : Fin m, v ≠ w → val gs (ind (S v)) (n + j) = false

private lemma spec_disjoint {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate)
    {w₁ w₂ : Fin m} (hne : w₁ ≠ w₂) {j : ℕ} (h1 : Spec S gs w₁ j) (h2 : Spec S gs w₂ j) :
    False := by
  have ht := h2.1
  have hf := h1.2 w₂ hne.symm
  rw [ht] at hf
  cases hf

private lemma descent_step {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hScard : ∀ i : Fin m, (S i).card = q + 1)
    (hSinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin m) :
    ∀ (B : ℕ) (F : Finset ℕ) (V : Finset ℕ) (P : Finset (Fin n)) (d : ℕ),
      (∀ a ∈ F, a < n + B) →
      (∀ a ∈ F, val gs (ind (S w)) a = true) →
      (∀ j ∈ V, j < gs.length ∧ Spec S gs w j ∧ B ≤ j) →
      (∀ A : Finset (Fin n), P ⊆ A → A.card ≤ K → ¬ (S w ⊆ A) → ∃ a ∈ F, val gs (ind A) a = false) →
      F.card + d ≤ 1 + V.card →
      (d = 0 → P = ∅) →
      (1 ≤ d → ∃ v₀ : Fin m, v₀ ≠ w ∧ S v₀ ⊆ P) →
      P.card ≤ (if d = 0 then 0 else 1 + d * q) →
      (S w ∩ P).card ≤ d →
      ∃ (F' : Finset ℕ) (V' : Finset ℕ) (P' : Finset (Fin n)) (d' : ℕ),
        (∀ a ∈ F', a < n) ∧
        (∀ a ∈ F', val gs (ind (S w)) a = true) ∧
        (∀ j ∈ V', j < gs.length ∧ Spec S gs w j) ∧
        (∀ A : Finset (Fin n), P' ⊆ A → A.card ≤ K → ¬ (S w ⊆ A) → ∃ a ∈ F', val gs (ind A) a = false) ∧
        F'.card + d' ≤ 1 + V'.card ∧
        P'.card ≤ (if d' = 0 then 0 else 1 + d' * q) ∧
        (S w ∩ P').card ≤ d' := by
  intro B
  induction B with
  | zero =>
    intro F V P d hB htrue hV hsound hcard _ _ hP hSwP
    exact ⟨F, V, P, d, hB, htrue, fun j hj => ⟨(hV j hj).1, (hV j hj).2.1⟩, hsound, hcard, hP, hSwP⟩
  | succ B ih =>
    intro F V P d hB htrue hV hsound hcard hd0 hd1 hP hSwP
    by_cases hmem : n + B ∈ F
    · have hBl : B < gs.length := by
        by_contra hge
        have hf := val_oob gs (ind (S w)) (n + B) (by omega)
        have ht := htrue (n + B) hmem
        rw [ht] at hf; cases hf
      have hBnotV : B ∉ V := by
        intro hBV
        have := (hV B hBV).2.2
        omega
      by_cases hspec : Spec S gs w B
      · -- Gate B is w-specific
        have hgB := hg gs[B] (List.getElem_mem hBl)
        have hvalB := val_gate gs (ind (S w)) B hBl
        have htrueB := htrue (n + B) hmem
        rcases hgB.1 with hop | hop
        · -- Specific AND gate
          have hch_ok : ∀ a ∈ gs[B].inputs, a < n + B ∧ val gs (ind (S w)) a = true := by
            intro a ha
            rw [hop] at hvalB
            rw [hvalB] at htrueB
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂] at htrueB
            have hxa := htrueB a ha
            by_cases halt : a < n + B
            · simp only [halt, ↓reduceIte] at hxa
              exact ⟨halt, hxa⟩
            · simp only [halt, ↓reduceIte] at hxa
              cases hxa
          let F1 := F.erase (n + B) ∪ gs[B].inputs.toFinset
          let V1 := insert B V
          apply ih F1 V1 P d
          · intro a ha
            simp only [F1, Finset.mem_union, Finset.mem_erase, List.mem_toFinset] at ha
            rcases ha with ⟨hne, hF⟩ | hin
            · have := hB a hF; omega
            · exact (hch_ok a hin).1
          · intro a ha
            simp only [F1, Finset.mem_union, Finset.mem_erase, List.mem_toFinset] at ha
            rcases ha with ⟨_, hF⟩ | hin
            · exact htrue a hF
            · exact (hch_ok a hin).2
          · intro j hj
            simp only [V1, Finset.mem_insert] at hj
            rcases hj with rfl | hj
            · exact ⟨hBl, hspec, le_rfl⟩
            · exact ⟨(hV j hj).1, (hV j hj).2.1, by have := (hV j hj).2.2; omega⟩
          · intro A hPA hAK hnotSw
            obtain ⟨a, haF, haf⟩ := hsound A hPA hAK hnotSw
            by_cases haB : a = n + B
            · subst haB
              rw [val_gate gs (ind A) B hBl, hop] at haf
              simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq, Bool.not_eq_true] at haf
              rcases haf with ⟨_, ⟨c, hc, rfl⟩, hcf⟩
              have hclt := (hch_ok c hc).1
              simp only [hclt, ↓reduceIte] at hcf
              exact ⟨c, Finset.mem_union_right _ (List.mem_toFinset.2 hc), hcf⟩
            · exact ⟨a, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨haB, haF⟩), haf⟩
          · have hF1 : F1.card ≤ (F.erase (n + B)).card + gs[B].inputs.toFinset.card :=
              Finset.card_union_le _ _
            have her : (F.erase (n + B)).card + 1 = F.card :=
              Finset.card_erase_add_one hmem
            have hto : gs[B].inputs.toFinset.card ≤ 2 :=
              le_trans (List.toFinset_card_le _) hgB.2
            have hV1 : V1.card = V.card + 1 := Finset.card_insert_of_notMem hBnotV
            omega
          · exact hd0
          · exact hd1
          · exact hP
          · exact hSwP
        · -- Specific OR gate
          rw [hop] at hvalB
          rw [hvalB] at htrueB
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at htrueB
          rcases htrueB with ⟨_, ⟨c, hc, rfl⟩, hct⟩
          have hclt : c < n + B := by
            by_contra hge
            simp only [hge, ↓reduceIte] at hct
            cases hct
          simp only [hclt, ↓reduceIte] at hct
          let F1 := insert c (F.erase (n + B))
          apply ih F1 V P d
          · intro a ha
            simp only [F1, Finset.mem_insert, Finset.mem_erase] at ha
            rcases ha with rfl | ⟨hne, hF⟩
            · exact hclt
            · have := hB a hF; omega
          · intro a ha
            simp only [F1, Finset.mem_insert, Finset.mem_erase] at ha
            rcases ha with rfl | ⟨_, hF⟩
            · exact hct
            · exact htrue a hF
          · intro j hj
            exact ⟨(hV j hj).1, (hV j hj).2.1, by have := (hV j hj).2.2; omega⟩
          · intro A hPA hAK hnotSw
            obtain ⟨a, haF, haf⟩ := hsound A hPA hAK hnotSw
            by_cases haB : a = n + B
            · subst haB
              rw [val_gate gs (ind A) B hBl, hop] at haf
              simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq, Bool.not_eq_true] at haf
              have hcf := haf _ ⟨c, hc, rfl⟩
              simp only [hclt, ↓reduceIte] at hcf
              exact ⟨c, Finset.mem_insert_self _ _, hcf⟩
            · exact ⟨a, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨haB, haF⟩), haf⟩
          · have hF1 : F1.card ≤ (F.erase (n + B)).card + 1 := Finset.card_insert_le _ _
            have her : (F.erase (n + B)).card + 1 = F.card := Finset.card_erase_add_one hmem
            omega
          · exact hd0
          · exact hd1
          · exact hP
          · exact hSwP
      · -- Gate B is NOT w-specific: drop it and add S v to P
        have hexv : ∃ v : Fin m, v ≠ w ∧ val gs (ind (S v)) (n + B) = true := by
          unfold Spec at hspec
          push Not at hspec
          obtain ⟨v, hvw, hvne⟩ := hspec (htrue (n + B) hmem)
          exact ⟨v, hvw, by cases h : val gs (ind (S v)) (n + B) <;> simp_all⟩
        rcases hexv with ⟨v, hvw, hvtrue⟩
        let F1 := F.erase (n + B)
        let P1 := P ∪ S v
        apply ih F1 V P1 (d + 1)
        · intro a ha
          simp only [F1, Finset.mem_erase] at ha
          have := hB a ha.2; omega
        · intro a ha
          exact htrue a (Finset.mem_of_mem_erase ha)
        · intro j hj
          exact ⟨(hV j hj).1, (hV j hj).2.1, by have := (hV j hj).2.2; omega⟩
        · intro A hP1A hAK hnotSw
          have hPA : P ⊆ A := Finset.Subset.trans Finset.subset_union_left hP1A
          have hSvA : S v ⊆ A := Finset.Subset.trans Finset.subset_union_right hP1A
          obtain ⟨a, haF, haf⟩ := hsound A hPA hAK hnotSw
          by_cases haB : a = n + B
          · subst haB
            have htA := val_mono gs hg (ind (S v)) (ind A) (ind_mono hSvA) (n + B) hvtrue
            rw [htA] at haf; cases haf
          · exact ⟨a, Finset.mem_erase.2 ⟨haB, haF⟩, haf⟩
        · have her : F1.card + 1 = F.card := Finset.card_erase_add_one hmem
          omega
        · intro h; omega
        · intro _; exact ⟨v, hvw, Finset.subset_union_right⟩
        · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          by_cases hd : d = 0
          · subst hd
            simp only [P1]
            rw [hd0 rfl, Finset.empty_union, hScard v]
            omega
          · simp only [hd, ↓reduceIte] at hP
            obtain ⟨v₀, hv₀w, hv₀P⟩ := hd1 (by omega)
            by_cases hvv₀ : v = v₀
            · subst hvv₀
              have hP1eq : P1 = P := Finset.union_eq_left.2 hv₀P
              have hmul : (d + 1) * q = d * q + q := by rw [Nat.add_mul, Nat.one_mul]
              rw [hP1eq]; omega
            · have hinter : (P ∩ S v).card ≥ 1 := by
                have hsub : S v₀ ∩ S v ⊆ P ∩ S v :=
                  Finset.inter_subset_inter hv₀P (Finset.Subset.refl _)
                have hc := Finset.card_le_card hsub
                rw [hSinter v₀ v (Ne.symm hvv₀)] at hc
                exact hc
              have hunion : P1.card + (P ∩ S v).card = P.card + (S v).card :=
                Finset.card_union_add_card_inter P (S v)
              have hSv := hScard v
              have : P1.card + 1 ≤ P.card + (q + 1) := by omega
              have : (d + 1) * q = d * q + q := by rw [Nat.add_mul, Nat.one_mul]
              omega
        · have hsub : S w ∩ P1 = (S w ∩ P) ∪ (S w ∩ S v) := Finset.inter_union_distrib_left _ _ _
          rw [hsub]
          have hle := Finset.card_union_le (S w ∩ P) (S w ∩ S v)
          rw [hSinter w v hvw.symm] at hle
          omega
    · -- n + B ∉ F
      apply ih F V P d
      · intro a ha
        have := hB a ha
        have hne : a ≠ n + B := fun h => hmem (h ▸ ha)
        omega
      · exact htrue
      · intro j hj
        exact ⟨(hV j hj).1, (hV j hj).2.1, by have := (hV j hj).2.2; omega⟩
      · exact hsound
      · exact hcard
      · exact hd0
      · exact hd1
      · exact hP
      · exact hSwP

private lemma spec_card_ge {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q)
    (hScard : ∀ i : Fin m, (S i).card = q + 1)
    (hSinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ (w : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (hcq : c ≤ q) (hcK : c * q < K) (hc1 : 1 ≤ c) (w : Fin m)
    [DecidablePred (Spec S gs w)] :
    c ≤ ((Finset.range gs.length).filter (fun j => Spec S gs w j)).card := by
  classical
  have hqK : q + 1 ≤ K := by
    have : 1 * q ≤ c * q := Nat.mul_le_mul_right q hc1
    omega
  have hout_true : val gs (ind (S w)) (out w) = true := by
    have h1 := heval w (ind (S w)) (by rw [filter_ind_card, hScard w]; exact hqK)
    change val gs (ind (S w)) (out w) = _ at h1
    rw [h1]
    simp [ind]
  have hout_lt : out w < n + gs.length := by
    by_contra hge
    have hf := val_oob gs (ind (S w)) (out w) (by omega)
    rw [hout_true] at hf; cases hf
  have hsound0 : ∀ A : Finset (Fin n), (∅ : Finset (Fin n)) ⊆ A → A.card ≤ K → ¬ (S w ⊆ A) →
      ∃ a ∈ ({out w} : Finset ℕ), val gs (ind A) a = false := by
    intro A _ hAK hnotSw
    refine ⟨out w, Finset.mem_singleton_self _, ?_⟩
    have h1 := heval w (ind A) (by rw [filter_ind_card]; exact hAK)
    change val gs (ind A) (out w) = _ at h1
    rw [h1]
    simp only [ind, decide_eq_true_eq, decide_eq_false_iff_not]
    exact hnotSw
  obtain ⟨F', V', P', d', hFlt, hFtrue, hV', hsound', hcard', hP', hSwP'⟩ :=
    descent_step S hScard hSinter gs hg w gs.length {out w} ∅ ∅ 0
      (fun a ha => by simp only [Finset.mem_singleton] at ha; subst ha; exact hout_lt)
      (fun a ha => by simp only [Finset.mem_singleton] at ha; subst ha; exact hout_true)
      (fun j hj => by simp at hj)
      hsound0
      (by simp)
      (fun _ => rfl)
      (fun h => by omega)
      (by simp)
      (by simp)
  have hVsub : V' ⊆ (Finset.range gs.length).filter (fun j => Spec S gs w j) := by
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hV' j hj).1, (hV' j hj).2⟩
  suffices hcV : c ≤ V'.card from le_trans hcV (Finset.card_le_card hVsub)
  let Fin_in : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => v.val ∈ F')
  have hFin_sub : Fin_in ⊆ S w := by
    intro v hv
    simp only [Fin_in, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have ht := hFtrue v.val hv
    rw [val_input gs (ind (S w)) v.val v.isLt] at ht
    simpa [ind] using ht
  have hFin_card : Fin_in.card = F'.card := by
    have hbij : Fin_in.image Fin.val = F' := by
      ext a
      simp only [Finset.mem_image, Fin_in, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hv, rfl⟩; exact hv
      · intro ha; exact ⟨⟨a, hFlt a ha⟩, ha, rfl⟩
    rw [← hbij, Finset.card_image_of_injective _ Fin.val_injective]
  let A := P' ∪ Fin_in
  have hnot_false : ¬ ∃ a ∈ F', val gs (ind A) a = false := by
    rintro ⟨a, haF, haf⟩
    have hal : a < n := hFlt a haF
    rw [val_input gs (ind A) a hal] at haf
    have hmemA : (⟨a, hal⟩ : Fin n) ∈ A :=
      Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, haF⟩)
    simp [ind, hmemA] at haf
  have hend : K < A.card ∨ S w ⊆ A := by
    by_contra h
    push Not at h
    exact hnot_false (hsound' A Finset.subset_union_left h.1 h.2)
  by_contra hlt
  have hVle : V'.card + 1 ≤ c := by omega
  rcases hend with hKA | hSwA
  · by_cases hd0 : d' = 0
    · subst hd0
      simp only [↓reduceIte] at hP'
      have hP0 : P' = ∅ := Finset.card_eq_zero.1 (by omega)
      have hAcard : A.card ≤ q + 1 := by
        simp only [A, hP0, Finset.empty_union]
        exact le_trans (Finset.card_le_card hFin_sub) (by rw [hScard w])
      omega
    · simp only [hd0, ↓reduceIte] at hP'
      by_cases hF0 : F'.card = 0
      · have hFin0 : Fin_in = ∅ := Finset.card_eq_zero.1 (by omega)
        have hAeq : A = P' := by simp [A, hFin0]
        rw [hAeq] at hKA
        have hdle : d' ≤ c := by omega
        have hdmul : d' * q ≤ c * q := Nat.mul_le_mul_right q hdle
        omega
      · have hAcard : A.card ≤ P'.card + Fin_in.card := Finset.card_union_le _ _
        have hdle : d' ≤ V'.card := by omega
        have hdmul : d' * (q - 1) ≤ V'.card * (q - 1) := Nat.mul_le_mul_right (q - 1) hdle
        have h1 : d' * q = d' * (q - 1) + d' := by
          calc d' * q = d' * ((q - 1) + 1) := by congr 1; omega
            _ = d' * (q - 1) + d' := by rw [Nat.mul_add, Nat.mul_one]
        have h2 : V'.card * q = V'.card * (q - 1) + V'.card := by
          calc V'.card * q = V'.card * ((q - 1) + 1) := by congr 1; omega
            _ = V'.card * (q - 1) + V'.card := by rw [Nat.mul_add, Nat.mul_one]
        have h3 : V'.card * q + q ≤ c * q := by
          have := Nat.mul_le_mul_right q hVle
          rw [Nat.add_mul, Nat.one_mul] at this
          exact this
        omega
  · have hSw_eq : S w = (S w ∩ P') ∪ (S w ∩ Fin_in) := by
      rw [← Finset.inter_union_distrib_left]
      exact (Finset.inter_eq_left.2 hSwA).symm
    have hle := Finset.card_union_le (S w ∩ P') (S w ∩ Fin_in)
    rw [← hSw_eq, hScard w] at hle
    have h2 : (S w ∩ Fin_in).card ≤ Fin_in.card := Finset.card_le_card Finset.inter_subset_right
    omega

end PEqualNP.Outside.L_meta_925_aux

theorem PEqualNP.Outside.L_meta_925 :
    ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)),
      2 ≤ q →
      (∀ i : Fin m, (S i).card = q + 1) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
        (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ (w : Fin m) (x : Fin n → Bool),
          (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) →
        ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hScard hSinter gates out hg heval c hcq hcK
  classical
  by_cases hc0 : c = 0
  · subst hc0; simp
  have hc1 : 1 ≤ c := by omega
  let Sp : Fin m → Finset ℕ := fun w =>
    (Finset.range gates.length).filter (fun j => PEqualNP.Outside.L_meta_925_aux.Spec S gates w j)
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin m)) Sp := by
    intro w₁ _ w₂ _ hne
    change Disjoint (Sp w₁) (Sp w₂)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact PEqualNP.Outside.L_meta_925_aux.spec_disjoint S gates hne
      (Finset.mem_filter.1 hj1).2 (Finset.mem_filter.1 hj2).2
  have hsum_le : ∑ w : Fin m, c ≤ ∑ w : Fin m, (Sp w).card := by
    apply Finset.sum_le_sum
    intro w _
    exact PEqualNP.Outside.L_meta_925_aux.spec_card_ge S hq hScard hSinter gates out hg heval c hcq hcK hc1 w
  have hbi : (Finset.univ.biUnion Sp).card = ∑ w : Fin m, (Sp w).card :=
    Finset.card_biUnion (fun w₁ hw₁ w₂ hw₂ hne => hdisj hw₁ hw₂ hne)
  have hsub : Finset.univ.biUnion Sp ⊆ Finset.range gates.length := by
    intro j hj
    rcases Finset.mem_biUnion.1 hj with ⟨w, _, hjw⟩
    exact (Finset.mem_filter.1 hjw).1
  have hle_len : (Finset.univ.biUnion Sp).card ≤ gates.length := by
    simpa [Finset.card_range] using Finset.card_le_card hsub
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
  omega
