
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p np,
  apply np,
  exact p,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_contra,
  apply nnp,
  exact h,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  have ht := doubleneg_elim P,
  exact ht,
  have ht := doubleneg_intro P,
  exact ht,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with p q,
  split,
  exact q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros h p,
  cases h with np q,
  have boom := np p,
  exfalso,
  exact boom,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros h np,
  cases h with p q,
  have boom := np p,
  exfalso,
  exact boom,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros h nq p,
  have q := h p,
  apply nq,
  exact q,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros h p,
  by_cases q : Q,
  exact q,
  have np := h q,
  exfalso,
  apply np,
  exact p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  have ht := impl_as_contrapositive P Q,
  exact ht,
  have ht := impl_as_contrapositive_converse P Q,
  exact ht,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have nponp : P ∨ ¬P,
  right,
  intro p,
  apply h,left,
  exact p,
  apply h,
  exact nponp,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros h np,
  have pq : P → Q,
  intro p,
  have boom := np p,
  exfalso,
  exact boom,
  have p := h pq,
  apply np,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros h nh,
  cases nh with np nq,
  cases h with p q,
  have boom := np p,
  exact boom,
  have boom := nq q,
  exact boom,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros h nh,
  cases h with p q,
  cases nh with np nq,
  have boom := np p,
  exact boom,
  have boom := nq q,
  exact boom,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  have poq : P ∨ Q,
  left,
  exact p,
  have boom := h poq,
  exact boom,
  intro q,
  have poq : P ∨ Q,
  right,
  exact q,
  have boom := h poq,
  exact boom,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  cases h with np nq,
  intro poq,
  cases poq with p q,
  have boom := np p,
  exact boom,
  have boom := nq q,
  exact boom,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases p : P,
  left,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros h nh,
  cases nh with p q,
  cases h with nq np,
  have boom := nq q,
  exact boom,
  have boom := np p,
  exact boom,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  have ht := demorgan_conj P Q,
  exact ht,
  have ht := demorgan_conj_converse P Q,
  exact ht,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  have ht := demorgan_disj P Q,
  exact ht,
  have ht := demorgan_disj_converse P Q,
  exact ht,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p qor,
  cases qor with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with poq por,
  cases poq with p q,
  split,
  exact p,
  left,
  exact q,
  cases por with p r,
  split,
  exact p,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  split,
  cases h with p qor,
  left,
  exact p,
  cases qor with q r,
  right,
  exact q,
  cases h with p qor,
  left,
  exact p,
  cases qor with q r,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with poq por,
  cases poq with p q,
  left,
  exact p,
  cases por with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros h p q,
  have pq: P ∧ Q,
  split,
  exact p,
  exact q,
  have r := h pq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros h paq,
  cases paq with p q,
  have qr := h p,
  have r := qr q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
  cases h with p p,
  exact p,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros h x nh,
  apply h,
  existsi x,
  exact nh,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros h1 h2,
  cases h2 with x h3,
  have h4 := h1 x,
  apply h4,
  exact h3,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h1,
  by_contra h2,
  apply h1,
  intro x,
  by_contra h3,
  apply h2,
  existsi x,
  exact h3,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros h1 h2,
  cases h1 with x h3,
  apply h3,
  have h4 := h2 x,
  exact h4,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  have ht := demorgan_forall U P,
  exact ht,
  have ht :=demorgan_forall_converse U P,
  exact ht,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  have ht := demorgan_exists U P,
  exact ht,
  have ht := demorgan_exists_converse U P,
  exact ht,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros h1 h2,
  cases h1 with x h3,
  have h4 := h2 x,
  apply h4,
  exact h3,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros h1 h2,
  cases h2 with x h3,
  have h4 := h1 x,
  apply h3,
  exact h4,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros h1 x,
  by_contra h2,
  apply h1,
  existsi x,
  exact h2,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro h1,
  by_contra h2,
  apply h1,
  intro x,
  intro h3,
  apply h2,
  existsi x,
  exact h3,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  have ht := forall_as_neg_exists U P,
  exact ht,
  have ht := forall_as_neg_exists_converse U P,
  exact ht,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  have ht := exists_as_neg_forall U P,
  exact ht,
  have ht := exists_as_neg_forall_converse U P,
  exact ht,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h1,
  split,
  cases h1 with x h2,
  existsi x,
  cases h2 with h3 h4,
  exact h3,
  cases h1 with x h2,
  existsi x,
  cases h2 with h3 h4,
  exact h4,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h1,
  cases h1 with x h2,
  cases h2 with h h,
  left,
  existsi x,
  exact h,
  right,
  existsi x,
  exact h,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with h h,
  cases h with x h,
  existsi x,
  left,
  exact h,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro x,
  have hf := h x,
  cases hf with hp hq,
  exact hp,
  intro x,
  have hf := h x,
  cases hf with hp hq,
  exact hq,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intros h x,
  split,
  cases h with h1 h2,
  have hp := h1 x,
  exact hp,
  cases h with h1 h2,
  have hq := h2 x,
  exact hq,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros h x,
  cases h with h h,
  left,
  have hp := h x,
  exact hp,
  right,
  have hq := h x,
  exact hq,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
