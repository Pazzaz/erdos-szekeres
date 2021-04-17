import data.list
import tactic
import data.finset

theorem sublist_take_mp_sublist
{X : Type*}
(A S: list X)
(n : ℕ)
(h: S <+ A.take n)
: S <+ A
:= list.sublist.trans h (list.sublist_of_prefix (A.take_prefix n))

theorem nth_le_mem_take_succ
{X : Type*}
(A : list X)
(n : ℕ)
(h : n < A.length)
: A.nth_le n h ∈ A.take n.succ
:= begin
  rw list.nth_le_take A h (lt_add_one n),
  exact list.nth_le_mem (list.take n.succ A) n _,
end

theorem sublist_concat_is_sublist {X : Type*} {l1 l2 : list X} {e : X} (n : ℕ)
  (h_sub : l1 <+ l2.take n) (h_in : e ∈ l2.drop n)
: l1.concat e <+ l2 :=
begin
  rw [list.concat_eq_append, ←list.take_append_drop n l2],
  exact list.sublist.append h_sub (list.singleton_sublist.mpr h_in),
end

theorem sublist_of_take_concat_sublist_of_take
{X : Type*}
{A B: list X}
{n₁ n₂ : ℕ}
(h₁ : n₂ < A.length)
(h₂ : n₁ ≤ n₂)
(h₃ : B <+ A.take n₁)
: B.concat (A.nth_le n₂ h₁) <+ A.take n₂.succ := begin
  have le_add_of_sub_eq_id : ∀ {a b : ℕ} (h : a ≤ b), a + (b - a) = b           := by omega,
  have succ_bring_in2 :      ∀ {a b : ℕ} (h : a ≤ b), (b + 1) - a = (b - a) + 1 := by omega,
  have le_comp : n₁ + (n₂ - n₁) < A.length,
  { rw le_add_of_sub_eq_id h₂, exact h₁, },
  have comp_nth_le : A.nth_le n₂ h₁ = A.nth_le (n₁ + (n₂ - n₁)) le_comp,
  { congr, exact (le_add_of_sub_eq_id h₂).symm, },
  apply sublist_concat_is_sublist n₁,
  { rw [list.take_take, min_eq_left (le_trans h₂ (nat.le_succ n₂))],
    exact h₃, },
  { rw [←(le_add_of_sub_eq_id (le_trans h₂ (nat.le_succ n₂))), list.drop_take n₁, comp_nth_le, list.nth_le_drop, succ_bring_in2 h₂],
    exact nth_le_mem_take_succ (A.drop n₁) (n₂ - n₁) _, }
end

theorem list_chain_concat
{X : Type*}
{R : X → X → Prop}
{l : list X}
(a : X)
(h1 : list.chain' R l)
(h2 : ∀ (x : X), x ∈ l.last' → R x a)
: list.chain' R (l.concat a)
:= begin
  rw list.concat_eq_append,
  apply list.chain'.append h1 (list.chain'_singleton a),
  intros _ x_in _ y_in,
  rw option.mem_unique y_in rfl,
  exact h2 x x_in,
end

theorem pair_from_pairwise_to_pair_from_map
{X Y: Type*}
{A : list X}
{f : X → Y}
{r1 : X → X → Prop} [ant : anti_symmetric r1]
{r2 : Y → Y → Prop} [rfx : reflexive r2]
(h1 : A.pairwise r1)
(h2 : (A.map f).pairwise r2)
{x y : X}
(h3 : x ∈ A)
(h4 : y ∈ A)
(h5 : r1 x y)
: r2 (f x) (f y)
:= begin
  induction A,
  { finish },
  { have A_tl_pair     := list.pairwise_of_pairwise_cons h1,
    have A_tl_map_pair := list.pairwise_of_pairwise_cons h2,
    have hypp := A_ih A_tl_pair A_tl_map_pair,
    cases h3,
    { cases h4,
      { rw [h3, h4],
        exact rfx (f A_hd), },
      { rw list.map_cons at h2,
        rw h3,
        exact list.rel_of_pairwise_cons h2 (list.mem_map_of_mem f h4), } },
    { cases h4,
      { have thinger := list.rel_of_pairwise_cons h1 h3,
        rw ←h4 at thinger,
        rw ant h5 thinger,
        exact rfx (f y), },
      { exact hypp h3 h4, } }, }
end

theorem prod_ne_iff_right_or_left_ne
{X Y : Type*}
(a b : X × Y)
: a.1 ≠ b.1 ∨ a.2 ≠ b.2 ↔ a ≠ b
:= begin
  cases a, cases b,
  simpa [not_and, prod.mk.inj_iff, ne.def] using imp_iff_not_or.symm,
end

theorem nat_mul_sub_right_lt
{a b : ℕ}
(h1 : a ≠ 0)
(h2 : b ≠ 0)
: a*(b-1) < a*b
:= (mul_lt_mul_left (pos_iff_ne_zero.mpr h1)).mpr (nat.pred_lt h2)

theorem nat_mul_sub_left_lt
{a b : ℕ}
(h1 : a ≠ 0)
(h2 : b ≠ 0)
: (a-1)*b < a*b
:= (mul_lt_mul_right (pos_iff_ne_zero.mpr h2)).mpr (nat.pred_lt h1)

theorem nat_mul_sub_left_le
(a b : ℕ)
: (a-1)*b ≤ a*b
:= begin
  by_cases h : 0 < b,
  { exact (mul_le_mul_right h).mpr (nat.sub_le a 1), },
  { rw [not_lt, nonpos_iff_eq_zero] at h,
    rw [h, mul_zero, mul_zero], }
end

theorem cons_sub_not_eq
{X : Type*}
{A B : list X}
{a b : X}
(h1 : a ≠ b)
(h2 : a :: A <+ b :: B)
: a :: A <+ B
:= begin
  cases h2 with _ _ _ e _ _ _ _,
  { exact e },
  { exact absurd rfl h1 },
end

theorem drop_while_imp_mem
{X: Type*} [decidable_eq X]
(A : list X)
(f : X → Prop) [decidable_pred f]
: A.drop_while f = A.drop_while (λ x, x ∈ A → f x)
:= begin
  induction A,
  { exact rfl, },
  { dsimp [list.drop_while],
    have thing : (A_hd ∈ (A_hd :: A_tl) → f A_hd) = f A_hd, by simp,
    have step2 : ∀ x, (x ∈ A_hd :: A_tl → f x) = ((x = A_hd ∨ x ∈ A_tl) → f x),
    { tauto, },
    simp only [thing],
    simp only [step2],

    split_ifs,
    { rw A_ih,
      congr,
      ext,
      split,
      { intros dkdkkd huehue,
        cases huehue,
        { rw ←huehue at h,
          exact h, },
        { exact dkdkkd huehue, }, },
      { intros juju x_inn,
        exact juju (or.inr x_inn), }, },
    { exact ⟨rfl, rfl⟩, } },
end

theorem sublist_map_exists
{X Y : Type*}
{A : list X}
{B : list Y}
{f : X → Y}
(h : B <+ A.map f)
: ∃ C, C <+ A ∧ C.map f = B
:= begin
  induction A generalizing B,
  { refine ⟨list.nil, list.nil.nil_sublist, _⟩,
    rw list.eq_nil_of_sublist_nil h,
    exact rfl, },
  { rw list.map_cons at h,
    by_cases hhh : B = list.nil,
    { rw hhh,
      exact ⟨list.nil, (A_hd :: A_tl).nil_sublist, rfl⟩, },
    { obtain ⟨b, B', hhh2⟩ := list.exists_cons_of_ne_nil hhh,
      rw hhh2 at *,
      by_cases heads_eq : b = f A_hd,
      { rw [heads_eq] at h,
        obtain ⟨C',C'_le,C'_map⟩ := A_ih (list.cons_sublist_cons_iff.mp h),
        refine ⟨A_hd :: C',_,_⟩,
        exact list.cons_sublist_cons_iff.mpr C'_le,
        rw [list.map_cons, C'_map, heads_eq], },
      { obtain ⟨C,C_le,C_map⟩ := A_ih (cons_sub_not_eq heads_eq h),
        exact ⟨C, list.sublist.cons C A_tl A_hd C_le, C_map⟩, }, } }
end

@[simp]
theorem take_while_false_mem
{X : Type*}
{A : list X}
(f : X → Prop) [decidable_pred f]
(h: ∀ x ∈ A, ¬(f x))
: list.take_while f A = list.nil
:= begin
  induction A,
  { exact rfl },
  { dsimp [list.take_while],
    rw [A_ih _, if_neg (h A_hd (list.mem_cons_self A_hd A_tl))],
    finish, }
end

@[simp]
theorem drop_while_false_mem
{X : Type*}
{A : list X}
(f : X → Prop) [decidable_pred f]
(h: ∀ x ∈ A, ¬(f x))
: list.drop_while f A = A
:= begin
  nth_rewrite 1 ←(list.take_while_append_drop f A),
  rw [take_while_false_mem f h, list.nil_append],
end

theorem finset_sort_idempotent
{X: Type*} [linear_order X]
{A : list X}
(h1 : A.sorted (≤))
(h2 : A.nodup)
: A.to_finset.sort (≤) = A
:= begin
  induction A,
  tauto,
  dsimp [finset.sort],
  have rw_nodup := list.erase_dup_eq_self.mpr h2,
  rw [  rw_nodup, list.merge_sort_eq_insertion_sort,
        list.insertion_sort_cons_eq_take_drop,
        list.sorted.insertion_sort_eq (list.sorted_of_sorted_cons h1)],
  dsimp [list.sorted] at h1,
  have drop_simple : list.drop_while (λ b, ¬A_hd ≤ b) A_tl = A_tl,
  { apply drop_while_false_mem _ _,
    intros _ aa_mem,
    rw not_not,
    exact list.rel_of_pairwise_cons h1 aa_mem, },
  have take_simple: list.take_while (λ b, ¬A_hd ≤ b) A_tl = [],
  { apply @list.append_right_cancel _ _ _(list.drop_while (λ (b : X), ¬A_hd ≤ b) A_tl),
    rw [list.take_while_append_drop _ A_tl, drop_simple, list.nil_append], },
  rw [take_simple, drop_simple, list.nil_append],
end
