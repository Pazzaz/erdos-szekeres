import data.list
import tactic
import data.list.nodup
import data.finset
import order.conditionally_complete_lattice
import algebra.order


-- THIS SHOULD BE IN MATLIB ----------------------
/- A sublist of a prefix (created with take) is a prefix of the whole list -/
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
: A.nth_le n h ∈ A.take (n.succ)
:= begin
  rw list.nth_le_take A h (lt_add_one n),
  exact list.nth_le_mem (list.take n.succ A) n _,
end

theorem sublist_concat_is_sublist {X : Type*} {l1 l2 : list X} {e : X} (n : ℕ)
  (h_sub : l1 <+ l2.take n) (h_in : e ∈ l2.drop n)
: (l1.concat e) <+ l2 :=
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
: (a.1 ≠ b.1 ∨ a.2 ≠ b.2) ↔ a ≠ b
:= begin
  cases a,
  cases b,
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
(a b : X)
(h1 : a ≠ b)
(h2 : a :: A <+ b :: B)
: a :: A <+ B
:= begin
  cases h2 with _ _ _ easy _ _ _ _,
  exact easy,
  exact false.rec (a :: A <+ B) (h1 rfl),
end

theorem drop_while_imp_mem
{X: Type*} [decidable_eq X]
(A : list X)
(f : X → Prop) [decidable_pred f]
: A.drop_while f = A.drop_while (λ x, x ∈ A → f x)
:= begin
  induction A,
  dsimp [list.drop_while],
  exact rfl,
  dsimp [list.drop_while],
  have thing : (A_hd ∈ (A_hd :: A_tl) → f A_hd) = f A_hd,
  { simp, },
  simp only [thing],
  have step2 : ∀ x, (x ∈ A_hd :: A_tl → f x) = ((x = A_hd ∨ x ∈ A_tl) → f x),
  { tauto, },
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
  { exact ⟨rfl, rfl⟩, }
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
  { 
    refine ⟨list.nil, list.nil.nil_sublist, _⟩,
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
      { obtain ⟨C,C_le,C_map⟩ := A_ih (cons_sub_not_eq b (f A_hd) heads_eq h),
        exact ⟨C, list.sublist.cons C A_tl A_hd C_le, C_map⟩, }, } }
end

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
(A : list X)
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

--------------------------------------------------

/-- Define all subsequences that (1) contain a point and (2) are pairwise following a
  relation (This will in our case be `≤` and `≥`). -/
def subsequences_ending
{X : Type*} [decidable_eq X]
{A : list X}
{n : ℕ}
(h : n < A.length)
(r : X → X → Prop) [decidable_rel r]
: list (list X)
:= (A.take n.succ).sublists.filter (λ l, A.nth_le n h ∈ l.last' ∧ l.pairwise r)

/- Our definition of `subsequences_ending` has the properties we want -/
theorem is_sublist
{X : Type*} [decidable_eq X]
{A l : list X}
{n : ℕ}
(h : n < A.length)
(R : X → X → Prop) [decidable_rel R]
(l_in : l ∈ subsequences_ending h R)
: l <+ A ∧ l.pairwise R
:= begin
  obtain ⟨rest, ⟨_, pairw⟩⟩ := list.mem_filter.mp l_in,
  rw list.mem_sublists at rest,
  exact ⟨sublist_take_mp_sublist A l n.succ rest, pairw⟩,
end

theorem contains_last_true
{X : Type*} [decidable_eq X]
{A : list X}
{n1 : ℕ}
(h1 : n1 < A.length)
(r : X → X → Prop) [decidable_rel r]
: [A.nth_le n1 h1] ∈ subsequences_ending h1 r
:= begin
  dsimp [subsequences_ending],
  rw list.mem_filter,
  split,
  { refine list.mem_sublists.mpr (list.singleton_sublist.mpr _),
    rw (list.nth_le_take A h1 (lt_add_one n1)),
    exact list.nth_le_mem (list.take (n1.succ) A) n1 _, },
  { exact ⟨rfl, list.pairwise_singleton r (list.nth_le A n1 h1)⟩, },
end

theorem contains_last
{X : Type*} [decidable_eq X]
{A : list X}
{n1 : ℕ}
(h1 : n1 < A.length)
(r : X → X → Prop) [decidable_rel r]
: [A.nth_le n1 h1] ∈ (subsequences_ending h1 r).to_finset
:= list.mem_to_finset.mpr (contains_last_true h1 r)

theorem largest_subsequence_ending_ne_zero
{X : Type*} [decidable_eq X]
{A : list X}
{n : ℕ}
(h1 : n < A.length)
(r : X → X → Prop) [decidable_rel r]
: ((subsequences_ending h1 r).to_finset).sup list.length ≠ 0
:= begin
  rw [(finset.insert_eq_of_mem (contains_last h1 r)).symm, finset.sup_insert],
  exact ne_of_gt (le_max_left 1 (finset.sup _ list.length)),
end

theorem subsequences_ending_increasing
{X : Type*} [decidable_eq X]
{A : list X}
{n1 n2 : ℕ}
(h1 : n1 < A.length)
(h2 : n2 < A.length)
(h3 : n1 < n2)
(r : X → X → Prop) [decidable_rel r]
(r_trans : transitive r)
(h4 : r (A.nth_le n1 h1) (A.nth_le n2 h2))
: ((subsequences_ending h1 r).to_finset).sup list.length < ((subsequences_ending h2 r).to_finset).sup list.length
:= begin
  obtain ⟨a, b, c⟩ := finset.exists_mem_eq_sup ((subsequences_ending h1 r).to_finset) _ list.length,
  { let newer := a.concat (A.nth_le n2 h2),
    have newer_in : newer ∈ (subsequences_ending h2 r).to_finset,
    { have kkk := list.mem_to_finset.mp b,
      dsimp [subsequences_ending] at kkk,
      rw list.mem_filter at kkk,
      apply list.mem_to_finset.mpr,
      dsimp [subsequences_ending],
      rw list.mem_filter,
      have thiny : newer = a ++ [A.nth_le n2 h2] := list.concat_eq_append (list.nth_le A n2 h2) a,
      split,
      { have newer_sub: newer <+ list.take n2.succ A := sublist_of_take_concat_sublist_of_take h2 h3 (list.mem_sublists.mp kkk.1),
        exact list.mem_sublists.mpr newer_sub, },
      { split,
        { dsimp [newer],
          rw list.concat_eq_append (list.nth_le A n2 h2) a,
          rw list.last'_append_of_ne_nil _ (list.cons_ne_nil (list.nth_le A n2 h2) list.nil),
          exact rfl, },
        { apply (list.chain'_iff_pairwise r_trans).mp _,
          apply list_chain_concat,
          { exact (list.chain'_iff_pairwise r_trans).mpr kkk.2.2, },
          { intros _ ku_in,
            rw option.mem_unique ku_in kkk.2.1,
            exact h4, } } } },
    rw c,
    have gflggl : a.length < newer.length := by { rw list.length_concat _ _, exact lt_add_one (list.length a),},
    exact gt_of_ge_of_gt (finset.le_sup newer_in) gflggl, },
  exact ⟨[A.nth_le n1 h1], contains_last h1 r⟩,
end

theorem subsequence_sup_short_exist
{X : Type*} [decidable_eq X]
{A : list X}
{n : ℕ}
(h : n < A.length)
(r : ℕ)
(R : X → X → Prop) [decidable_rel R]
(kk : (subsequences_ending h R).to_finset.sup list.length = r)
{nnn : ℕ}
(nle : nnn ≤ r)
: ∃ l, l <+ A ∧ l.length = nnn ∧ l.pairwise R
:= begin
  obtain ⟨aaa, memming, lenning⟩ := finset.exists_mem_eq_sup ((subsequences_ending h R).to_finset) _ list.length,
  { obtain ⟨aaa_pre, aaa_pairwise⟩ := is_sublist h R (list.mem_to_finset.mp memming),
    refine ⟨aaa.take nnn, _, _, _⟩,
    { exact list.sublist.trans (list.sublist_of_prefix (list.take_prefix nnn aaa)) aaa_pre, },
    { rw [list.length_take, lenning.symm, kk, min_eq_left_iff],
      exact nle, },
    { have take_sublist := list.sublist_of_prefix (list.take_prefix nnn aaa),
      exact list.pairwise_of_sublist take_sublist aaa_pairwise, } },
  exact ⟨[A.nth_le n h], contains_last h R⟩,
end

theorem subsequences_ending_image
{X : Type*} [decidable_eq X]
{A : list X}
{x : ℕ}
(x_le : x < A.length)
(k : ℕ)
(R : X → X → Prop) [decidable_rel R]
(h : transitive R)
(h1: ∀ (x : list X), ¬(x <+ A ∧ x.length = k ∧ list.pairwise R x))
: ((subsequences_ending x_le R).to_finset).sup list.length ∈ finset.range k \ {0}
:= begin
  apply finset.mem_sdiff.mpr,
  split,
  { rw finset.mem_range,
    by_contradiction,
    simp only [fin.val_eq_coe, not_lt] at h,
    let lenner := (subsequences_ending x_le R).to_finset.sup list.length,
    obtain ⟨ll, h_ll⟩ := subsequence_sup_short_exist x_le lenner R rfl h,
    exact (h1 ll) h_ll, },
  { apply finset.not_mem_singleton.mpr,
    exact largest_subsequence_ending_ne_zero x_le R, }
end

/- **Erdős–Szekeres theorem** -/
theorem erdos_szekeres
{X : Type*} [linear_order X]
(A : list X)
(r s : ℕ)
(h : (r-1)*(s-1) < A.length)
:   (∃ (R : list X), R <+ A ∧ R.length = r ∧ R.pairwise (≤))
  ∨ (∃ (S : list X), S <+ A ∧ S.length = s ∧ S.pairwise (≥))
:= begin
  by_cases hr : (1 ≤ r),
  by_cases hs : (1 ≤ s),

  -- We assume the sequences don't exist.
  { by_contradiction, 
    simp only [not_or_distrib, not_exists] at h,
    cases h,

    -- Label each number nᵢ in the sequence with the pair (aᵢ, bᵢ), where aᵢ is
    -- the length of the longest monotonically increasing subsequence ending with
    -- nᵢ and bᵢ is the length of the longest monotonically decreasing subsequence
    -- ending with nᵢ
    let f := (λ (i : (fin (A.length))), ((subsequences_ending i.2 (≤)).to_finset.sup list.length, (subsequences_ending i.2 (≥)).to_finset.sup list.length) ),
    let B := (list.fin_range A.length).map f,
    have aaaa: B.length = (list.fin_range A.length).length := by {dsimp [B], exact list.length_map f (list.fin_range (A.length)), },
    have se: A.length = B.length := (finset.card_fin A.length).symm.trans aaaa.symm,

    -- Each two numbers in the sequence are labeled with a different pair
    have B_nodup : B.nodup,
    { unfold list.nodup,
      apply list.pairwise_iff_nth_le.mpr,
      intros ii jj hhj hh2,
      let bi                    := B.nth_le ii (lt_trans hh2 hhj),
      let bj                    := B.nth_le jj hhj,
      have hhi  : ii < B.length := lt_trans hh2 hhj,
      have hhia : ii < A.length := by {rw se, exact hhi},
      have hhja : jj < A.length := by {rw se, exact hhj},
      have hhfi : ii < (list.fin_range A.length).length := by {rw [ list.length_fin_range, se ], exact hhi,},
      have hhfj : jj < (list.fin_range A.length).length := by {rw [ list.length_fin_range, se ], exact hhj,},
      apply (prod_ne_iff_right_or_left_ne bi bj).mp,
      dsimp [bj, bi],
      by_cases lt_ind : (A.nth_le ii hhia ≤ A.nth_le jj hhja),
      refine or.inl _,
      rotate,
      refine or.inr _,
      all_goals
      { refine ne_of_lt _,
        rw list.nth_le_map _ hhj hhfj,
        rw list.nth_le_map _ hhi hhfi,
        simp only [list.nth_le_fin_range], },
      exact subsequences_ending_increasing hhia hhja hh2 (≥) (@ge_trans X _) (le_of_not_ge lt_ind),
      exact subsequences_ending_increasing hhia hhja hh2 (≤) preorder.le_trans lt_ind, },

    let values : finset (ℕ × ℕ) := ⟨↑B, B_nodup⟩,
    have v_card : values.card = A.length := eq.symm se,
    let poss_values : finset (ℕ × ℕ) := finset.product ((finset.range r) \ {0}) ((finset.range s) \ {0}),
    have pv_card: poss_values.card = (r-1)*(s-1),
    { rw [finset.card_product, ←finset.range_one, finset.card_sdiff (finset.range_subset.mpr hr), finset.card_sdiff (finset.range_subset.mpr hs)],
      repeat { rw finset.card_range, }, },

    have hc : poss_values.card < values.card := by {rw [v_card, pv_card], exact h, },

    -- But there are only (r − 1)(s − 1) possible labels if aᵢ is at most r − 1 and bᵢ is at most s − 1
    have incl : ∀ x ∈ values, x ∈ poss_values,
    { intros xx xx_in_ttt,
      apply finset.mem_product.mpr,
      rw finset.mem_def at xx_in_ttt,
      change xx ∈ ((list.fin_range A.length).map f) at xx_in_ttt,
      rw list.mem_map at xx_in_ttt,
      obtain ⟨xx_ind, _, uuuu⟩ := xx_in_ttt,
      rw ←uuuu,
      split,
      exact subsequences_ending_image xx_ind.2 r (≤) preorder.le_trans h_left,
      exact subsequences_ending_image xx_ind.2 s (≥) (@ge_trans X _) h_right, },

    -- By the pigeonhole principle, two pairs must have the same value to fit in the range.
    obtain ⟨x, _, y, _, h⟩ := @finset.exists_ne_map_eq_of_card_lt_of_maps_to _ _ _ _ hc id incl,
    -- Contradiction
    exact (not_and_self (x = y)).mp h, },

  -- Special cases when s=0 ...
  { have s_eq_zero : s = 0, { linarith },
    refine or.inr (exists.intro list.nil _),
    rw s_eq_zero,
    exact ⟨list.nil_sublist A, rfl, list.pairwise.nil⟩, },
  -- ... or r=0
  { have r_eq_zero : r = 0, { linarith },
    refine or.inl (exists.intro list.nil _),
    rw r_eq_zero,
    exact ⟨list.nil_sublist A, rfl, list.pairwise.nil⟩, }

end

theorem erdos_szekeres_single
{X : Type*} [linear_order X]
(A : list X)
: ∃ (R : list X), R <+ A ∧ R.length = A.length.sqrt ∧ (R.pairwise (≤) ∨ R.pairwise (≥))
:= begin
  let l := A.length.sqrt,
  by_cases h : 1 ≤ A.length,
  { have one_le2 : A.length.sqrt ≠ 0 := mt (nat.sqrt_eq_zero).mp (ne_of_gt h),
    have leee := calc
            (A.length.sqrt - 1) * (A.length.sqrt - 1)
          ≤ A.length.sqrt * (A.length.sqrt - 1)       : nat_mul_sub_left_le A.length.sqrt (A.length.sqrt - 1)
      ... < A.length.sqrt * A.length.sqrt             : nat_mul_sub_right_lt one_le2 one_le2
      ... ≤ A.length                                  : (list.length A).sqrt_le,
    have list_erdos := erdos_szekeres A (A.length.sqrt) (A.length.sqrt) leee,
    cases list_erdos,
    { obtain ⟨R, rl, rp, pw⟩ := list_erdos,
      exact ⟨R, rl, rp, (or.inl pw)⟩, },
    { obtain ⟨R, rl, rp, pw⟩ := list_erdos,
      exact ⟨R, rl, rp, (or.inr pw)⟩, }, },
  { have len_eq_zero : A.length = 0 := by omega,
    rw (nat.sqrt_eq_zero.mpr len_eq_zero),
    exact ⟨list.nil, (list.nil_sublist A), (list.length_eq_zero.mpr rfl), (or.inl list.pairwise.nil)⟩, }
end

theorem finset_from_list_properties
{X Y: Type*} [linear_order X]
(A : finset X)
(r : ℕ)
(r1 : Y → Y → Prop)
(r1_refl : reflexive r1)
(f : X → Y)
(cses : ∃ (Rl : list Y), Rl <+ (A.sort (≤)).map f ∧ Rl.length = r ∧ list.pairwise r1 Rl)
: ∃ (R : finset X) (H : R ⊆ A), R.card = r ∧ ∀ (x : X), x ∈ R → ∀ (y : X), y ∈ R → x ≤ y → r1 (f x) (f y)
:= begin
  let li := (A.sort (≤)).map f,
  have bef_sorted     := finset.sort_sorted (≤) A,
  have bef_nodup      := finset.sort_nodup (≤) A,
  obtain ⟨r_list, r_list_sub, r_list_len, r_list_pairwise⟩ := cses,
  obtain ⟨bef_sub, bef_sub_sub, bef_sub_map_eq_r_list⟩ := sublist_map_exists r_list_sub,
  have bef_sub_sorted := list.pairwise_of_sublist bef_sub_sub bef_sorted,
  have bef_sub_nodup  := list.nodup_of_sublist bef_sub_sub bef_nodup,
  have yeppers        := finset_sort_idempotent bef_sub bef_sub_sorted bef_sub_nodup,
  let bef_sub_set     := bef_sub.to_finset,
  
  
  have bef_sub_set_sub : bef_sub_set ⊆ A,
  { intros _ xx_in,
    refine (finset.mem_sort (≤)).mp _,
    refine list.subset_def.mp (list.sublist.subset bef_sub_sub) _,
    exact list.mem_to_finset.mp xx_in, },
  have len : bef_sub_set.card = r,
  { rw [←r_list_len, ←bef_sub_map_eq_r_list, bef_sub.length_map f, ←yeppers],
    exact (finset.length_sort (≤)).symm, },
  refine ⟨bef_sub_set, bef_sub_set_sub, len, _⟩,
  { intros xx xx_in yy yy_in xx_le_yy,
    have xx_in' : xx ∈ bef_sub := list.mem_to_finset.mp xx_in,
    have yy_in' : yy ∈ bef_sub := list.mem_to_finset.mp yy_in,
    rw ←bef_sub_map_eq_r_list at r_list_pairwise,
    exact @pair_from_pairwise_to_pair_from_map X Y bef_sub f (≤) (@le_antisymm X _) r1 r1_refl bef_sub_sorted r_list_pairwise _ _ xx_in' yy_in' xx_le_yy,
    },
end

theorem erdos_szekeres''
{X Y: Type*} [linear_order X] [linear_order Y]
(r s : ℕ)
(A : finset X)
(h : (r-1)*(s-1) < A.card)
(f : X → Y)
: (∃ (R ⊆ A), R.card = r ∧ ∀ (x ∈ R) (y ∈ R), x ≤ y → f x ≤ f y)
∨ (∃ (S ⊆ A), S.card = s ∧ ∀ (x ∈ S) (y ∈ S), x ≤ y → f y ≤ f x)
:= begin
  let li := (A.sort (≤)).map f,
  have ye : (r - 1) * (s - 1) < li.length := by { rw [list.length_map, finset.length_sort], exact h, },
  have cses := erdos_szekeres li r s ye,
  cases cses,
  { exact or.inl (finset_from_list_properties A r (≤) (@le_rfl Y _) f cses), },
  { exact or.inr (finset_from_list_properties A s (≥) (@le_rfl Y _) f cses), },
end
