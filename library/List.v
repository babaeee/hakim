Import /Induction;
Import /Eq;

Axiom cons_nil_case: ∀ A: U, ∀ x: list A, x = nil A ∨ ∃ y: list A, ∃ a: A, x = cons A a y;

Axiom #1 head: ∀ A: U, A -> list A -> A;
Axiom head_nil: ∀ A: U, ∀ default: A, head default [] = default;
Axiom head_cons: ∀ A: U, ∀ default: A, ∀ x: list A, ∀ a: A, head default (cons A a x) = a;

Todo head_append_l: ∀ A: U, ∀ default: A, ∀ a b: list A, ~ a = [] -> head default (a + b) = head default a;

Axiom #1 tail: ∀ A: U, list A -> list A;
Axiom tail_nil: ∀ A: U, tail (nil A) = nil A;
Axiom tail_cons: ∀ A: U, ∀ x: list A, ∀ a: A, tail (cons A a x) = x;

Theorem cons_to_add_list: ∀ A: U, ∀ x: list A, ∀ a: A, cons A a x = [a] + x;
Proof; intros; auto_list; Qed;

Theorem tail_add: ∀ A: U, ∀ x: list A, ∀ a: A, tail ([a] + x) = x;
Proof; intros; auto_list; Qed;
Suggest goal default apply tail_add with label Trivial;
Theorem cons_head_tail: ∀ A: U, ∀ default: A, ∀ x: list A, ~ x = [] -> x = cons A (head default x) (tail x);
Proof;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (A));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (x));
    destruct cons_nil_case_ex_ex with (or_ind ? ?);
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (a a_property);
    destruct a_property with (ex_ind ? ?) to (y y_property);
    replace #2 (x) with (cons A y a);
    assumption;
    replace #2 (x) with (cons A y a);
    assumption;
    replace #1 (head default (cons A y a)) with (y);
    apply head_cons;
    replace #1 (tail (cons A y a)) with (a);
    apply tail_cons;
    assumption;
    assumption;
Qed;

Theorem add_head_tail: ∀ A: U, ∀ default: A, ∀ x: list A, ~ x = [] -> x = [ head default x ] + (tail x);
Proof; intros; destruct x; auto_list; replace #1 (head default (x0 :: l)) with (x0); auto_list; auto_list; Qed;

Suggest hyp default destruct $n with label l => l = [] ∨ l = x :: l';

Todo list_len_concat_lt: ∀ A: U, ∀ x y: list A, ~ x = nil A -> |y| < |x+y|;
Todo add_head: ∀ A: U, ∀ default: A, ∀ x: list A, ∀ a: A, head default ([a] + x) = a;
Suggest goal default apply add_head with label Trivial;
Todo Inhabit_not_empty_list: ∀ T: U, ∀ x: list T, |x| > 0 -> ∃ x: T, True;

Theorem list_induction_len: ∀ A: U, ∀ P: list A -> U, (∀ b: list A, (∀ a: list A, |a| < |b| -> P a) -> P b) -> ∀ a: list A, P a;
Proof;
    intros;
    add_hyp (∃ k, k = |a|);
    apply (ex_intro ? ? (|a|));
    auto_list;
    destruct H0 with (ex_ind ? ?) to (k k_property);
    add_hyp (0 ≤ k);
    lia;
    revert k_property;
    revert a;
    revert H0;
    revert k;
    apply z_induction_strong;
    intros;
    apply H;
    intros;
    apply (⁨H1 (|a0|) ?2 ?4 ?6 ?8⁩);
    auto_list;
    lia;
    lia;
Qed;

Todo cons_eq: ∀ T: U, ∀ x y: list T, ∀ a b, a :: x = b :: y -> a = b ∧ x = y; 
Todo append_eq: ∀ T: U, ∀ a b c d: list T, |a| = |b| -> a + c = b + d -> a = b ∧ c = d;

Todo tail_len: ∀ T: U, ∀ x: list T, ∀ n: ℤ, |x| = n + 1 → |tail x| = n;
Suggest goal auto apply tail_len with label Trivial;

Theorem list_len_gt_0: ∀ A: U, ∀ x: list A, 0 ≤ |x|;
Proof;
    intros A;
    apply list_induction_len;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (A));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b));
    destruct cons_nil_case_ex_ex with (or_ind ? ?);
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (a a_property);
    destruct a_property with (ex_ind ? ?) to (e e_property);
    add_hyp H_ex := (H (a));
    replace #1 (|b|) with (|a| + 1);
    replace #1 (b) with (cons A e a);
    assumption;
    lia;
    Seq (add_hyp (⁨|a| < |b|⁩)) (remove_hyp H_ex) (Switch 1) (add_hyp H_ex_o := (H_ex H0)) (remove_hyp H0) (remove_hyp H_ex) ;
    lia;
    replace #1 (b) with (cons A e a);
    assumption;
    lia;
    lia;
Qed;
Theorem nil_unique: ∀ A: U, ∀ l: list A, |l| = 0 -> l = [];
Proof;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (A));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (l));
    destruct cons_nil_case_ex_ex with (or_ind ? ?);
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property);
    destruct y_property with (ex_ind ? ?) to (a a_property);
    replace #1 (l) with (cons A a y) in H;
    assumption;
    lia;
    assumption;
Qed;
Suggest hyp default apply nil_unique in $n with label |l| = 0 => l = [];
Axiom #1 repeat: ∀ A: U, ℤ -> A -> list A;
Axiom repeat_intro: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> repeat t x = [x] + repeat (t - 1) x;
Todo repeat_unique: ∀ A: U, ∀ x: A, ∀ l: list A, cnt x l = |l| -> l = repeat (|l|) x;
Todo repeat_len: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> |repeat t x| = t;
Todo repeat_cnt: ∀ A: U, ∀ x: A, ∀ t: ℤ, 0 ≤ t -> cnt x (repeat t x) = t;
Todo repeat_cnt_others: ∀ A: U, ∀ x y: A, ∀ t: ℤ, 0 ≤ t -> ~ x = y -> cnt y (repeat t x) = 0;
Todo repeat_head: ∀ A: U, ∀ default: A, ∀ x: A, ∀ t: ℤ, 0 < t -> head default (repeat t x) = x;

Axiom #1 member_set: ∀ A: U, list A -> set A;
Todo member_set_subset: ∀ A: U, ∀ l: list A, ∀ m: set A, member_set l ⊆ m -> l = [] ∨ ∃ h: A, ∃ t: list A, h ∈ m ∧ l = [h] + t ∧ member_set t ⊆ m;
Todo member_set_empty: ∀ A: U, member_set (nil A) = {};
Todo member_set_singleton: ∀ A: U, ∀ x: A, member_set ([x]) = {x};
Todo member_set_add: ∀ A: U, ∀ a: A, ∀ l: list A, member_set ([a] + l) = {a} ∪ member_set l;
Todo member_set_append: ∀ A: U, ∀ x y: list A, member_set (x + y) = member_set x ∪ member_set y;
Todo member_set_cons: ∀ T: U, ∀ x: list T, ∀ a: T, a ∈ member_set (cons T a x);
Todo member_set_cons_union: ∀ T: U, ∀ x: list T, ∀ a: T, member_set (a :: x) = {a} ∪ member_set x;
Todo head_in_member_set: ∀ T: U, ∀ x: list T, ∀ default: T, (head default x) ∈ member_set x;
Todo member_set_repeat: ∀ T: U, ∀ x: T, ∀ t: ℤ, 0 < t -> member_set (repeat t x) = {x};
Todo member_set_nil_included: ∀ A: U, ∀ S: set A, member_set (nil A) ⊆ S;
Suggest goal auto apply member_set_empty with label Trivial;
Suggest goal auto apply member_set_singleton with label Trivial;
Suggest goal auto apply member_set_append with label Trivial;

Axiom inlist_nil: ∀ A: U, ∀ a: A, a in [] -> False;
Axiom inlist_unfold: ∀ A: U, ∀ l: list A, ∀ a x: A, a in [x] + l -> a = x ∨ a in l;
Axiom inlist_fold: ∀ A: U, ∀ l: list A, ∀ a x: A, a = x ∨ a in l -> a in [x] + l;
Todo inlist_singleton: ∀ A: U, ∀ a x: A, a in [x] -> a = x; 
Todo inlist_append: ∀ A: U, ∀ x y: list A, ∀ a: A, a in x + y -> a in x ∨ a in y;
Suggest hyp default apply inlist_unfold in $n with label a in [x] + l => a = x ∨ a in l;
Suggest goal default apply inlist_fold with label a in [x] + l => a = x ∨ a in l;
Suggest hyp default apply inlist_append in $n with label a in x + y => a in x ∨ a in y;

Todo inlist_member_set: ∀ A: U, ∀ a: A, ∀ l: list A, a in l -> a ∈ member_set l;
Suggest goal default apply inlist_member_set with label a ∈ member_set l => a in l;
Todo member_set_inlist: ∀ A: U, ∀ a: A, ∀ l: list A, a ∈ member_set l -> a in l;
Suggest hyp default apply member_set_inlist in $n with label a ∈ member_set l => a in l;

Todo inlist_append_r: ∀ A: U, ∀ x y: list A, ∀ a: A, a in x ∨ a in y -> a in x + y; 
Suggest goal default apply inlist_append_r with label a in x + y => a in x or a in y;

Axiom #1 unique_elements: ∀ A: Universe, list A -> Universe;
Axiom unique_elements_unfold: ∀ A: U, ∀ a: A, ∀ l: list A, unique_elements ([a] + l) -> ~ a in l ∧ unique_elements l;
Axiom unique_elements_fold: ∀ A: U, ∀ a: A, ∀ l: list A, ~ a in l ∧ unique_elements l -> unique_elements ([a] + l);
Axiom unique_elements_nil: ∀ A: U, unique_elements (nil A);
Todo unique_elements_sing: ∀ A: U, ∀ a: A, unique_elements [a];
Todo unique_elements_cons_fold: ∀ A: U, ∀ a: A, ∀ l: list A, ~ a in l ∧ unique_elements l -> unique_elements (a :: l);
Todo unique_elements_cons_unfold: ∀ A: U, ∀ a: A, ∀ l: list A, unique_elements (a :: l) -> ~ a in l ∧ unique_elements l;
Suggest hyp default apply unique_elements_unfold in $n with label unique_elements ([x] + l) => ~ x in l ∧ unique_elements l;
Suggest goal default apply unique_elements_fold with label unique_elements ([x] + l) => ~ x in l ∧ unique_elements l;
Suggest goal default apply unique_elements_nil with label Trivial;
Suggest goal default apply unique_elements_sing with label Trivial;
Suggest goal default apply unique_elements_cons_fold with label unique_elements (a :: l) =>  ~ a in l ∧ unique_elements l;
Suggest hyp default apply unique_elements_cons_unfold in $n with label unique_elements (a :: l) =>  ~ a in l ∧ unique_elements l;

Todo unique_elements_append: ∀ A: U, ∀ x y: list A, unique_elements (y + x) -> unique_elements(x + y);
Suggest goal default apply unique_elements_append with label unique_elements (x + y) =>  unique_elements (y + x);

Todo listing_set: ∀ T: U, ∀ S: set T, finite S -> ∃ l: list T, member_set l = S ∧ |l| = |S| ∧ unique_elements l;

Theorem split_index: ∀ T: U, ∀ l: list T, ∀ i, 0 < i -> i ≤ |l| -> ∃ x y, ∃ a, l = x + a :: y ∧ |x| = i - 1 ∧ |y| = |l| - i;
Proof;
    intros;
    add_hyp (1 ≤ i);
    lia;
    remove_hyp H;
    revert H0;
    revert l;
    revert H1;
    revert i;
    apply z_induction_simple;
    intros;
    add_hyp H0_ex := (H0 (l));
    Seq (add_hyp (⁨n ≤ |l|⁩)) (remove_hyp H0_ex) (Switch 1) (add_hyp H0_ex_o := (H0_ex H1)) (remove_hyp H1) (remove_hyp H0_ex) ;
    destruct H0_ex_o with (ex_ind ? ?) to (x x_property);
    destruct x_property with (ex_ind ? ?) to (y y_property);
    destruct y_property with (ex_ind ? ?) to (a a_property);
    destruct y;
    lia;
    apply (ex_intro ? ? (x + [a]));
    apply (ex_intro ? ? (l0));
    apply (ex_intro ? ? (x0));
    destruct a_property with (and_ind ? ?) to (a_property_l a_property_r);
    apply and_intro;
    lia;
    rewrite a_property_l;
    auto_list;
    lia;
    intros;
    apply (ex_intro ? ? ([]));
    destruct l;
    lia;
    apply (ex_intro ? ? (l0));
    apply (ex_intro ? ? (x));
    apply and_intro;
    lia;
    auto_list;
Qed;

Todo inlist_split: ∀ T: U, ∀ l: list T, ∀ a, a in l -> ∃ i, 0 ≤ i ∧ i < |l| ∧ ∃ x y, |x| = i ∧ |y| = |l| - i - 1 ∧ l = x + a :: y;

Axiom #1 firstn: ∀ T: U, list T -> ℤ -> list T;
Axiom firstn_nil: ∀ T: U, ∀ n: ℤ, firstn (nil T) n = [];
Axiom firstn_cons: ∀ T: U, ∀ a: T, ∀ l: list T, ∀ n: ℤ, n ≥ 0 -> firstn (a::l) (n + 1) = a::firstn l n;
Axiom firstn_le_0: ∀ T: U, ∀ l: list T, ∀ n: ℤ, 0 ≥ n -> firstn l n = []; 
Todo firstn_gt_len: ∀ T: U, ∀ l: list T, ∀ n: ℤ, n > |l| -> firstn l n = l;
Todo firstn_len: ∀ T: U, ∀ l: list T, firstn l (|l|) = l;
Todo firstn_cons_1: ∀ T: U, ∀ l: list T, ∀ a, firstn (a::l) 1 = [a];
Todo firstn_append_l: ∀ T: U, ∀ a b: list T, ∀ m, |a| ≥ m -> firstn (a + b) m = firstn a m;
Todo firstn_append_r: ∀ T: U, ∀ a b: list T, ∀ m, m ≥ 0 -> firstn (a + b) (|a| + m) = a + firstn b m;
Todo firstn_append_l_len: ∀ T: U, ∀ a b: list T, firstn (a + b) (|a|) = a;
Todo cnt_of_firstn_dis_range: ∀ T: U, ∀ a: list T, ∀ m, ∀ c, 0 ≤ cnt c (firstn a m) - cnt c (firstn a (m - 1)) ∧ cnt c (firstn a m) - cnt c (firstn a (m - 1)) ≤ 1;
Todo cnt_of_firstn_dis_1: ∀ T: U, ∀ a: list T, ∀ m, ∀ c, cnt c (firstn a m) = cnt c (firstn a (m - 1)) + 1 -> firstn a m = firstn a (m - 1) + [c];
Todo member_set_firstn: ∀ T: U, ∀ l: list T, ∀ i, member_set (firstn l i) ⊆ member_set l;
Todo len_firstn: ∀ T: U, ∀ l: list T, ∀ i, 0 ≤ i -> i ≤ |l| -> |firstn l i| = i; 
Todo firstn_firstn: ∀ T: U, ∀ l: list T, ∀ i j, i ≤ j -> firstn (firstn l j) i = firstn l i;

Axiom #1 skipn: ∀ T: U, list T -> ℤ -> list T;
Axiom skipn_nil: ∀ T: U, ∀ n: ℤ, skipn (nil T) n = [];
Axiom skipn_cons: ∀ T: U, ∀ a: T, ∀ l: list T, ∀ n: ℤ, n ≥ 0 -> skipn (a::l) (n + 1) = skipn l n;
Axiom skipn_le_0: ∀ T: U, ∀ l: list T, ∀ n: ℤ, 0 ≥ n -> skipn l n = l;
Todo skipn_append_l: ∀ T: U, ∀ a b: list T, ∀ i: ℤ, |a| ≥ i -> skipn (a + b) i = skipn a i + b;
Todo skipn_append_r: ∀ T: U, ∀ a b: list T, ∀ i: ℤ, i ≥ 0 -> skipn (a + b) (|a| + i) = skipn b i;
Todo skipn_append_l_len: ∀ T: U, ∀ a b: list T, skipn (a + b) (|a|) = b;
Todo skipn_len: ∀ T: U, ∀ l: list T, skipn l (|l|) = [];

Todo firstn_skipn: ∀ T: U, ∀ l: list T, ∀ i: ℤ, l = firstn l i + skipn l i;

Axiom #2 map: ∀ X Y: U, (X -> Y) -> list X -> list Y;
Axiom map_nil: ∀ X Y: U, ∀ f: X -> Y, map f [] = [];
Axiom map_cons: ∀ X Y: U, ∀ f: X -> Y, ∀ x, ∀ l, map f (x::l) = (f x)::map f l;
Todo map_len: ∀ X Y: U, ∀ f: X -> Y, ∀ l, |map f l| = |l|;
Todo map_f_o_g: ∀ X Y Z: U, ∀ f: Y -> Z, ∀ g: X -> Y, ∀ l, map f (map g l) = map (λ x, f (g x)) l;
Todo map_eq: ∀ X Y: U, ∀ f: X -> Y, ∀ g: X -> Y, ∀ l, (∀ a, a in l -> f a = g a) -> map f l = map g l;
Todo map_identity: ∀ X: U, ∀ f: X -> X, ∀ l, (∀ a, a in l -> f a = a) ->  map f l = l;
Todo firstn_map: ∀ X Y: U, ∀ f: X -> Y, ∀ l, ∀ i, firstn (map f l) i = map f (firstn l i);
Todo injective_map: ∀ X Y: U, ∀ f: X -> Y, ∀ S: set (list X), ∀ D: set X, (∀ l, l ∈ S -> member_set l ⊆ D) -> injective f D -> injective (map f) S;

Axiom #2 fold_left: ∀ X Y: U, (X -> Y -> X) -> X -> list Y -> X;
Axiom fold_left_nil: ∀ X Y: U, ∀ f: X -> Y -> X, ∀ hesab_shode: X, ∀ l: list Y, fold_left f hesab_shode l = hesab_shode;
Axiom fold_left_cons: ∀ X Y: U, ∀ f: X -> Y -> X, ∀ hesab_shode: X, ∀ y: Y, ∀ l: list Y, fold_left f hesab_shode (y::l) = fold_left f (f hesab_shode y) l;
Todo fold_left_append: ∀ X Y: U, ∀ f: X -> Y -> X, ∀ hesab_shode: X, ∀ a b: list Y, fold_left f hesab_shode (a + b) = fold_left f (fold_left f hesab_shode a) b;
Theorem fold_left_map: ∀ X Y Z: U, ∀ f: X -> Y -> X, ∀ hesab_shode: X, ∀ l: list Z, ∀ g: Z -> Y, fold_left f hesab_shode (map g l) = fold_left (λ x, λ z, f x (g z)) hesab_shode l;
Proof;
    intros;
    revert hesab_shode;
    revert l;
    apply list_induction_len;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (Z));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b));
    destruct cons_nil_case_ex_ex with (or_ind ? ?);
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (l l_property);
    destruct l_property with (ex_ind ? ?) to (z z_property);
    rewrite z_property;
    replace #1 ((map g (z :: l))) with (g z :: (map g l));
    apply map_cons;
    replace #1 (fold_left f hesab_shode (g z :: map g l)) with (fold_left f (f hesab_shode (g z))  (map g l));
    apply (⁨fold_left_cons ?0 ?2 f ?6 ?8 ?10⁩);
    replace #1 (fold_left (λ x: X, λ z0: Z, f x (g z0)) hesab_shode (z :: l)) with (fold_left (λ x: X, λ z0: Z, f x (g z0)) (f hesab_shode (g z)) l);
    apply (⁨fold_left_cons ?0 ?2 (λ x: X, λ z0: Z, f x (g z0)) ?6 ?8 ?10⁩);
    apply H;
    z3;
    rewrite cons_nil_case_ex_ex ;
    replace #1 ((map g [])) with ([]);
    apply map_nil;
    replace #1 (fold_left f hesab_shode []) with (hesab_shode);
    apply fold_left_nil;
    replace #1 (fold_left (λ x: X, λ z: Z, f x (g z)) hesab_shode []) with (hesab_shode);
    apply fold_left_nil;
    auto_list;
Qed;

Axiom #1 nth: ∀ X: U, X -> list X -> ℤ -> X; 
Axiom nth_nil: ∀ X: U, ∀ default: X, ∀ i, nth default ([]) i = default;
Axiom nth_0: ∀ X: U, ∀ default a: X, ∀ l, nth default (a :: l) 0 = a;
Axiom nth_cons: ∀ X: U, ∀ default a: X, ∀ l, ∀ i, nth default (a :: l) i = nth default l (i - 1);

Theorem nth_ge_len: ∀ X: U, ∀ default: X, ∀ l, ∀ i, |l| ≤ i -> nth default l i = default;
Proof;
    intros;
    revert H;
    revert i;
    revert l;
    apply list_induction_len;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (X));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b));
    destruct cons_nil_case_ex_ex with (or_ind ? ?);
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property);
    destruct y_property with (ex_ind ? ?) to (x x_property);
    rewrite x_property;
    replace #1 (nth default (x :: y) i) with (nth default (y) (i - 1));
    apply nth_cons;
    apply H;
    z3;
    z3;
    rewrite cons_nil_case_ex_ex ;
    apply nth_nil;
Qed;

Theorem nth_neg: ∀ X: U, ∀ default: X, ∀ l, ∀ i, i < 0 -> nth default l i = default;
Proof;
    intros;
    revert H;
    revert i;
    revert l;
    apply list_induction_len;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (X));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b));
    destruct cons_nil_case_ex_ex with (or_ind ? ?) ;
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property);
    destruct y_property with (ex_ind ? ?) to (x x_property);
    rewrite x_property ;
    replace #1 (nth default (x :: y) i) with (nth default (y) (i - 1));
    apply nth_cons;
    apply H;
    lia;
    z3;
    rewrite cons_nil_case_ex_ex ;
    apply nth_nil;
Qed;

Theorem nth_map: ∀ X Y: U, ∀ default: Y, ∀ default2: X, ∀ l: list X, ∀ f: X -> Y, ∀ i, 0 ≤ i -> i < |l| -> nth default (map f l) i = f (nth default2 l i);
Proof;
    intros;
    revert H0;
    revert H;
    revert i;
    revert l;
    apply list_induction_len;
    intros;
    add_from_lib cons_nil_case;
    add_hyp cons_nil_case_ex := (cons_nil_case (X));
    add_hyp cons_nil_case_ex_ex := (cons_nil_case_ex (b));
    destruct cons_nil_case_ex_ex with (or_ind ? ?) ;
    destruct cons_nil_case_ex_ex with (ex_ind ? ?) to (y y_property);
    destruct y_property with (ex_ind ? ?) to (x x_property);
    rewrite x_property ;
    replace #1 (map f (x :: y)) with (f x :: map f ( y));
    apply map_cons;
    destruct H0 with (or_ind ? ?) ;
    apply eq_sym in H0 ;
    rewrite H0 ;
    replace #1 (nth default (f x :: map f y) 0) with (f x);
    z3;
    replace #1 (nth default2 (x :: y) 0) with (x);
    z3;
    auto_list;
    replace #1 (nth default (f x :: map f y) i) with (nth default ( map f y) (i - 1));
    apply nth_cons;
    replace #1 (nth default2 (x :: y) i) with (nth default2 (y) (i - 1));
    z3;
    apply H;
    z3;
    lia;
    z3;
    z3;
Qed;

Todo nth_append_l: ∀ T: U, ∀ d: T, ∀ x y: list T, ∀ i, 0 ≤ i ∧ i < |x| -> nth d (x + y) i = nth d x i;
Todo nth_append_r: ∀ T: U, ∀ d: T, ∀ x y: list T, ∀ i, |x| ≤ i ∧ i < |x| + |y| -> nth d (x + y) i = nth d y (i - |x|);

Todo in_nth: ∀ X: U, ∀ default: X, ∀ i, ∀ l, 0 ≤ i ∧ i < |l| -> nth default l i in l;
Suggest goal default apply in_nth with label nth default l i in l =>  0 ≤ i ∧ i < |l|;
Todo nth_in: ∀ X: U, ∀ default: X, ∀ a, ∀ l, a in l -> (∃ i, 0 ≤ i ∧ i < |l| ∧ nth default l i = a);
Suggest hyp default apply nth_in in $n with label a in l => nth default l i = a;
Todo nth_eq: ∀ A: U, ∀ d: A, ∀ a b, |a| = |b| -> (∀ i, 0 ≤ i ∧ i < |a| -> nth d a i = nth d b i) -> a = b;
Suggest goal default apply nth_eq with label a = b => |a| = |b| and nth a i = nth b i;

Axiom #1 list_of_fun: ∀ X: U, ℤ -> (ℤ -> X) -> list X;
Axiom list_of_fun_not_pos: ∀ X: U, ∀ n, n ≤ 0 -> ∀ f: ℤ -> X, list_of_fun n f = [];
Axiom list_of_fun_nth: ∀ X: U, ∀ default: X, ∀ n, ∀ f: ℤ -> X, n > 0 -> ∀ i, 0 ≤ i -> i < n -> nth default (list_of_fun n f) i = f i;
Axiom list_of_fun_len: ∀ X: U, ∀ n, n > 0 -> ∀ f: ℤ -> X, |list_of_fun n f| = n;

