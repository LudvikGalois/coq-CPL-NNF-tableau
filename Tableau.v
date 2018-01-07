(* The Tableau itself *)
Require Import Automate Semantics Sets Syntax.
Require Import Coq.Arith.Arith. (* For eq_nat_dec *)

Notation "X ; Y" := (SetNNF.union X Y) (at level 90, right associativity).
Notation "{ x } ; Y" := (SetNNF.union (SetNNF.singleton x) Y) (at level 90, right associativity).

(* FUTURE WORK: merge validity rules into single type *)
Inductive valid_and_rule (f : SetNNF.t) : SetNNF.t -> Type :=
  | valid_and_rule_apply : forall p q Y, SetNNF.eq ({SimpleNNF.And p q}; Y) f -> 
  valid_and_rule f ({p}; {q};Y).

Inductive valid_close (f : SetNNF.t) : Prop :=
  | valid_close_apply : forall v Y, SetNNF.eq ({SimpleNNF.PosVar v}; {SimpleNNF.NegVar v}; Y) f ->
  valid_close f.

Inductive valid_or_rule (f : SetNNF.t) : SetNNF.t -> SetNNF.t -> Type :=
  | valid_or_rule_apply : forall p q Y, SetNNF.eq ({SimpleNNF.Or p q}; Y) f -> 
  valid_or_rule f ({p}; Y) ({q}; Y).

Instance unsatis_rw  : (Morphisms.Proper (Morphisms.respectful SetNNF.eq (Basics.flip Basics.impl)) unsatis_set).
repeat red. crush. constructor.
unfold unsatis_set in H0. (destruct (H0 V)).
destruct H1. exists x0. crush. 
Defined.

Definition close_sound : forall (f : SetNNF.t), valid_close f -> unsatis_set f.
intros f X. inversion X; subst.
rewrite <- H.
unfold unsatis_set.
intro V. destruct (V v) eqn:?.
constructor. exists (SimpleNNF.NegVar v). crush.
extend (SetNNF.union_spec 
       (SetNNF.singleton (SimpleNNF.PosVar v)) 
       ({SimpleNNF.NegVar v}; Y)
      (SimpleNNF.NegVar v)).
extend (SetNNF.union_spec
       (SetNNF.singleton (SimpleNNF.NegVar v)) Y (SimpleNNF.NegVar v)).
assert (forall x, SetNNF.In x (SetNNF.singleton x)). crush' SetNNF.singleton_spec fail.
crush.
constructor. exists (SimpleNNF.PosVar v). crush.
Defined.

(* TODO include the exact contradiction(s) in Closed to allow backjumping *)
Inductive Decision (F : SetNNF.t) : Type :=
  | Closed : unsatis_set F -> Decision F
  | Open : {V : valuation | (forall x, SetNNF.In x F -> V |= x)} -> Decision F.

(* These are used a bit, so let's just add them to the hint database *)
(* TODO move to sets *)
Lemma singleton_in : forall x, SetNNF.In x (SetNNF.singleton x).
crush' SetNNF.singleton_spec SetNNF.In.
Defined.
Hint Resolve singleton_in.

Lemma singleton_union : forall f X, SetNNF.In f ({f};X).
intros. pose (SetNNF.union_spec (SetNNF.singleton f) X f). crush.
Defined.
Hint Resolve singleton_union.

(* These proofs are a bit ugly and possibly could be automated quite a bit
   more *)
Definition and_sound : forall (f f' : SetNNF.t), valid_and_rule f f' -> Decision f' -> Decision f.
intros. inversion X; subst. destruct H; [apply Closed | apply Open].
rewrite <- H0.
unfold unsatis_set in *. crush. constructor.
pose (u V). inversion i; subst. destruct H.
destruct (SimpleNNF.eq_dec x p). exists (SimpleNNF.And p q). crush.
destruct (SimpleNNF.eq_dec x q). exists (SimpleNNF.And p q). crush.
exists x. assert (SetNNF.In x Y). 
assert (~SetNNF.In x (SetNNF.singleton p)).
intro. crush' SetNNF.singleton_spec fail.
assert (~SetNNF.In x (SetNNF.singleton q)) by crush' SetNNF.singleton_spec fail.
extend (SetNNF.union_spec (SetNNF.singleton p) ({q}; Y) x).
extend (SetNNF.union_spec (SetNNF.singleton q) Y x).
crush. extend (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.And p q)) Y x).
crush. destruct s.
exists x. intro. repeat red in H. extend (H0 x0). intuition.
assert (x |= p) by auto.
assert (x |= q). apply i. 
assert (SetNNF.In q ({q} ; Y)) by auto.
pose (SetNNF.union_spec (SetNNF.singleton p) ({q}; Y) q). crush.
assert (x |= (SimpleNNF.And p q)) by auto.
destruct (SimpleNNF.eq_dec x0 p); try solve [subst; auto].
destruct (SimpleNNF.eq_dec x0 q); try solve [subst; auto].
destruct (SimpleNNF.eq_dec x0 (SimpleNNF.And p q)); subst; auto.
apply i. 
extend (SetNNF.union_spec (SetNNF.singleton p) ({q}; Y) x0). 
extend (SetNNF.union_spec (SetNNF.singleton q) Y x0).
extend (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.And p q)) Y x0).
assert (SetNNF.In x0 Y). rewrite H8 in *.
destruct H6; auto. extend (SetNNF.singleton_spec (SimpleNNF.And p q)).
rewrite H10 in *. crush.
crush.
Defined.

Definition or_sound : forall (f fl fr : SetNNF.t), valid_or_rule f fl fr -> Decision fl -> Decision fr -> Decision f.
intros. inversion X; subst. destruct H eqn:?; [| apply Open].
destruct H0 eqn:?; [apply Closed| apply Open].
unfold unsatis_set in *. intro V. pose (u V); pose (u0 V).
inversion i; inversion i0; subst. destruct H2, H5.
constructor.
destruct (SimpleNNF.eq_dec x p).
destruct (SimpleNNF.eq_dec x0 q).
crush.
assert (V |/= (SimpleNNF.Or p q)).
crush.
exists (SimpleNNF.Or p q). crush.
repeat red in H1. apply H1. auto.
exists x0; crush. repeat red in H1; apply H1.
pose (SetNNF.union_spec (SetNNF.singleton q) Y x0).
rewrite i1 in H.
destruct H; auto.
pose (SetNNF.singleton_spec q x0). crush.
destruct (SimpleNNF.eq_dec x0 (SimpleNNF.Or p q)); subst; auto.
pose (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.Or p q)) Y x0).
crush.
exists x. crush. repeat red in H1; apply H1.
assert (SetNNF.In x Y).
pose (SetNNF.union_spec (SetNNF.singleton p) Y x).
pose (SetNNF.singleton_spec p x).
crush.
pose (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.Or p q)) Y x).
crush.
destruct s. crush. 
assert (x |= SimpleNNF.Or p q).
assert (x |= q). apply i. auto. crush.
exists x. crush. repeat red in H1. pose (H1 x0).
destruct (SimpleNNF.eq_dec x0 (SimpleNNF.Or p q)); subst; auto.
intuition. apply i.
assert (SetNNF.In x0 Y).
pose (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.Or p q)) Y x0).
rewrite i0 in H4. destruct H4; auto.
pose (SetNNF.singleton_spec (SimpleNNF.Or p q) x0); crush.
pose (SetNNF.union_spec (SetNNF.singleton q) Y x0); crush.
destruct s. crush. 
assert (x |= SimpleNNF.Or p q).
assert (x |= p). apply i. auto. crush.
exists x. crush. repeat red in H1. pose (H1 x0).
destruct (SimpleNNF.eq_dec x0 (SimpleNNF.Or p q)); subst; auto.
intuition. apply i.
assert (SetNNF.In x0 Y).
pose (SetNNF.union_spec (SetNNF.singleton (SimpleNNF.Or p q)) Y x0).
rewrite i0 in H5. destruct H5; auto.
pose (SetNNF.singleton_spec (SimpleNNF.Or p q) x0); crush.
pose (SetNNF.union_spec (SetNNF.singleton p) Y x0); crush.
Defined.

(* FUTURE WORK: Replace AndRule and OrRule with a single "Rule" *)
(* FUTURE WORK: Add a variant of Or with backjumping *)
Inductive Tableau (F : SetNNF.t) : (Decision F) -> Type :=
  | ClosedTableau : forall (p : valid_close F), Tableau F (Closed F (close_sound F p))
  | OpenTableau : forall (p : {V : valuation | (forall x, SetNNF.In x F -> V |= x)}), Tableau F (Open F p)
  | AndRule : forall F' (D : Decision F') (p : valid_and_rule F F'), Tableau F' D -> Tableau F (and_sound F F' p D)
  | OrRule : forall FL FR (DL : Decision FL) (DR : Decision FR) (p : valid_or_rule F FL FR), Tableau FL DL -> Tableau FR DR -> Tableau F (or_sound F FL FR p DL DR).

(* TODO The following 2 proofs are very similar, factor out re-used code *)
Definition has_and (F : SetNNF.t) : {x : SimpleNNF.Formula * SimpleNNF.Formula | SetNNF.In (SimpleNNF.And (fst x) (snd x)) F} + (forall x, SetNNF.In x F -> ~SimpleNNF.isAnd x).
refine (match SetNNF.choose (SetNNF.filter (fun x => if SimpleNNF.isAnd_dec x then true else false) F) as H' return 
  SetNNF.choose (SetNNF.filter (fun x => if SimpleNNF.isAnd_dec x then true else false) F) = H' -> 
  {x : SimpleNNF.Formula * SimpleNNF.Formula | SetNNF.In (SimpleNNF.And (fst x) (snd x)) F} + (forall x, SetNNF.In x F -> ~SimpleNNF.isAnd x)
  with
  | None => _
  | Some x => _
  end eq_refl).
  intros. assert (SimpleNNF.isAnd x).
  extend (@SetNNF.filter_spec F x (fun x => if SimpleNNF.isAnd_dec x then true else false) _).
  intuition.
  destruct (SimpleNNF.isAnd_dec x); auto.
  assert (SetNNF.In x
       (SetNNF.filter (fun x : SetNNF.elt => if SimpleNNF.isAnd_dec x then true else false)
          F)).
  crush.
  crush.
  destruct x; try solve [contradict H0; inversion 1].
  left; exists (x1,x2).
  simpl.
  extend (@SetNNF.filter_spec F (SimpleNNF.And x1 x2) (fun x => if SimpleNNF.isAnd_dec x then true else false) _).
  extend (SetNNF.choose_spec1 H).
  crush.
  intros.
  extend (SetNNF.choose_spec2 H).
  right. intros.
  extend (@SetNNF.filter_spec F x (fun x => if SimpleNNF.isAnd_dec x then true else false) _).
  intuition.
  destruct (SimpleNNF.isAnd_dec x); auto.
  extend (H5 eq_refl).
  exact (H0 x H2).
Defined.

Definition has_or (F : SetNNF.t) : {x : SimpleNNF.Formula * SimpleNNF.Formula | SetNNF.In (SimpleNNF.Or (fst x) (snd x)) F} + (forall x, SetNNF.In x F -> ~SimpleNNF.isOr x).
refine (match SetNNF.choose (SetNNF.filter (fun x => if SimpleNNF.isOr_dec x then true else false) F) as H' return 
  SetNNF.choose (SetNNF.filter (fun x => if SimpleNNF.isOr_dec x then true else false) F) = H' -> 
  {x : SimpleNNF.Formula * SimpleNNF.Formula | SetNNF.In (SimpleNNF.Or (fst x) (snd x)) F} + (forall x, SetNNF.In x F -> ~SimpleNNF.isOr x)
  with
  | None => _
  | Some x => _
  end eq_refl).
  intros. assert (SimpleNNF.isOr x).
  extend (@SetNNF.filter_spec F x (fun x => if SimpleNNF.isOr_dec x then true else false) _).
  intuition.
  destruct (SimpleNNF.isOr_dec x); auto.
  assert (SetNNF.In x
       (SetNNF.filter (fun x : SetNNF.elt => if SimpleNNF.isOr_dec x then true else false)
          F)).
  crush.
  crush.
  destruct x; try solve [contradict H0; inversion 1].
  left; exists (x1,x2).
  simpl.
  extend (@SetNNF.filter_spec F (SimpleNNF.Or x1 x2) (fun x => if SimpleNNF.isOr_dec x then true else false) _).
  extend (SetNNF.choose_spec1 H).
  crush.
  intros.
  extend (SetNNF.choose_spec2 H).
  right. intros.
  extend (@SetNNF.filter_spec F x (fun x => if SimpleNNF.isOr_dec x then true else false) _).
  intuition.
  destruct (SimpleNNF.isOr_dec x); auto.
  extend (H5 eq_refl).
  exact (H0 x H2).
Defined.

(* TODO clean up with abbreviations *)
Definition has_cont (F : SetNNF.t) : {n : nat | SetNNF.In (SimpleNNF.PosVar n) F /\ SetNNF.In (SimpleNNF.NegVar n) F} + (forall n, SetNNF.In (SimpleNNF.PosVar n) F -> ~SetNNF.In (SimpleNNF.NegVar n) F).
refine (let pos := SetNNF.filter (fun x => if SimpleNNF.isPosVar_dec x then true else false) F
  in let neg := SetNNF.filter (fun f => match f with
  | SimpleNNF.PosVar n => SetNNF.mem (SimpleNNF.NegVar n) F
  | SimpleNNF.NegVar _ | SimpleNNF.And _ _ | SimpleNNF.Or _ _ => false
  end) pos in match SetNNF.choose neg as H return SetNNF.choose neg = H ->
  {n : nat | SetNNF.In (SimpleNNF.PosVar n) F /\ SetNNF.In (SimpleNNF.NegVar n) F} + (forall n, SetNNF.In (SimpleNNF.PosVar n) F -> ~SetNNF.In (SimpleNNF.NegVar n) F)   
  with
  | None => _
  | Some x => _
  end eq_refl).
intros.
left.
assert (SetNNF.In x neg) by auto with set.
assert (SetNNF.In x pos).
extend (@SetNNF.filter_spec pos x ((fun f : SetNNF.elt =>
          match f with
          | SimpleNNF.PosVar n => SetNNF.mem (SimpleNNF.NegVar n) F
          | SimpleNNF.NegVar _ => false
          | SimpleNNF.And _ _ => false
          | SimpleNNF.Or _ _ => false
          end)) _).
crush.
assert (SetNNF.In x F).
extend (@SetNNF.filter_spec F x (fun x : SetNNF.elt => if SimpleNNF.isPosVar_dec x then true else false) _).
crush.
destruct (SimpleNNF.isPosVar_dec x).
destruct x; try solve [contradict i; inversion 1].
exists n. intuition.
extend (@SetNNF.filter_spec pos (SimpleNNF.PosVar n) ((fun f : SetNNF.elt =>
          match f with
          | SimpleNNF.PosVar n => SetNNF.mem (SimpleNNF.NegVar n) F
          | SimpleNNF.NegVar _ => false
          | SimpleNNF.And _ _ => false
          | SimpleNNF.Or _ _ => false
          end)) _).
intuition.
extend (@SetNNF.filter_spec F x (fun x : SetNNF.elt => if SimpleNNF.isPosVar_dec x then true else false) _).
destruct (SimpleNNF.isPosVar_dec x); intuition.
intros; right; intros; intro.
assert (SetNNF.In (SimpleNNF.PosVar n) pos).
extend (@SetNNF.filter_spec F (SimpleNNF.PosVar n) (fun x : SetNNF.elt => if SimpleNNF.isPosVar_dec x then true else false) _).
crush.
assert (SetNNF.In (SimpleNNF.PosVar n) neg).
extend (@SetNNF.filter_spec pos (SimpleNNF.PosVar n) ((fun f : SetNNF.elt =>
          match f with
          | SimpleNNF.PosVar n => SetNNF.mem (SimpleNNF.NegVar n) F
          | SimpleNNF.NegVar _ => false
          | SimpleNNF.And _ _ => false
          | SimpleNNF.Or _ _ => false
          end)) _).
intuition.
extend (SetNNF.choose_spec2 H).
exact (H4 (SimpleNNF.PosVar n) H3).
Defined.

Definition make_satis_val (F : SetNNF.t) : (forall x : SetNNF.elt, SetNNF.In x F -> ~ SimpleNNF.isAnd x) ->
(forall x : SetNNF.elt, SetNNF.In x F -> ~ SimpleNNF.isOr x) ->
(forall n : nat, SetNNF.In (SimpleNNF.PosVar n) F -> ~ SetNNF.In (SimpleNNF.NegVar n) F) ->
{V : valuation | (forall x, SetNNF.In x F -> V |= x)}.
intros. exists (fun x => if SetNNF.mem (SimpleNNF.PosVar x) F then true else false).
intros.
destruct x.
constructor. destruct (SetNNF.mem (SimpleNNF.PosVar n) F) eqn:?; auto.
extend (SetNNF.mem_spec F (SimpleNNF.PosVar n)); crush.
constructor.
destruct (SetNNF.mem (SimpleNNF.PosVar n) F) eqn:?; auto.
extend (SetNNF.mem_spec F (SimpleNNF.NegVar n)).
extend (SetNNF.mem_spec F (SimpleNNF.PosVar n)).
intuition. contradict (H1 n H6 H3).
extend (H _ H2). contradict H3; auto.
extend (H0 _ H2). contradict H3; auto.
Defined.

Definition add_remove : forall f F, SetNNF.In f F -> SetNNF.eq ({f}; (SetNNF.remove f F)) F.
intros; intro a; extend (SetNNF.singleton_spec f a);
extend (SetNNF.union_spec (SetNNF.singleton f) (SetNNF.remove f F) a);
extend (SetNNF.remove_spec F f a); destruct (SimpleNNF.eq_dec f a); subst;
intuition.
Defined.

Definition add_remove2 : forall f f0 F, SetNNF.In f F -> SetNNF.In f0 F -> SetNNF.eq ({f}; {f0}; (SetNNF.remove f (SetNNF.remove f0 F))) F.
intros; intro a; destruct (SimpleNNF.eq_dec f a); destruct (SimpleNNF.eq_dec f0 a);
extend (SetNNF.singleton_spec f a); extend (SetNNF.singleton_spec f0 a);
extend (SetNNF.remove_spec (SetNNF.remove f0 F) f a);
extend (SetNNF.remove_spec F f0 a);
extend (SetNNF.union_spec (SetNNF.singleton f) ({f0}; (SetNNF.remove f (SetNNF.remove f0 F))) a); 
extend (SetNNF.union_spec (SetNNF.singleton f0) (SetNNF.remove f (SetNNF.remove f0 F)) a); subst;
intuition.
Defined. 
Hint Immediate add_remove add_remove2.


Definition not_in_self_AndL : forall x y, x <> (SimpleNNF.And x y).
Proof.
induction x; crush.
Defined.

Definition not_in_self_AndR : forall y x, y <> (SimpleNNF.And x y).
Proof.
induction y; crush.
Defined.

Definition not_in_self_OrL : forall x y, x <> (SimpleNNF.Or x y).
Proof.
induction x; crush.
Defined.

Definition not_in_self_OrR : forall y x, y <> (SimpleNNF.Or x y).
Proof.
induction y; crush.
Defined.

Lemma set_component_count_remove : forall f F, set_component_count (SetNNF.remove f F) <= set_component_count F.
intros.
destruct (SetNNF.mem f F) eqn:?.
destruct (SetNNF.mem_spec F f); intuition.
assert (SetNNF.eq F ({f}; (SetNNF.remove f F))) by (symmetry; auto).
rewrite H0 at 2. unfold set_component_count; rewrite sum_union. crush.
crush. destruct (SetNNF.singleton_spec f x); destruct (SetNNF.remove_spec F f x); crush.
assert (SetNNF.eq F (SetNNF.remove f F)).
intro a.
destruct (SetNNF.mem_spec F f); destruct (SetNNF.remove_spec F f a).
split; intros; auto. apply H2. split; auto.
intro; subst; crush.
crush.
rewrite H at 2; auto.
Defined.

Definition singleton_count : forall f, set_component_count (SetNNF.singleton f) = SimpleNNF.component_count f.
intros. unfold set_component_count. unfold set_sum. rewrite (SetNNF.fold_spec). simpl. crush.
Defined.
Hint Resolve singleton_count.

(* TODO reduce repetition by factoring out to Ltacs and Lemmas *)
Definition and_shrinking : forall f f0 F, SetNNF.In (SimpleNNF.And f f0) F -> 
  set_component_count ({f};{f0}; SetNNF.remove (SimpleNNF.And f f0) F) < set_component_count F.
intros.
assert (SimpleNNF.component_count f + SimpleNNF.component_count f0 < SimpleNNF.component_count (SimpleNNF.And f f0)) by crush.
assert (SetNNF.eq F ({SimpleNNF.And f f0}; (SetNNF.remove (SimpleNNF.And f f0) F))) by (symmetry; auto).
rewrite H1 at 2.
set (Y := SetNNF.remove (SimpleNNF.And f f0) F).
assert (SetNNF.eq ({f};{f0};Y) ({f};{f0}; (SetNNF.remove f (SetNNF.remove f0 Y)))).
set (Z := (SetNNF.remove f (SetNNF.remove f0 Y))).
intro a.
destruct (SetNNF.singleton_spec f a); destruct (SetNNF.singleton_spec f0 a);
destruct (SetNNF.union_spec (SetNNF.singleton f) ({f0};Y) a);
destruct (SetNNF.union_spec (SetNNF.singleton f) ({f0};Z) a);
destruct (SetNNF.union_spec (SetNNF.singleton f0) (Y) a);
destruct (SetNNF.union_spec (SetNNF.singleton f0) (Z) a);
destruct (SetNNF.remove_spec Y f0 a);
destruct (SetNNF.remove_spec (SetNNF.remove f0 Y) f a);
unfold Y,Z. destruct (SimpleNNF.eq_dec a f); destruct (SimpleNNF.eq_dec a f0); repeat subst; crush.
assert (set_component_count ({f}; {f0}; SetNNF.remove f (SetNNF.remove f0 Y)) < set_component_count ({SimpleNNF.And f f0}; SetNNF.remove f (SetNNF.remove f0 Y))).
destruct (SimpleNNF.eq_dec f f0); subst.
assert (SetNNF.eq ({f0}; {f0}; SetNNF.remove f0 (SetNNF.remove f0 Y)) ({f0}; SetNNF.remove f0 (SetNNF.remove f0 Y))).
intro a. repeat rewrite SetNNF.union_spec; repeat rewrite SetNNF.singleton_spec;
repeat rewrite SetNNF.remove_spec;
destruct (SimpleNNF.eq_dec f0 a); subst; crush.
rewrite H3.
unfold set_component_count; repeat rewrite sum_union; repeat rewrite singleton_count; crush;
unfold Y in *; set_op_to_set_spec; crush.
unfold set_component_count; repeat rewrite sum_union; repeat rewrite singleton_count; crush;
unfold Y in *; set_op_to_set_spec; crush.
rewrite <- H2 in H3.
eapply lt_le_trans. exact H3.
cut (set_component_count (SetNNF.remove f (SetNNF.remove f0 Y)) <= set_component_count Y).
intros. unfold set_component_count; repeat rewrite sum_union; crush;
unfold Y in *; set_op_to_set_spec; crush.
repeat rewrite set_component_count_remove; trivial.
Defined.

Definition or_shrinking : forall x f f0 F, (x=f\/x=f0) ->SetNNF.In (SimpleNNF.Or f f0) F -> 
  set_component_count ({x}; SetNNF.remove (SimpleNNF.Or f f0) F) < set_component_count F.
intros.
assert (SimpleNNF.component_count x < SimpleNNF.component_count (SimpleNNF.Or f f0)) by crush.
assert (SetNNF.eq F ({SimpleNNF.Or f f0}; (SetNNF.remove (SimpleNNF.Or f f0) F))) by (symmetry; auto).
rewrite H2 at 2.
set (Y := SetNNF.remove (SimpleNNF.Or f f0) F).
assert (SetNNF.eq ({x};Y) ({x}; (SetNNF.remove x Y))).
intro a. destruct (SimpleNNF.eq_dec a x); set_op_to_set_spec; crush.
cut (set_component_count (SetNNF.remove x Y) <= set_component_count Y).
intros.
rewrite H3.
unfold set_component_count; repeat rewrite sum_union; 
try solve [intros; intro; unfold Y in *; set_op_to_set_spec; crush];
repeat rewrite singleton_count. unfold set_component_count in H4. crush.
rewrite set_component_count_remove; trivial.
Defined.

Definition or_shrinkingl : forall f f0 F, SetNNF.In (SimpleNNF.Or f f0) F -> 
  set_component_count ({f}; SetNNF.remove (SimpleNNF.Or f f0) F) < set_component_count F.
intros; apply or_shrinking; crush.
Defined.

Definition or_shrinkingr : forall f f0 F, SetNNF.In (SimpleNNF.Or f f0) F -> 
  set_component_count ({f0}; SetNNF.remove (SimpleNNF.Or f f0) F) < set_component_count F.
intros; apply or_shrinking; crush.
Defined.

(* Write this, and we're done :D *)
(* Writing it this way is pretty bad style, but
   I wanted to see what this would extract to *)
Definition Tableau_Complete : forall (F : SetNNF.t), {res : Decision F & Tableau F res}.
induction F using (well_founded_induction_type set_component_count_wf).
destruct (has_and F).
inversion s; subst. destruct x; simpl in H.
pose ({f};{f0};(SetNNF.remove (SimpleNNF.And f f0) F)).
pose ({SimpleNNF.And f f0}; (SetNNF.remove (SimpleNNF.And f f0) F)).
assert (SetNNF.eq t0 F) by (apply add_remove; auto).
pose (valid_and_rule_apply F f f0 (SetNNF.remove (SimpleNNF.And f f0) F) H0).
pose (and_sound F t v).
assert (set_component_count t < set_component_count F) as H' by (apply and_shrinking; auto).
pose (X t H').
inversion s0; subst.
exists (d x).
apply AndRule; auto.
destruct (has_or F).
inversion s; subst. destruct x; simpl in H.
pose ({f};(SetNNF.remove (SimpleNNF.Or f f0) F)).
pose ({f0};(SetNNF.remove (SimpleNNF.Or f f0) F)).
pose ({SimpleNNF.Or f f0}; (SetNNF.remove (SimpleNNF.Or f f0) F)).
assert (SetNNF.eq t1 F) by (apply add_remove; auto).
pose (valid_or_rule_apply F f f0 (SetNNF.remove (SimpleNNF.Or f f0) F) H0).
pose (or_sound F t t0 v).
assert (set_component_count t < set_component_count F) as HL by (apply or_shrinkingl; auto).
assert (set_component_count t0 < set_component_count F) as HR by (apply or_shrinkingr; auto).
introvert (X t HL).
introvert (X t0 HR).
exists (d x x0).
apply OrRule; auto.
destruct (has_cont F).
assert (valid_close F).
inversion s; subst.
assert (SetNNF.eq ({SimpleNNF.PosVar x}; {SimpleNNF.NegVar x};
  SetNNF.remove (SimpleNNF.PosVar x) (SetNNF.remove (SimpleNNF.NegVar x) F)) F).
apply add_remove2; intuition.
apply (valid_close_apply F x (SetNNF.remove (SimpleNNF.PosVar x)
  (SetNNF.remove (SimpleNNF.NegVar x) F))); auto.
exists (Closed F (close_sound F H)).
apply ClosedTableau; auto.
exists (Open F (make_satis_val F n n0 n1)).
apply OpenTableau.
Defined.

(* Function to extract *)
Definition tableau_list (l : list SimpleNNF.Formula) := 
  let gamma := (List.fold_left (fun acc x => SetNNF.add x acc) l SetNNF.empty) in 
  match Tableau_Complete gamma with
  | existT _ (Closed _ y) tab => None
  | existT _ (Open _ (exist _ v _)) tab => Some v
  end.
