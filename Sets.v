(* Sets of Formulae *)

Require Import Automate.
Require Import Syntax.

Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetInterface.
Require Coq.MSets.MSetProperties.
Require Import Ring.
Require Import ArithRing.
Require Import Omega.
Require Import Setoid.

Module SimpleNNF := MakeNNF Coq.Arith.PeanoNat.Nat.
Module SetNNF := Coq.MSets.MSetAVL.Make SimpleNNF.
Module SP := Coq.MSets.MSetProperties.OrdProperties SetNNF.

Ltac set_op_to_set_spec := repeat match goal with
  | [H : context[SetNNF.In _ (SetNNF.singleton _)] |- _] => rewrite SetNNF.singleton_spec in H
  | [ |- context[SetNNF.In _ (SetNNF.singleton _)]] => rewrite SetNNF.singleton_spec
  | [H : context[SetNNF.In _ (SetNNF.add _ _)] |- _] => rewrite SetNNF.add_spec in H
  | [ |- context[SetNNF.In _ (SetNNF.add _ _)]] => rewrite SetNNF.add_spec
  | [H : context[SetNNF.In _ (SetNNF.remove _ _)] |- _] => rewrite SetNNF.remove_spec in H
  | [ |- context[SetNNF.In _ (SetNNF.remove _ _)]] => rewrite SetNNF.remove_spec
  | [H : context[SetNNF.In _ (SetNNF.union _ _)] |- _] => rewrite SetNNF.union_spec in H
  | [ |- context[SetNNF.In _ (SetNNF.union _ _)]] => rewrite SetNNF.union_spec
  end.

Definition set_sum (f : SetNNF.elt -> nat) (S : SetNNF.t) := SetNNF.fold (fun x acc => f x + acc) S 0.

(* Why can't I find this? *)
Lemma fold_left_sum_acc : forall {A : Type} f (xs : list A) acc, List.fold_left (fun acc x => f x + acc) xs acc
 = acc + List.fold_left (fun acc x => f x + acc) xs 0.
induction xs; intuition. simpl. rewrite IHxs.
cut (f a + List.fold_left (fun acc x => f x + acc) xs 0 
  = List.fold_left(fun acc x => f x + acc) xs (f a + 0)). intros; omega.
rewrite <- IHxs. 
replace (f a + 0) with (f a); auto with arith.
Defined.

Lemma fold_left_sum_acc2 : forall {A : Type} f (xs : list A) n acc, List.fold_left (fun acc x => f x + acc) xs (acc+n)
 = acc + List.fold_left (fun acc x => f x + acc) xs n.
induction xs; intuition. simpl.
rewrite fold_left_sum_acc. rewrite (fold_left_sum_acc _ _ (f a + n)).
ring.
Defined.

Definition set_sum_acc : forall f s1 s2, set_sum f s1 + set_sum f s2 = 
  SetNNF.fold (fun x acc => f x + acc) s1 (set_sum f s2).
intros.
unfold set_sum.
extend (@SetNNF.fold_spec s1 nat). repeat rewrite H.
clear H.
induction (SetNNF.elements s1); auto. simpl.
assert (List.fold_left (fun (a0 : nat) (e : SetNNF.elt) => f e + a0) l (f a) =
 f a + List.fold_left (fun (a0 : nat) (e : SetNNF.elt) => f e + a0) l 0) by (apply fold_left_sum_acc; auto).
replace (f a + 0) with (f a); auto with arith.
rewrite fold_left_sum_acc2.
rewrite fold_left_sum_acc.
rewrite <- IHl. auto with arith.
Defined.

Definition sum_union : forall f s1 s2, (forall x, SetNNF.In x s1 -> ~SetNNF.In x s2) ->
  (set_sum f (SetNNF.union s1 s2)) = (set_sum f s1 + set_sum f s2).
intros.
rewrite set_sum_acc.
unfold set_sum.
rewrite SP.P.fold_union; crush.
exact (H x H1 H2).
Defined.

Definition set_component_count (S : SetNNF.t) : nat := set_sum SimpleNNF.component_count S.

Definition set_component_count_wf : well_founded 
  (fun x y => set_component_count x < set_component_count y).
Proof.
auto.
Defined.

Definition set_component_count_eq : forall s1 s2, SetNNF.eq s1 s2 -> set_component_count s1 = set_component_count s2.
intros. unfold set_component_count; unfold set_sum.
apply SP.fold_equal; crush.
Defined.
Hint Immediate set_component_count_eq.

(* Allow rewrites over set_component_count *)
Instance set_component_count_eq_inst : Morphisms.Proper (SetNNF.eq==>eq) set_component_count.
repeat red; crush.
Defined.

Definition set_component_shrinking : forall x s, ~ SetNNF.In x s -> SimpleNNF.component_count x > 0 -> 
  set_component_count s < set_component_count (SetNNF.union (SetNNF.singleton x) s).
intros. 
unfold set_component_count.
rewrite sum_union.
assert (set_sum SimpleNNF.component_count (SetNNF.singleton x) > 0).
unfold set_sum. 
rewrite SetNNF.fold_spec.
simpl. auto with arith.
omega.
intros. extend (SetNNF.singleton_spec x x0); crush.
Defined.

Lemma elements_nil_then_empty : forall x, SetNNF.elements x = nil -> SetNNF.Empty x.
Proof.
unfold SetNNF.Empty; crush; extend (SetNNF.elements_spec1 x a).
match goal with
  [H : SetNNF.elements ?x = nil |- _] => rewrite H in *
  end; crush' False SetoidList.InA.
Defined.
Hint Resolve elements_nil_then_empty.

Lemma empty_then_elements_nil : forall x, SetNNF.Empty x -> SetNNF.elements x = nil.
Proof.
unfold SetNNF.Empty; crush; extend (SetNNF.elements_spec1). 
match goal with
  [ |- SetNNF.elements ?x = nil] => destruct (SetNNF.elements x) eqn:?
  end; crush. extend (H e); extend (H0 x e).
destruct H2. enough False; intuition. refine (H1 (H2 _)).
rewrite Heql. constructor. trivial.
Defined.
Hint Resolve empty_then_elements_nil.

Lemma elements_nil_iff_empty : forall x, SetNNF.elements x = nil <-> SetNNF.Empty x.
Proof.
crush.
Defined.

Lemma sum_eq : forall (f : SimpleNNF.Formula -> nat) s1 s2, SetNNF.eq s1 s2 -> set_sum f s1 = set_sum f s2.
Proof.
unfold set_sum; intros; apply SP.fold_equal; crush.
Defined. 
Hint Resolve sum_eq.

(* The advantage of not doing this for all sets, but just our specific instantiations, is
   we can just prove through evaluation *)
Lemma fold_singleton : forall {A : Type} (f : SimpleNNF.Formula -> A -> A), forall x z, SetNNF.fold f (SetNNF.singleton x) z = f x z.
Proof.
crush.
Defined.
Hint Resolve fold_singleton.

