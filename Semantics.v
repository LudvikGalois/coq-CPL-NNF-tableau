(* Semantics for CPL in NNF with vars being nats *)

Require Import Automate.
Require Import Syntax.
Require Import Sets.
Require Import Coq.Arith.Arith.

Definition valuation := nat -> bool.

Reserved Notation "V |= X" (at level 60).
Reserved Notation "V |/= X" (at level 60).

(* I don't think this needs a proper induction scheme since
   we don't really induct over the shape of proofs here, only
   formulae. So we'll just stick with the broken scheme Coq
   gives us *)
Inductive is_true_at : valuation -> SimpleNNF.Formula -> Prop :=
  | pvar_true : forall V n, V n = true -> V |= SimpleNNF.PosVar n
  | nvar_true : forall V n, V n = false -> V |= SimpleNNF.NegVar n
  | and_true : forall V p q, V |= p -> V |= q -> V |= (SimpleNNF.And p q)
  | or_true : forall V p q, (V |= p \/ V |= q) -> V |= (SimpleNNF.Or p q)
  with is_false_at : valuation -> SimpleNNF.Formula -> Prop :=
  | pvar_false : forall V n, V n = false -> V |/= SimpleNNF.PosVar n
  | nvar_false : forall V n, V n = true -> V |/= SimpleNNF.NegVar n
  | and_false : forall V p q, (V |/= p \/ V |/= q) -> V |/= SimpleNNF.And p q
  | or_false : forall V p q, V |/= p -> V |/= q -> V |/= SimpleNNF.Or p q
  where "V |= X" := (is_true_at V X) and
        "V |/= X" := (is_false_at V X).
Hint Constructors is_true_at is_false_at.

Definition valuation_dec : forall V phi, {V |= phi} + {V |/= phi}.
induction phi; try solve [destruct (V t) eqn:H; auto]; crush.
Defined.

Definition two_valued_nature : forall V phi, V |= phi <-> ~(V |/= phi).
split; induction phi; try solve [do 2 inversion 1; crush];
try solve [intros; destruct (V t) eqn:?; crush];
destruct (valuation_dec V phi1); destruct (valuation_dec V phi2); crush.
Defined.

Definition two_valued_nature_neg : forall V phi, V |/= phi <-> ~(V |= phi).
intros; destruct (valuation_dec V phi); crush' two_valued_nature fail.
Defined.

Reserved Notation "V [|=] X" (at level 60).
Reserved Notation "V [|/=] X" (at level 60).

Inductive is_true_at_set : valuation -> SetNNF.t -> Prop :=
  | set_true : forall V gamma, (forall phi, SetNNF.In phi gamma -> V |= phi) -> V [|=] gamma 
 with is_false_at_set : valuation -> SetNNF.t -> Prop :=
  | set_false : forall V gamma, (exists phi, SetNNF.In phi gamma /\ V |/= phi) -> V [|/=] gamma
  where "V [|=] X" := (is_true_at_set V X) and
        "V [|/=] X" := (is_false_at_set V X).
Hint Constructors is_true_at_set is_false_at_set.

(* Another fragile proof, but I don't expect the definitions that I use in this to change *)
Definition valuation_list_dec : forall V gamma, 
  {forall phi, List.In phi gamma -> V |= phi} + {exists phi, List.In phi gamma /\ V |/= phi}.
intro V; induction gamma. left; intuition.
destruct (valuation_dec V a); 
  [ destruct IHgamma; [left; crush | right; crush; exists x; auto] 
  | right; exists a; crush]; intros.
Defined.


Definition InAIsIn : forall {A : Type} (x : A) (xs : list A), SetoidList.InA eq x xs <-> List.In x xs.
induction xs; crush' false SetoidList.InA. inversion H1; subst; crush.
Defined.
Hint Resolve InAIsIn.

(* It's often bad to rewrite in a use of auto, but this loses no information *)
Hint Extern 5 => match goal with
  [H : context[SetoidList.InA eq _ _] |- _] => rewrite InAIsIn in H
  end.

(* This is true because we only consider finite set of formulae *)
Definition valuation_set_dec : forall V gamma, {V [|=] gamma} + {V [|/=] gamma}.
intros; destruct (valuation_list_dec V (SetNNF.elements gamma)); 
  [left | right]; constructor; crush; try eapply ex_intro;
crush' SetNNF.elements_spec1 fail. 
Defined.

Definition valid (phi : SimpleNNF.Formula) := forall V, V |= phi.
Definition valid_set (gamma : SetNNF.t) := forall V, V [|=] gamma.

Definition satis (phi : SimpleNNF.Formula) := exists V, V |= phi.
Definition satis_set (gamma : SetNNF.t) := exists V, V [|=] gamma.

Definition unsatis (phi : SimpleNNF.Formula) := forall V, V |/= phi.
Definition unsatis_set (gamma : SetNNF.t) := forall V, V [|/=] gamma.

Hint Unfold valid valid_set satis satis_set unsatis unsatis_set.

Fixpoint negate (f : SimpleNNF.Formula) : SimpleNNF.Formula := match f with
  | SimpleNNF.PosVar v => SimpleNNF.NegVar v
  | SimpleNNF.NegVar v => SimpleNNF.PosVar v
  | SimpleNNF.And f1 f2 => SimpleNNF.Or (negate f1) (negate f2)
  | SimpleNNF.Or f1 f2 => SimpleNNF.And (negate f1) (negate f2)
  end.

Definition negate_spec : forall V f, V |= f <-> V |/= (negate f).
intro V; induction f; crush' false (is_true_at, is_false_at).
Defined.

Definition valid_unsatis_rel : forall f, valid f <-> unsatis (negate f).
induction f; unfold valid, unsatis; crush' negate_spec (is_true_at, is_false_at).
Defined.
