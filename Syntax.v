Require Import Automate.

Require Import Coq.Structures.Orders.

(* The Syntax of CPL in NNF. For simplicity, we restrict the type of
   variables to totally ordered things with Leibniz equality *)
Module MakeNNF (var_type : UsualOrderedType) <: UsualOrderedType.

Inductive Formula : Type :=
  | PosVar : var_type.t -> Formula
  | NegVar : var_type.t -> Formula
  | And : Formula -> Formula -> Formula
  | Or : Formula -> Formula -> Formula.
Hint Constructors Formula.

Lemma Formula_eq_dec : forall (f1 f2 : Formula), {f1=f2} + {f1 <> f2}.
decide equality; solve [apply var_type.eq_dec].
Defined.
Hint Resolve Formula_eq_dec.

(* The shapes of Formulae - these are needed to specify rules, and also
   in our ordering *)

Inductive isPosVar : Formula -> Prop := IsPosVar : forall v, isPosVar (PosVar v).
Inductive isNegVar : Formula -> Prop := IsNegVar : forall v, isNegVar (NegVar v).
Inductive isAnd : Formula -> Prop := IsAnd : forall f1 f2, isAnd (And f1 f2).
Inductive isOr : Formula -> Prop := IsOr : forall f1 f2, isOr (Or f1 f2).
Hint Constructors isPosVar isNegVar isAnd isOr.

(* And these are all decidable *)

Ltac isShape_dec shape := intro f; destruct f; crush_dec false shape.

Definition isPosVar_dec : forall f, {isPosVar f} + {~isPosVar f}. 
isShape_dec isPosVar. Defined.
Definition isNegVar_dec : forall f, {isNegVar f} + {~isNegVar f}.
isShape_dec isNegVar. Defined.
Definition isAnd_dec : forall f, {isAnd f} + {~isAnd f}.
isShape_dec isAnd. Defined.
Definition isOr_dec : forall f, {isOr f} + {~isOr f}.
isShape_dec isOr. Defined.

Notation "X <v Y" := (var_type.lt X Y) (at level 80).
Reserved Notation "X <f Y" (at level 80).

Inductive flt : Formula -> Formula -> Prop :=
  | PVar_fltS : forall v v', v <v v' -> PosVar v <f PosVar v'
  | PVar_fltD : forall v f, isNegVar f \/ isAnd f \/ isOr f -> PosVar v <f f
  | NVar_fltS : forall v v', v <v v' -> NegVar v <f NegVar v'
  | NVar_fltD : forall v f, isAnd f \/ isOr f -> NegVar v <f f
  | And_fltS1 : forall f1 f2 f3 f4, f1 <f f3 -> (And f1 f2) <f (And f3 f4)
  | And_fltS2 : forall f1 f2 f3, f2 <f f3 -> (And f1 f2) <f (And f1 f3)
  | And_fltD : forall f1 f2 f3, isOr f3 -> (And f1 f2) <f f3
  | Or_fltS1 : forall f1 f2 f3 f4, f1 <f f3 -> (Or f1 f2) <f (Or f3 f4)
  | Or_fltS2 : forall f1 f2 f3, f2 <f f3 -> (Or f1 f2) <f (Or f1 f3)
  where "X <f Y" := (flt X Y).
Hint Constructors flt.

Lemma var_type_irrefl : forall v, ~(v <v v). apply irreflexivity. Defined.

Lemma fltPosVar_irrefl : forall (v : var_type.t), ~(PosVar v <f PosVar v).
intros; inversion 1; crush' var_type_irrefl ((isOr, isAnd), isNegVar).
Defined.

Lemma fltNegVar_irrefl : forall (v : var_type.t), ~(NegVar v <f NegVar v).
intros; inversion 1; crush' var_type_irrefl (isOr, isAnd).
Defined.

Lemma flt_irrefl : forall (f : Formula), ~(f <f f).
induction f; inversion 1; crush' (fltPosVar_irrefl, fltNegVar_irrefl) isOr.
Defined.

Lemma var_type_trans : forall (v1 v2 v3 : var_type.t), v1 <v v2 -> v2 <v v3 -> v1 <v v3.
eapply transitivity.
Defined.

Lemma flt_trans : forall (f1 f2 f3 : Formula), f1 <f f2 -> f2 <f f3 -> f1 <f f3.
induction f1; destruct f2; destruct f3; try solve [crush' false (((isOr, isAnd), isNegVar), flt)];
repeat inversion 1; crush' var_type_trans (((isOr, isAnd), isNegVar), flt).
Defined.

Instance flt_strorder : StrictOrder flt := Build_StrictOrder flt flt_irrefl flt_trans.

Fixpoint compare (f1 f2 : Formula) : comparison := match f1 with
  | PosVar v => match f2 with
    | PosVar v' => var_type.compare v v'
    | _ => Lt
    end
  | NegVar v => match f2 with
    | PosVar _ => Gt
    | NegVar v' => var_type.compare v v'
    | _ => Lt
    end
 | And x y => match f2 with
    | PosVar _ | NegVar _ => Gt
    | And x' y' => match compare x x' with
      | Eq => compare y y'
      | res => res
      end
    | _ => Lt
    end
  | Or x y => match f2 with
    | Or x' y' => match compare x x' with
      | Eq => compare y y'
      | res => res
      end
    | _ => Gt
    end
  end.

Definition compare_spec : forall (f1 f2 : Formula),
  CompareSpec (f1 = f2) (f1 <f f2) (f2 <f f1) (compare f1 f2).
induction f1; destruct f2; crush; try solve [introvert (var_type.compare_spec t t0); crush];
repeat destruct_match;
repeat match goal with 
  [|- context[compare ?x ?y]] => let H := fresh "H" in
    destruct (compare x y) eqn:H 
  end; crush;
(* A little bit fragile, but it does the job. We just instantiate the induction
   hypotheses with the correct subtree, at which point inversion should provide 0 or
   1 constructors, which crush will discharge 
   TODO clean, or at least fix to handle unary operators *)
set (X1:=IHf1_1 f2_1); rewrite H in X1; try (set (X2:= IHf1_2 f2_2); rewrite H0 in X2);
crush' false CompareSpec.
Defined.

Fixpoint component_count (f : Formula) : nat := match f with
  | PosVar _ | NegVar _ => 0
  | And x y | Or x y => S (component_count x + component_count y)
  end.

Lemma component_count_wf : well_founded (fun f1 f2 => component_count f1 < component_count f2).
Proof.
unfold well_founded; intro f; constructor;
induction (component_count f); crush; constructor; crush.
Defined.

Lemma shrinking : forall (f1 f2 : Formula), component_count (And f1 f2) = component_count (Or f1 f2) /\ component_count f1 + component_count f2 < component_count (And f1 f2).
Proof.
crush.
Defined.  

(* Renamings and trivial definition so this module exports an OrderedType *)
Definition t := Formula.
Definition eq := @eq Formula.
Definition eq_dec := Formula_eq_dec.
Definition eq_equiv : Equivalence eq. unfold eq; constructor; crush. Defined.
Definition lt := flt.
Definition lt_strorder := flt_strorder.
Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt. intuition. Defined.

End MakeNNF.