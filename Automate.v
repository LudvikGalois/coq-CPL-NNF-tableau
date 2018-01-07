(* A few things for when CPDT's crush is overkill, also we export crush
   because it's so useful with tedious simple proofs *)
Require Export CpdtTactics.

(* Our assumption is that what's used in an if is a sumbool, so we don't need to keep X *)
Ltac destruct_if := repeat match goal with
  | [ H : context[if ?X then _ else _] |- _] => destruct X
  | [ |- context[if ?X then _ else _]] => destruct X
  end.

Ltac destruct_match := repeat match goal with
  | [ H : context[match ?X with _ => _ end] |- _] => let H := fresh "H" in destruct X eqn:H
  | [ |- context[match ?X with _ => _ end]] => let H := fresh "H" in destruct X eqn:H
  end.

(* "Borrowed" from CPDT *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

(* An imitation of Hol's RESTAC. Use for things in Prop only unless you want garbage code *)
Ltac restac := repeat match goal with
  | [ F : (?A -> _), a : ?A |- _] => extend (F a)
  | [ F : (?A <->  _), a : ?A |- _] => extend (proj1 F a)
  | [ F : (_ <-> ?A), a : ?A |- _] => extend (proj2 F a)
  | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
  end; try solve [intuition].

Hint Extern 4 => discriminate. (* I don't know why this isn't part of auto *)

(* crush specialised for sumbool *)
Ltac crush_dec lemmas invOne := 
  first [ solve [left; crush' lemmas invOne] 
        | solve [right; crush' lemmas invOne]
        | crush' lemmas invOne]. (* if not solved, simplify anyway *)

(* Introduce a new term and the call inversion on it *)
Ltac introvert expr := let H := fresh "H" in set (H := expr); inversion H; try subst.

Definition f_nat_lt_wf : forall {A : Type} (f : A -> nat), well_founded (fun x y => f x < f y).
Proof.
intros A f; unfold well_founded; intro a; constructor; induction (f a); [crush | constructor; crush ].
Defined.
Hint Immediate f_nat_lt_wf.
