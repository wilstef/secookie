(** Support for atoms, i.e., objects with decidable equality.  We
    provide here the ability to generate an atom fresh for any finite
    collection, e.g., the lemma [atom_fresh_for_set], and a tactic to
    pick an atom fresh for the current proof context.

    Authors: Arthur Charguéraud and Brian Aydemir.

    Implementation note: In older versions of Coq, [OrderedTypeEx]
    redefines decimal constants to be integers and not natural
    numbers.  The following scope declaration is intended to address
    this issue.  In newer versions of Coq, the declaration should be
    benign. *)

Require Import List.
Require Import Max.
Require Import OrderedType.
Require Import OrderedTypeEx.
Open Scope nat_scope.

Require Import FSetDecide.
 

(* ********************************************************************** *)
(** * Definition *)

(** Atoms are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on atoms is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of atoms.  The [Export AtomImpl] line below allows
    us to refer to the type [atom] and its properties without having
    to qualify everything with "[AtomImpl.]". *)

Module Type ATOM.

  Parameter atom : Set.

  Parameter atom_fresh_for_list :
    forall (xs : list atom), {x : atom | ~ List.In x xs}.

  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.

  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module AtomImpl : ATOM.

  (* begin hide *)

  Definition atom := nat.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y; auto with arith.
      simpl. induction z. omega. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). omega. trivial.
  Qed.

  Module Atom_as_OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts Atom_as_OT.

  Definition eq_atom_dec : forall x y : atom, {x = y} + {x <> y} :=
    Facts.eq_dec.

  (* end hide *)

End AtomImpl.

Export AtomImpl.
