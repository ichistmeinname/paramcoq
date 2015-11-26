Require Import List.

Module MaybeMonad.

  Inductive option (A : Type) :=
  | Some : A -> option A
  | None : option A.


  (* Without Implicit Arguments *)

  (* Definition ret {A: Type} (x : A) := Some A x. *)
  (* Definition bind {A B : Type} (a : option A) (f: A -> option B) : option B := *)
  (*   match a with *)
  (*     | Some _ x => f x *)
  (*     | None _ => None B *)
  (*   end. *)

  Arguments Some {A} _.
  Arguments None {A}.

  Definition ret {A: Type} (x : A) := Some x.
  Definition bind {A B : Type} (a : option A) (f: A -> option B) : option B :=
    match a with
      | Some x => f x
      | None => None
    end.

  Lemma monad_left_identity :
    forall (A B : Type) (x : A) (f : A -> option B), bind (ret x) f = f x.
    repeat intro.
    compute.
    trivial.
  Qed.

  Lemma monad_right_identity :
    forall (A B : Type) (mx : option A), bind mx ret = mx.
    repeat intro.
    induction mx; compute; reflexivity.
  Qed.

  Lemma monad_associativity :
    forall (A B C : Type) (mx : option A) (f : A -> option B) (g : B -> option C),
      bind (bind mx f) g = bind mx (fun x => bind (f x) g).
    repeat intro.
    induction mx; compute.
    induction (f a); trivial.
    trivial.
  Qed.

End MaybeMonad.

Module ListMonad.

  (* Inductive list (A : Type) := *)
  (* | cons : A -> list A -> list A*)
  (* | nil : list A. *)

  Arguments nil {A}.
  Arguments cons {A} _ _.

  Definition ret {A : Type} (x : A) := cons x nil.
  Definition bind {A B : Type} (mx : list A) (f : A -> list B) : list B :=
    flat_map f mx.

  (* Fixpoint bind {A B : Type} (mx : list A) (f : A -> list B) : list B := *)
  (*   match mx with *)
  (*     | nil => nil *)
  (*     | cons x my => f x ++ bind my f  * *)
  (*   end. *)
  
  Lemma monad_left_identity :
    forall (A B : Type) (x : A) (f : A -> list B), bind (ret x) f = f x.
    repeat intro.
    unfold ret.
    unfold bind.
    unfold flat_map.
    SearchAbout nil.
    rewrite  (app_nil_r (f x)).
    reflexivity.
  Qed.

  Lemma monad_right_identity :
    forall (A B : Type) (mx : list A), bind mx ret = mx.
    repeat intro.
    induction mx.
    compute; trivial.
    simpl.
    rewrite -> IHmx.
    reflexivity.
Qed.

  Lemma flat_map_app :
    forall (A B : Type) (l1 : list A) (l2 : list A) (f : A -> list B),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    repeat intro.
    induction l1; simpl.
    trivial.
    rewrite IHl1.
    SearchAbout ((_ ++ _) ++ _).
    apply app_assoc.
  Qed.
  
  Lemma monad_associativity :
    forall (A B C : Type) (mx : list A) (f : A -> list B) (g : B -> list C),
      bind (bind mx f) g = bind mx (fun x => bind (f x) g).
    repeat intro.
    induction mx; simpl.
    trivial.
    rewrite <- IHmx.
    apply flat_map_app.
  Qed.
  
End ListMonad.