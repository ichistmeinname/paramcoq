Declare ML Module "paramcoq".

Require Import List.
(* Require Import Basics. *)

(* Print flip. *)

Set Implicit Arguments.

Print flat_map.
Definition flip {A B C} (f : A -> B -> C) x y : C := f y x.

Print flip.

Section MonadClass.

  Class Monad (M : Type -> Type) := {
  bind : forall A B,
    M A -> (A -> M B) -> M B;
  unit : forall A , A -> M A;
  bind_assoc :
    forall A B C
    (m : M A)
    (f : A -> M B) (g : B -> M C),
    bind (bind m f) g = bind m (fun i => bind (f i) g);
  right_unit : forall A (m : M A),
    bind m (@unit A) = m;
  left_unit : forall A B (x : A) (f : A -> M B),
    bind (unit x) f = f x
}.

Section MonadClass.


Section MaybeMonad.

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

  Definition option_ret {A: Type} (x : A) := Some x.
  Definition option_bind {A B : Type} (a : option A) (f: A -> option B) : option B :=
    match a with
      | Some x => f x
      | None => None
    end.

  Lemma option_left_identity :
    forall (A B : Type) (x : A) (f : A -> option B), option_bind (option_ret x) f = f x.
    repeat intro.
    compute.
    trivial.
  Qed.

  Lemma option_right_identity :
    forall (A : Type) (mx : option A), option_bind mx option_ret = mx.
    repeat intro.
    induction mx; compute; reflexivity.
  Qed.

  Lemma option_associativity :
    forall (A B C : Type) (mx : option A) (f : A -> option B) (g : B -> option C),
      option_bind (option_bind mx f) g = option_bind mx (fun x => option_bind (f x) g).
    repeat intro.
    induction mx; compute.
    induction (f a); trivial.
    trivial.
  Qed.

  Instance option_monad : Monad option :=
    {
      bind := fun X => fun Y => option_bind;
      unit := fun X => option_ret;
      bind_assoc := option_associativity;
      left_unit := option_left_identity;
      right_unit := option_right_identity
    }. 

End MaybeMonad.

Section ListMonad.

  (* Inductive list (A : Type) := *)
  (* | cons : A -> list A -> list A*)
  (* | nil : list A. *)

  (* Arguments nil {A}. *)
  (* Arguments cons {A} _ _. *)

  Definition list_ret {A : Type} (x : A) := cons x nil.
  Definition list_bind {A B : Type} (mx : list A) (f : A -> list B) : list B :=
    flat_map f mx.

  (* Fixpoint bind {A B : Type} (mx : list A) (f : A -> list B) : list B := *)
  (*   match mx with *)
  (*     | nil => nil *)
  (*     | cons x my => f x ++ bind my f  * *)
  (*   end. *)
  
  Lemma list_left_identity :
    forall (A B: Type) (x : A) (f : A -> list B), list_bind (list_ret x) f = f x.
    repeat intro.
    unfold list_ret.
    unfold list_bind.
    unfold flat_map.
    SearchAbout nil.
    rewrite  (app_nil_r (f x)).
    reflexivity.
  Qed.

  Lemma list_right_identity :
    forall (A : Type) (mx : list A), list_bind mx list_ret = mx.
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
  
  Lemma list_associativity :
    forall (A B C : Type) (mx : list A) (f : A -> list B) (g : B -> list C),
      list_bind (list_bind mx f) g = list_bind mx (fun x => list_bind (f x) g).
    repeat intro.
    induction mx; simpl.
    trivial.
    rewrite <- IHmx.
    apply flat_map_app.
  Qed.

  Print flip.
  Print flat_map.

  Instance list_monad : Monad list :=
    {
      bind := fun X => fun Y => list_bind;
      unit := fun X => list_ret;
      bind_assoc := list_associativity;
      left_unit := list_left_identity;
      right_unit := list_right_identity
    }. 
  
End ListMonad.

Section MonadAction.


  (* Definition in_relation (A B : Type) := forall (x : A) (y : B), Prop. *)

  (* Inductive Rel : Type := *)
  (*   | EmbedRel : forall S T, in_relation S T -> Rel. *)

  (* Definition full_relation {A B} (t1 : A) (t2 : B) := True. *)
  (* Print Monad. *)
  (* Definition function_relation {A B M1 M2} *)
  (*            (Rel : A -> B -> Prop) (t1 : A -> Monad (M1 A)) (t2 : B -> Monad (M2 B)) *)
  (*            : Prop := forall x y, Rel x y -> full_relation (t1 x) (t2 y). *)
  (* Definition F {A B : Set} (R : Type) (k1 : A) (k2 : B) : Type := *)
  (*  forall Tau1 Tau2, (Parametricity R) /\ R_R Tau1 Tau2.  *)
  (* Definition Monad_Action {A B X Y} (k1 : Monad A) (k2 : Monad B) : Type := *)
  (*   function_relation full_relation (unit : X -> k1) (unit). *)

  (* Print full_relation. *)
  (* Definition Maybe_List_FR {A B} (R : A -> B -> Prop) := *)
  (*   full_relation (None A) (nil : list B) /\ *)
  (*   function_relation R (fun x => Some x) (fun z => cons z nil). *)
  
End MonadAction.