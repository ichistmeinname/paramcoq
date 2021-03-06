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

End MonadClass.


Section MaybeMonad.

  Inductive option (A : Type) :=
  | some : A -> option A
  | none : option A.

  (* Without Implicit Arguments *)

  (* Definition ret {A: Type} (x : A) := some A x. *)
  (* Definition bind {A B : Type} (a : option A) (f: A -> option B) : option B := *)
  (*   match a with *)
  (*     | some _ x => f x *)
  (*     | none _ => none B *)
  (*   end. *)

  Arguments some {A} _.
  Arguments none {A}.

  Definition option_ret {A: Type} (x : A) := some x.
  Definition option_bind {A B : Type} (a : option A) (f: A -> option B) : option B :=
    match a with
      | some x => f x
      | none => none
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

  Print option_monad.

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

  Parametricity list.
  Print list_R.
(*   Inductive *)
(* list_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) *)
(*   : list A₁ -> list A₂ -> Type := *)
(*     nil_R : list_R A_R nil nil *)
(*   | cons_R : forall (H : A₁) (H0 : A₂), *)
(*              A_R H H0 -> *)
(*              forall (H1 : list A₁) (H2 : list A₂), *)
(*              list_R A_R H1 H2 -> list_R A_R (H :: H1) (H0 :: H2) *)

(* For list_R: Arguments A₁, A₂ are implicit *)
(* For nil_R: Arguments A₁, A₂ are implicit *)
(* For cons_R: Arguments A₁, A₂, A_R, H1, H2 are implicit *)
(* For list_R: Argument scopes are [type_scope type_scope _ list_scope *)
(*               list_scope] *)
(* For nil_R: Argument scopes are [type_scope type_scope _] *)
(* For cons_R: Argument scopes are [type_scope type_scope _ _ _ _ list_scope *)
(*               list_scope _] *)

  Parametricity option.
  Print option_R.
(*   Inductive *)
(* option_R (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) *)
(*   : option A₁ -> option A₂ -> Type := *)
(*     some_R : forall (H : A₁) (H0 : A₂), *)
(*              A_R H H0 -> option_R A_R (some H) (some H0) *)
(*   | none_R : option_R A_R (none A₁) (none A₂) *)

(* For option_R: Arguments A₁, A₂ are implicit *)
(* For some_R: Arguments A₁, A₂ are implicit *)
(* For none_R: Arguments A₁, A₂ are implicit *)
(* For option_R: Argument scopes are [type_scope type_scope _ _ _] *)
(* For some_R: Argument scopes are [type_scope type_scope _ _ _ _] *)
(* For none_R: Argument scopes are [type_scope type_scope _] *)


  Inductive maybe_list_R (A1 B1 : Type) (AB_R : A1 -> B1 -> Type)
  : option A1 -> list B1 -> Type :=
    Nothing_Nil_R : maybe_list_R AB_R (none A1) nil
  | Just_Cons_R : forall (H : A1) (H0 : B1), AB_R H H0 -> maybe_list_R AB_R (some H) (cons H0 nil).

  Definition test {m : Type -> Type} {M : Monad m} {A : Type} : A -> m A := fun x => unit x.
  
  Definition Functional (m1 m2 : Type -> Type) (M1 : Monad m1) (M2 : Monad m2)
             (A B : Type) := (A -> B -> Type) -> m1 A -> m2 B -> Type.
  Print Functional.

  Print bind.

  Definition test2 {m : Type -> Type} {M : Monad m} {A B : Type}
  : m A -> (A -> m B) -> m B := fun mx f => bind B mx f.

  Definition func {A B : Type} := A -> B.
  Parametricity func.
  Print func_R.

  (*   func_R =  *)
  (* fun (A₁ A₂ : Type) (A_R : A₁ -> A₂ -> Type) (B₁ B₂ : Type) *)
  (*   (B_R : B₁ -> B₂ -> Type) (H : A₁ -> B₁) (H0 : A₂ -> B₂) => *)
  (* forall (H1 : A₁) (H2 : A₂), A_R H1 H2 -> B_R (H H1) (H0 H2) *)
  (*      : forall A₁ A₂ : Type, *)
  (*        (A₁ -> A₂ -> Type) -> *)
  (*        forall B₁ B₂ : Type, (B₁ -> B₂ -> Type) -> func -> func -> Type *)

  (* Arguments A₁, A₂, B₁, B₂ are implicit *)
  (* Argument scopes are [type_scope type_scope _ type_scope type_scope _ _ _] *)
  
  Definition Monad_Action_Return {m1 m2 : Type -> Type} {A B : Type}
             {M1 : Monad m1} {M2 : Monad m2} (MA_R : Functional M1 M2 A B) :=
    forall (R: A -> B -> Type) (x : A) (y : B), MA_R R (unit x) (unit y).  


  Print bind.
  Check Functional.
  Definition Monad_Action_Bind {m1 m2 : Type -> Type} {M1 : Monad m1} {M2 : Monad m2}
             {A1 B1 A2 B2 : Type}
             (MA_R : Functional M1 M2 A1 A2) (MA_S : Functional M1 M2 B1 B2)
    (f : A1 -> m1 B1) (g : A2 -> m2 B2) :=
    forall (R : A1 -> A2 -> Type) (S : B1 -> B2 -> Type) (mx : m1 A1) (my : m2 A2),
      MA_R R mx my -> MA_S S (bind B1 mx f) (bind B2 my g).

  
  (* Inductive Monad_Action {m1 m2 : Type -> Type} {M1 : Monad m1} {M2 : Monad m2} *)
  (*           {A1 B1 A2 B2 : Type} *)
  (*           (MA_R : Functional M1 M2 A1 A2) : m1 B1 -> m2 B2 -> Type := *)
  (*   MA_Return : forall (R: B1 -> B2 -> Type) (x : B1) (y : B2), *)
  (*                 R x y -> Monad_Action MA_R (unit x) (unit y) *)
  (* | MA_Bind : forall (R : A1 -> A2 -> Type) (mx : m1 A1) (my : m2 A2) *)
  (*               (f : A1 -> m1 B1) (g : A2 -> m2 B2), *)
  (*               MA_R R mx my -> Monad_Action MA_R (bind B1 mx f) (bind B2 my g). *)

  Definition T := forall X Y, list X -> list Y.
  Definition TF := forall X Y, (X -> Y) -> list X -> list Y.

  Parametricity TF.
  Parametricity T.
  Print T_R.
  Print TF_R.

(*   TF_R =  *)
(* fun H H0 : forall X Y : Type, (X -> Y) -> list X -> list Y => *)
(* forall (X₁ X₂ : Type) (X_R : X₁ -> X₂ -> Type) (Y₁ Y₂ : Type) *)
(*   (Y_R : Y₁ -> Y₂ -> Type) (H1 : X₁ -> Y₁) (H2 : X₂ -> Y₂), *)
(* (forall (H3 : X₁) (H4 : X₂), X_R H3 H4 -> Y_R (H1 H3) (H2 H4)) -> *)
(* forall (H3 : list X₁) (H4 : list X₂), *)
(* list_R X_R H3 H4 -> list_R Y_R (H X₁ Y₁ H1 H3) (H0 X₂ Y₂ H2 H4) *)
  (*      : TF -> TF -> Type *)

  Definition FREE_THEOREM (F : TF) := forall
     T1 T2 T3 T4
     (g : T1 -> T2) (h : T3 -> T4)
     (p : T1 -> T3) (q : T2 -> T4),
      (forall x, h (p x) = q (g x)) ->
           forall l, F T2 T4 q (map g l) = map h (F T1 T3 p l).

(* Lemma param_MAP_naturality : *)
(*   forall F (F_R : TF_R F F), FREE_THEOREM F. *)

  Inductive t_i (A : Type) :=
    t_1 : A -> t_i A
  | t_2 : forall B, t_i B -> (B -> t_i A) -> t_i A.
  Parametricity t_i.
  Print t_i_R.
   (* Print list_R. *)
 
  Definition Monad_Action {m1 m2 : Type -> Type} (M1 : Monad m1) (M2 : Monad m2) :=
            forall (H H0 : Type), (H -> H0 -> Type) -> m1 H -> m2 H0 -> Type.

  Inductive monad_R {m1 m2 : Type -> Type} {M1 : Monad m1} {M2 : Monad m2} :
    Monad_Action M1 M2
            (* forall H H0 : Type, (H -> H0 -> Type) -> m1 H -> m2 H0 -> Type *) :=
    unit_R : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type) (x : A1) (y : A2),
               A_R x y -> monad_R A_R (unit x) (unit y)
  | bind_R : forall (A1 A2 : Type) (A_R : A1 -> A2 -> Type)
               (B1 B2 : Type) (B_R : B1 -> B2 -> Type)
               (mx : m1 A1) (my : m2 A2),
               monad_R A_R mx my -> forall (f : A1 -> m1 B1) (g : A2 -> m2 B2),
                                     (forall (x : A1) (y : A2),
                                        A_R x y -> monad_R B_R (f x) (g y)) ->
                                     monad_R B_R (bind B1 mx f) (bind B2 my g).

  Definition F_T {M1 : Monad list} {M2 : Monad option}
             (F : Monad_Action M1 M2) :=
    forall A B (x : A) (y : B)
      (A_R : A -> B -> Type),
      A_R x y -> F A B A_R nil (none B) = F A B A_R (cons x nil) (some y).

  Lemma param_list_maybe_naturality :
    forall A B F (A_R : list A -> option B -> Type) (F_R : monad_R A_R F F), F_T (F list option).
  
End MonadAction.