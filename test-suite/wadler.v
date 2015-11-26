Declare ML Module "paramcoq".
(* Require Import Omega. *)
Require Import List.

Parametricity nat.

  
Lemma nat_R_equal : 
  forall x y, nat_R x y -> x = y.
  intros x y H;
  induction H;
  subst;
  trivial.
Defined.

Lemma equal_nat_R : 
  forall x y, x = y -> nat_R x y.
  intros x y H.
  subst.
  induction y; constructor; trivial.
Defined.

Parametricity list.

Definition full_relation {A B} (x : A) (y : B) := True.

Definition same_length {A B} := list_R A B full_relation.

Print full_relation.
Print list_R.

Lemma same_length_length : 
  forall A B (l1 : list A) (l2 : list B), 
    same_length l1 l2 -> length l1 = length l2.
  intros A B l1 l2 H.
  Print list_R.
  induction H.
  simpl.
  reflexivity.
  Print f_equal.
  Print list_R.
  exact (f_equal S IHlist_R).
Qed.

(* Theorem length_cons : forall A B : Type, forall n : A, forall l1 : list A, forall l2 : list B, *)
(*   length l1 = length l2 -> length (n :: l1) = S (length l2). *)
(* Proof. *)
(*   repeat intro. *)
(*   induction l1, l2. *)
(*   simpl; reflexivity. *)
(*   simpl in H. *)
(*   Print Peano. *)
(*   congruence. *)
(*   simpl in H; symmetry in H. *)
(*   congruence. *)
(*   symmetry in H. *)
(*   rewrite H. *)
(*   simpl; trivial. *)
(* Qed. *)


Theorem length_cons : forall A B : Type, forall n : A, forall m : B, forall l1 : list A, forall l2 : list B,
  length l1 = length l2 <-> length (n :: l1) = length (m :: l2).
Proof.
  repeat intro.
  split.
  simpl.
  auto.
  auto.
Qed.

Theorem length_cons_not_nil : forall A B : Type, forall a : A, forall l1 : list A, forall l2 : list B, length (a :: l1) = length l2 -> nil <> l2.
Proof.
  intros.
  induction l1.
  simpl in H.
  contradict H.
  symmetry in H.
  rewrite H.
  auto.
  intro.
  symmetry in H0.
  rewrite H0 in H.
  simpl in H.
  symmetry in H.
  apply O_S in H.
  auto.
Qed.
  (* simpl in H. *)
  (* apply eq_add_S in H. *)
  (* symmetry in H. *)
  (* apply length_zero_iff_nil in H. *)
  (* apply nil_cons. *)
  (* simpl in H. *)
  (* symmetry in H. *)
  
  (* induction IHl1. *)
  (* rewrite H. *)
  (* simpl. *)
  (* apply eq_S. *)
  (* pose n_Sn. *)
  (* pose (m := length l1). *)
  (* replace (length l1) with m. *)
  (* induction m. *)
  (* discriminate. *)
  (* inversion. *)
  (* simpl in H. *)
  (* inversion H. *)
  (* induction l2. *)
  (* Print nil_cons. *)
  (* simpl in H. *)
  (* symmetry in H. *)
  (* apply O_S in H. *)
  (* contradiction. *)

Hypotheses eqA_dec : forall A : Type, forall (x y : A), {x = y}+{x <> y}.

Lemma list_eq_dec :
  forall A : Type, forall l l' : list A, {l = l'} + {l <> l'}.
Proof.
  induction l  as [| x l IHl]; destruct l' as [| y l'].
  left; trivial.
  right. apply nil_cons.
  right. unfold not. intro HF.
  apply (nil_cons (sym_eq HF)).
  destruct (eqA_dec A x y) as [xeqy|xneqy]; destruct (IHl l') as [leql'|lneql'];
  try (right; unfold not; intro HF; injection HF; intros; contradiction).
  rewrite xeqy; rewrite leql'; left; trivial.
Qed.

  
Lemma length_same_length :
  forall A B (l1 : list A) (l2 : list B),
    length l1 = length l2 -> same_length l1 l2.
  (* repeat intro. *)
  (* induction l1; induction l2. *)
  (* apply nil_R. *)
  (* simpl in H. *)
  (* apply O_S in H. *)
  (* inversion H. *)
  (* simpl in H. symmetry in H. apply O_S in H. inversion H. *)
  (* simpl in IHl1. *)
  (* simpl in IHl2. *)
  (* apply IHl2. *)
  (* unfold lis *)
  (* SearchAbout 0. *)
  (* Print list_R *)
        
  repeat intro.
  Print list_R.
  induction l1; induction l2.
  constructor.
  simpl in H.
  apply O_S in H.
  inversion H.
  simpl in H; symmetry in H; apply O_S in H.
  inversion H.
  constructor.
  compute; auto.
  simpl in *; apply eq_add_S in H.
  admit.
Admitted.
                                        
Module LengthType.

Definition T := forall X, list X -> nat.
Parametricity T.
Print T_R.
Definition FREE_THEOREM (f : T) := 
  forall A l1 l2,  same_length l1 l2 -> f A l1 = f A l2.

Lemma param_length_type : 
  forall f (f_R  : T_R f f), FREE_THEOREM f.
  repeat intro.
  Print nat_R_equal.
  apply nat_R_equal.
  Print T_R.
  apply (f_R A A (fun _ _ => True)).
  assumption.
Qed.

Parametricity length.
Definition length_rev : T := fun A l => length (rev l).

Parametricity Recursive length_rev.
Definition double_length : T := fun A l => length (l ++ l).

Parametricity Recursive double_length.
Definition constant : T := fun A l => 42.
Parametricity constant.

Definition length_free_theorem : FREE_THEOREM length
  := param_length_type length length_R.
Definition double_length_free_theorem : FREE_THEOREM double_length
  := param_length_type double_length double_length_R.
Definition constant_free_theorem : FREE_THEOREM constant
  := param_length_type constant constant_R.

End LengthType.

Fixpoint fold {X Y} (f : X -> Y -> Y) (e : Y) (l : list X) : Y := 
  match l with 
   | nil => e
   | x::tl => f x (fold f e tl)
  end.

Parametricity fold.
   

Definition graph {A B} (f : A -> B) := fun x y => f x = y.

Definition map_rel {A B} (f : A -> B) := 
  list_R A B (graph f).

Lemma map_rel_map A B (f : A -> B) : 
   forall (l : list A), map_rel f l (map f l).
  induction l. constructor. compute. auto. constructor. auto.
  compute. auto.
Defined.

Lemma rel_map_map A B (f : A -> B) : 
  forall (l: list A) fl, map_rel f l fl -> fl = map f l.
  intros.
  induction X.
  reflexivity.
  unfold graph in *.
  subst.
  reflexivity.
Defined.

Module RevType.

Definition T := forall X, list X -> list X.
Parametricity T.

Definition FREE_THEOREM (F : T) := 
 forall A B (f : A -> B) l, 
      F B (map f l) = map f (F A l).

Lemma param_naturality : 
   forall F (F_R : T_R F F), FREE_THEOREM F.
repeat intro.
apply rel_map_map.
apply F_R.
apply map_rel_map.
Defined.


Parametricity rev.

Definition tail : T := fun A l => 
  match l with 
    | nil => nil 
    | hd :: tl => tl
  end.
Parametricity tail.

Definition rev_rev : T := fun A l => rev (rev l).
Parametricity rev_rev.


Definition rev_naturality : FREE_THEOREM rev 
 := param_naturality rev rev_R.
Definition rev_rev_naturality : FREE_THEOREM rev_rev
 := param_naturality rev_rev rev_rev_R.
Definition tail_naturality : FREE_THEOREM tail
 := param_naturality tail tail_R.

End RevType.


Parametricity prod.

Definition prod_map {A B} (f : A -> B) 
                  {A' B'} (f' : A' -> B') :=
           prod_R A B (graph f) A' B' (graph f').

Definition pair {A B} (f : A -> B) {A' B'} (f' : A' -> B') : A * A' -> B * B' := 
  fun c => let (x, x') := c in (f x, f' x').

Lemma pair_prod_map : 
  forall A B (f : A -> B) 
         A' B' (f' : A' -> B') xy xy', 
       graph (pair f f') xy xy' -> prod_map f f' xy xy'.
intros ? ? f ? ? f' [x y] [x' y'].
intro H.
compute in H.
injection H.
intros; subst.
constructor; reflexivity.
Defined.

Lemma prod_map_pair : 
  forall A B (f : A -> B) 
         A' B' (f' : A' -> B') xy xy', 
       prod_map f f' xy xy' -> graph (pair f f') xy xy'.
intros ? ? f ? ? f' [x y] [x' y'].
intro H.
compute in H.
induction H; subst.
reflexivity.
Defined.


Lemma list_R_prod_map A B (f : A -> B) A' B' (f' : A' -> B') l1 l2 :
  list_R _ _ (prod_map f f') l1 l2 -> list_R _ _ (graph (pair f f')) l1 l2.
intro H; induction H; constructor; [ apply prod_map_pair|]; auto.
Defined.

Module ZipType.

Definition T := 
  forall X Y, list X -> list Y -> list (X * Y).
Parametricity T.

Definition FREE_THEOREM (F : T) := forall
     A B (f : A -> B)
     A' B' (f' : A' -> B') l l', 
      F B B' (map f l) (map f' l') = map (pair f f') (F A A' l l').

Lemma param_ZIP_naturality : 
   forall F (F_R : T_R F F), FREE_THEOREM F.
repeat intro.
apply rel_map_map.
unfold map_rel.
Print list_R_prod_map.
apply list_R_prod_map.
unfold prod_map.
Print graph.
Print T_R.
(* F : T *)
(*   F_R : T_R F F *)
(*   A : Type *)
(*   B : Type *)
(*   f : A -> B *)
(*   A' : Type *)
(*   B' : Type *)
(*   f' : A' -> B' *)
(*   l : list A *)
(*   l' : list A' *)
(*   ============================ *)
(*    list_R (A * A') (B * B') (prod_R A B (graph f) A' B' (graph f')) *)
(*      (F A A' l l') (F B B' (map f l) (map f' l')) *)

specialize (F_R A B (graph f) A' B' (graph f') l (map f l) (map_rel_map _ _ _ _) l' (map f' l') (map_rel_map _ _ _ _)).
assumption.
Defined.

Fixpoint zip {X Y} (l1 : list X) (l2 : list Y) : list (X * Y) := 
  match l1, l2 with 
   | nil, _ => nil
   | _, nil => nil
   | x::tl1, y::tl2 => (x,y)::(zip tl1 tl2)
  end.
Parametricity zip.
Definition zip_free_theorem : FREE_THEOREM (@zip) := param_ZIP_naturality _ zip_R.

End ZipType.

Print S.

Module MapType.

Definition T := forall X Y, (X -> Y) -> list X -> list Y.

Parametricity T.

Definition FREE_THEOREM (F : T) := forall
     T1 T2 T3 T4
     (g : T1 -> T2) (h : T3 -> T4)
     (p : T1 -> T3) (q : T2 -> T4),
      (forall x, h (p x) = q (g x)) ->
           forall l, F T2 T4 q (map g l) = map h (F T1 T3 p l).
Lemma test :
  forall T1 T2 T3 T4 (g : T1 -> T2) (h : T3 -> T4) (p : T1 -> T3) (q : T2 -> T4), (forall (x : T1), h (p x) = q (g x)) -> forall H H0, (graph g H H0 -> graph h (p H) (q H0)).
Proof.
  repeat intro.
  unfold graph in H2; symmetry in H2.
  rewrite H2.
  unfold graph.
  specialize (H H0).
  assumption.
Qed.

Lemma param_MAP_naturality :
  forall F (F_R : T_R F F), FREE_THEOREM F.
Proof.
  repeat intro.
  apply rel_map_map.
  unfold map_rel.
  Print T_R.
  Print graph.
  (* apply (forall x, graph h (p x) (q (g x))) in H. *)
  specialize (F_R T1 T2 (graph g) T3 T4 (graph h) p q (test T1 T2 T3 T4 g h p q H) l (map g l) (map_rel_map _ _ _ _)).
  assumption.
Qed.
End MapType.