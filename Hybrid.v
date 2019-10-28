
(****************************************************************
   File: Hybrid.v                                                 
   Authors: Amy Felty
   Date: May 2009

   Current Coq Version: V8.7.1 (also updated ext_eq relation and
   morphisms to use current version of generalized rewriting, i.e.,
   setoids, as described in the "Generalized Rewriting" chapter of
   the reference manual)
                                                                
   The main library, described in:

   Amy Felty and Alberto Momigliano, "Hybrid: A Definitional Two Level
   Approach to Reasoning with Higher-Order Abstract Syntax."  Journal
   of Automated Reasoning, 48(1):43-105, 2012.

  ***************************************************************)

Require Export Div2.
Require Export EqNat.
Require Export Le.
Require Export Lt.
Require Export Plus.
Require Export Gt.
Require Export BoolEq.
Require Export Decidable.
Require Export Omega.
Require Export Max.
Require Export List.
Require Export Wf_nat.
Require Export Classical.
Require Export ClassicalDescription.
Require Export Setoid.

Section utils.

Theorem lt_non_zero : forall i j : nat, i < j -> exists j' : nat, j = j'+1.
unfold lt in |- *.
intros i j; simple induction 1.
exists i; omega.
intros m H0 [j' H1].
rewrite H1.
exists (j'+1); omega.
Qed.

Fixpoint blt_nat (n m : nat) {struct n} : bool :=
  match n, m with
  | O, O => false
  | O, S _ => true
  | S _, O => false
  | S n1, S m1 => blt_nat n1 m1
  end.

Definition ble_nat : nat -> nat -> bool :=
  fun n m => ((blt_nat n m) || (beq_nat n m)).

Lemma max_le_l : forall (n m:nat), n <= (max n m).
Proof.
induction n.
intro m; try omega.
induction m; simpl; try omega.
generalize (IHn m); intro h; omega.
Qed.

Lemma max_le_r : forall (n m:nat), m <= (max n m).
Proof.
intros n m; rewrite max_comm.
apply max_le_l; auto.
Qed.

End utils.

(********************************************************************
  Section hybrid
 ********************************************************************)

Section hybrid.

(********************************************************************
  expr
 ********************************************************************)

Set Implicit Arguments.

Definition var : Set := nat.
Definition bnd : Set := nat.
Variable con: Set.

Inductive expr : Set :=
  CON : con -> expr
| VAR : var -> expr
| BND : bnd -> expr
| APP : expr -> expr -> expr
| ABS : expr -> expr.

(* A new free variable. *)
Fixpoint newvar (e:expr): var :=
match e with
  CON c => 0
| VAR v => (S v)
| BND i => 0
| APP e1 e2 => max (newvar e1) (newvar e2)
| ABS e' => newvar e'
end.

(********************************************************************
  level and proper
 ********************************************************************)

Inductive level : bnd -> expr -> Prop :=
  level_CON : forall (i:bnd) (a:con), (level i (CON a))
| level_VAR : forall (i:bnd) (n:var), (level i (VAR n))
| level_BND : forall i j:bnd, (j<i) -> (level i (BND j))
| level_APP : forall (i:bnd) (s t:expr),
              (level i s) -> (level i t) ->
              (level i (APP s t))
| level_ABS : forall (i:bnd) (s:expr),
              (level (i+1) s) -> (level i (ABS s)).

Definition proper : expr -> Prop := fun e => (level 0 e).

Lemma level_succ : forall (i:bnd) (e:expr), (level i e)->(level (i+1) e).
Proof.
intros i e; induction 1.
apply level_CON.
apply level_VAR.
apply level_BND; omega.
apply level_APP; auto.
apply level_ABS; auto.
Qed.

Lemma bnd_not_proper : forall i:bnd, ~(proper (BND i)).
Proof.
unfold proper; intros i H.
inversion H.
omega.
Qed.

Lemma proper_VAR : forall x:var, (proper (VAR x)).
Proof.
unfold proper; apply level_VAR.
Qed.

Lemma proper_APP1 : forall e1 e2:expr, (proper (APP e1 e2)) -> (proper e1).
Proof.
unfold proper; intros e1 e2 h; inversion h; auto.
Qed.

Lemma proper_APP2 : forall e1 e2:expr, (proper (APP e1 e2)) -> (proper e2).
Proof.
unfold proper; intros e1 e2 h; inversion h; auto.
Qed.

Lemma proper_APP : forall e1 e2:expr,
  proper e1 -> proper e2 -> (proper (APP e1 e2)).
Proof.
unfold proper; intros e1 e2 h1 h2.
apply level_APP; auto.
Qed.

(********************************************************************
  insts
 ********************************************************************)

Definition elist : Set := list expr.

Fixpoint insts (i:bnd)(xs:elist)(e:expr) {struct e} : expr
  := match e with
       (CON a) => (CON a)
     | (VAR n) => (VAR n)
     | (BND j) => if ((ble_nat i j) && (blt_nat (j-i) (length xs)))
                  then (nth (j-i) xs (BND j)) else (BND j)
     | (APP s t) => (APP (insts i xs s) (insts i xs t))
     | (ABS s) => (ABS (insts (i+1) xs s))
     end.

(********************************************************************
  Extensional equality of expr->expr
 ********************************************************************)
Definition ext_eq (f g: expr -> expr) := forall x:expr,
    proper x -> f x = g x.

Lemma ext_eq_refl : forall x : expr -> expr, ext_eq x x.
Proof.
unfold ext_eq; auto.
Qed.

Hint Resolve ext_eq_refl : Ext_Eq.

Lemma ext_eq_symm : forall x y : expr -> expr, ext_eq x y -> ext_eq y x.
Proof.
unfold ext_eq; intros x y h1 x0 h2.
specialize h1 with (1:=h2).
auto.
Qed.

Lemma ext_eq_trans : forall x y z : expr -> expr,
  ext_eq x y -> ext_eq y z -> ext_eq x z. 
Proof.
intros x y z H H0 x0 h1.
generalize (H x0); generalize (H0 x0); intros H1 H2.
specialize H1 with (1:=h1); specialize H2 with (1:=h1).
rewrite -> H1 in H2; auto.
Qed.

Add Parametric Relation : (expr -> expr) ext_eq
  reflexivity proved by ext_eq_refl
  symmetry proved by ext_eq_symm
  transitivity proved by ext_eq_trans
  as ext_eq_S.

Lemma ext_eq_eta : forall (e:expr -> expr), ext_eq e (fun x => e x).
Proof.
unfold ext_eq; auto.
Qed.

Lemma ext_eq_APP_elim1 : forall (f g f' g': expr -> expr),
  (ext_eq (fun x => (APP (f x) (g x))) (fun x => (APP (f' x) (g' x)))) ->
  (ext_eq f f').
Proof.
unfold ext_eq; intros f g f' g' H x.
generalize (H x); intro H0.
intro h1; specialize H0 with (1:=h1).
inversion H0; auto.
Qed.

Lemma ext_eq_APP_elim2 : forall (f g f' g': expr -> expr),
  (ext_eq (fun x => (APP (f x) (g x))) (fun x => (APP (f' x) (g' x)))) ->
  (ext_eq g g').
Proof.
unfold ext_eq; intros f g f' g' H x.
generalize (H x); intro H0.
intro h1; specialize H0 with (1:=h1).
inversion H0; auto.
Qed.

Lemma ext_eq_ABS : forall (f f': expr -> expr),
  (ext_eq (fun x => (ABS (f x))) (fun x => (ABS (f' x)))) ->
  (ext_eq f f').
Proof.
unfold ext_eq; intros f f' H x.
intro h1; specialize H with (1:=h1).
inversion H; auto.
Qed.

(********************************************************************
  abst and lbnd
 ********************************************************************)

Inductive abst_aux: bnd -> (expr->expr) -> Prop :=
  abst_CON : forall (i:bnd) (a:con),
             (abst_aux i (fun x => (CON a)))
| abst_id  : forall (i:bnd),
             (abst_aux i (fun x => x))
| abst_VAR : forall (i:bnd) (n:var),
             (abst_aux i (fun x => (VAR n)))
| abst_BND : forall (i j:bnd) (e: expr -> expr), (j<i) ->
             (abst_aux i (fun x => (BND j)))
| abst_APP : forall (i:bnd) (f g: expr -> expr),
             (abst_aux i f) -> (abst_aux i g) ->
             (abst_aux i (fun x => (APP (f x) (g x))))
| abst_ABS : forall (i:bnd) (f:expr -> expr), (abst_aux (i+1) f) ->
             (abst_aux i (fun x => (ABS (f x)))).

Definition abst (i:bnd) (e:expr->expr) : Prop :=
  exists e', ((ext_eq e' e) /\ (abst_aux i e')).

Definition abstr := abst 0.

Definition ordinary : (expr -> expr) -> Prop :=
  fun e => (exists a, ext_eq e (fun x => (CON a))) \/
           (ext_eq e (fun x => x)) \/
           (exists n, ext_eq e (fun x => (VAR n))) \/
           (exists j, ext_eq e (fun x => (BND j))) \/
           (exists f, exists g, ext_eq e (fun x => (APP (f x) (g x)))) \/
           (exists f, ext_eq e (fun x => (ABS (f x)))).

Inductive lbnd_aux : bnd -> (expr -> expr) -> expr -> Prop :=
  lbnd_CON : forall (i:bnd) (a:con),
             (lbnd_aux i (fun x => CON a) (CON a))
| lbnd_id  : forall (i:bnd), (lbnd_aux i (fun x => x) (BND i))
| lbnd_VAR : forall (i:bnd) (n:var),
             (lbnd_aux i (fun x => VAR n) (VAR n))
| lbnd_BND : forall (i j:bnd), (lbnd_aux i (fun x => BND j) (BND j))
| lbnd_APP : forall (i:bnd) (f g: expr -> expr) (s t: expr),
             (lbnd_aux i f s) -> (lbnd_aux i g t) ->
             (lbnd_aux i (fun x => APP (f x) (g x)) (APP s t))
| lbnd_ABS : forall (i:bnd) (f:expr -> expr) (s:expr),
             (lbnd_aux (i+1) f s) -> (lbnd_aux i (fun x => ABS (f x)) (ABS s))
| lbnd_Err : forall (i:bnd) (e:expr -> expr),
             ~(ordinary e) -> (lbnd_aux i e (BND 0)).

Definition lbnd (i:bnd) (e:expr -> expr) (t:expr) : Prop :=
  exists e', ((ext_eq e' e) /\ (lbnd_aux i e' t)).

(********************************************************************
  lbnd is a total relation
 ********************************************************************)

Fixpoint size (e:expr) : nat
  := match e with
     (CON a) => 1
   | (VAR n) => 1
   | (BND j) => 1
   | (APP s t) => (size s)+(size t)
   | (ABS s) => (size s)+1
   end.

Lemma size_positive : forall e:expr, (size e) > 0.
Proof.
induction e; simpl in |- *; auto; auto with arith.
Qed.

Lemma size_APP1 : forall e1 e2:expr, (size e1) < (size (APP e1 e2)).
Proof.
simpl; intros e1 e2.
generalize (size_positive e2); omega.
Qed.

Lemma size_APP2 : forall e1 e2:expr, (size e2) < (size (APP e1 e2)).
Proof.
simpl; intros e1 e2.
generalize (size_positive e1); omega.
Qed.

Lemma size_ABS :forall e:expr, (size e) < (size (ABS e)).
simpl; intro e; omega.
Qed.

Definition rank : (expr -> expr) -> nat := fun f => (size (f (VAR 0))).

Lemma rank_APP1 : forall f g e : expr -> expr,
  (ext_eq e (fun x => (APP (f x) (g x)))) -> (rank f) < (rank e).
Proof.
unfold rank; unfold ext_eq; simpl; intros f g e H.
rewrite (H (VAR 0) (proper_VAR 0)).
generalize (size_positive (g (VAR 0))); intro H0.
assert (0 < size (g (VAR 0))).
auto with arith.
generalize (plus_lt_compat_l 0 (size (g (VAR 0))) (size (f (VAR 0))) H1);
  intro H2.
rewrite plus_0_r in H2; auto.
Qed.

Lemma rank_APP2 : forall f g e : expr -> expr,
  (ext_eq e (fun x => (APP (f x) (g x)))) -> (rank g) < (rank e).
Proof.
unfold rank; unfold ext_eq; simpl; intros f g e H'.
rewrite (H' (VAR 0) (proper_VAR 0)).
generalize (size_positive (f (VAR 0))); intro H.
assert (0 < size (f (VAR 0))).
auto with arith.
generalize (plus_lt_compat_r 0 (size (f (VAR 0))) (size (g (VAR 0))) H0);
  intro H1.
rewrite plus_0_l in H1; auto.
Qed.

Lemma rank_ABS : forall e' e: expr -> expr,
  (ext_eq e (fun x => (ABS (e' x)))) ->
  (rank e') < (rank e).
Proof.
unfold rank; unfold ext_eq; simpl; intros e' e H'.
rewrite (H' (VAR 0) (proper_VAR 0)).
generalize (size_positive (e' (VAR 0))); intro H.
assert (0 < 1).
auto with arith.
generalize (plus_lt_compat_l 0 1 (size (e' (VAR 0))) H0); intro H1.
rewrite plus_0_r in H1; auto.
Qed.

Lemma lbnd_total :
  forall (i:bnd) (e:expr -> expr), exists s : expr, (lbnd i e s).
Proof.
intros i e.
assert (exists n:nat, n=(rank e)).
exists (rank e); auto.
elim H; clear H.
intro x; generalize i e; clear i e.
generalize (lt_wf_ind x (fun x => (forall (i : bnd) (e : expr -> expr),
   x = rank e -> exists s : expr, lbnd i e s))).
intros H.
apply H; auto.
clear H.
intros n H i e H0.
subst.
unfold rank,lbnd in H.
generalize (classic (ordinary e)).
intros [H1 | H1].
generalize H1; clear H1.
unfold ordinary,lbnd.
intros [[a H0] | [H0 | [[n H0] | [[j H0] | [[f [g H0]] | [f H0]]]]]].
exists (CON a); exists (fun x:expr => (CON a)); split.
apply ext_eq_symm; auto.
apply lbnd_CON.
exists (BND i); exists (fun x:expr => x);
  split; try (apply ext_eq_symm); auto.
apply lbnd_id; apply ext_eq_refl.
exists (VAR n); exists (fun x:expr => VAR n);
  split; try (apply ext_eq_symm); auto.
apply lbnd_VAR; apply ext_eq_refl.
exists (BND j); exists (fun x:expr => BND j);
  split; try (apply ext_eq_symm); auto.
apply lbnd_BND; apply ext_eq_refl.
assert (rank f < rank e).
apply rank_APP1 with g; auto.
assert (rank g < rank e).
apply rank_APP2 with f; auto.
generalize (H (rank f) H1 i f (refl_equal (rank f))).
intros [s [e' [H3 H4]]].
generalize (H (rank g) H2 i g (refl_equal (rank g))).
intros [s' [e'' [H5 H6]]].
exists (APP s s'); exists (fun x : expr => APP (e' x) (e'' x));
  split; try (apply ext_eq_symm); auto.
unfold ext_eq in H0; unfold ext_eq in H3; unfold ext_eq in H5;
  unfold ext_eq; intros x0 h1.
specialize H0 with (1:=h1); specialize H3 with (1:=h1);
  specialize H5 with (1:=h1).
rewrite -> H0; rewrite -> H3; rewrite -> H5; auto.
apply lbnd_APP; auto.
assert (rank f < rank e).
apply rank_ABS; auto.
generalize (H (rank f) H1 (i+1) f (refl_equal (rank f))).
intros [s [e' [H2 H3]]].
exists (ABS s); exists (fun x : expr => ABS (e' x));
  split; try (apply ext_eq_symm); auto.
unfold ext_eq in H0; unfold ext_eq in H2; unfold ext_eq; intros x0 h1.
specialize H0 with (1:=h1); specialize H2 with (1:=h1).
rewrite -> H0; rewrite -> H2; auto.
apply lbnd_ABS; auto.
unfold lbnd.
exists (BND 0); exists e; split; [apply ext_eq_refl | apply lbnd_Err]; auto.
Qed.

(********************************************************************
  inversion lemmas for lbnd_aux
 ********************************************************************)

Lemma lbnd_CON_inv : forall (i:bnd) (a:con) (t:expr) (e:expr -> expr),
  (ext_eq e (fun x => CON a)) -> (lbnd_aux i e t) -> t=(CON a).
Proof.
intros i a t e H; unfold ext_eq in H; destruct 1.
apply (H (VAR 0)); apply proper_VAR; auto.
generalize (H (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H (VAR 0) (proper_VAR 0)); discriminate 1.
elim H0; unfold ordinary,ext_eq.
left; exists a; auto.
Qed.
 
Lemma lbnd_id_inv : forall (i:bnd) (t:expr) (e:expr -> expr),
  (ext_eq e (fun x => x)) -> (lbnd_aux i e t) -> t=(BND i).
Proof.
intros i t e H; unfold ext_eq in H; destruct 1; auto;
  try (specialize H with (1:=(proper_VAR 0)); discriminate H).
assert (proper (APP (VAR 0) (VAR 0))).
apply proper_APP; apply proper_VAR; auto.
specialize H with (1:=H0); discriminate H.
elim H0; unfold ordinary, ext_eq.
right; left; auto.
Qed.

Lemma lbnd_VAR_inv : forall (i:bnd) (n:var) (t:expr) (e:expr -> expr),
  (ext_eq e (fun x => VAR n)) -> (lbnd_aux i e t) -> t=(VAR n).
Proof.
intros i n t e H; unfold ext_eq in H; destruct 1; auto;
  try (specialize H with (1:=(proper_VAR 0)); discriminate H).
assert (proper (APP (VAR 0) (VAR 0))).
apply proper_APP; apply proper_VAR; auto.
specialize H with (1:=H0); discriminate H.
specialize H with (1:=(proper_VAR n)); auto.
elim H0; unfold ordinary, ext_eq.
right; right; left; exists n; auto.
Qed.

Lemma lbnd_BND_inv : forall (i j:bnd) (t:expr) (e:expr -> expr),
  (ext_eq e (fun x => BND j)) -> (lbnd_aux i e t) -> t=(BND j).
Proof.
intros i j t e H; unfold ext_eq in H; destruct 1; auto;
  try (specialize H with (1:=(proper_VAR 0)); discriminate H).
specialize H with (1:=(proper_VAR 0)); auto.
elim H0; unfold ordinary,ext_eq.
right; right; right; left; exists j; auto.
Qed.

Lemma lbnd_APP_inv : forall (i:bnd) (t: expr) (e f g: expr -> expr),
  (ext_eq e (fun x => APP (f x) (g x))) ->
  (lbnd i e t) -> 
  (exists s':expr, exists t':expr, (lbnd i f s') /\ (lbnd i g t') /\
  t=(APP s' t')).
Proof.
unfold lbnd.
intros i t e f g H.
setoid_rewrite -> H; clear H e.
intros [H]. destruct H0. destruct H1.
generalize (H0 (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H0 (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H0 (VAR 0) (proper_VAR 0)); discriminate 1.
generalize (H0 (VAR 0) (proper_VAR 0)); discriminate 1.
exists s; exists t; repeat split; auto.
exists f0; split; auto; apply ext_eq_APP_elim1 with g0 g; auto.
exists g0; split; auto; apply ext_eq_APP_elim2 with f0 f; auto.
generalize (H0 (VAR 0) (proper_VAR 0)); discriminate 1.
elim H; unfold ordinary.
right; right; right; right; left; exists f; exists g; auto.
Qed.

Lemma lbnd_ABS_inv : forall (i:bnd) (t: expr) (e f: expr -> expr),
  (ext_eq e (fun x => ABS (f x))) ->
  (lbnd i e t) ->
  (exists s:expr, (lbnd (i+1) f s) /\ t=(ABS s)).
Proof.
unfold lbnd.
intros i t e f H.
setoid_rewrite -> H ; clear H e.
intros [H]. destruct H0. destruct H1;
  try (unfold ext_eq in H0; specialize H0 with (1:=(proper_VAR 0));
       discriminate H0); auto.
exists s; split; auto.
exists f0; split; auto; apply ext_eq_ABS; auto.
elim H; unfold ordinary.
right; right; right; right; right; exists f; auto.
Qed.

Lemma lbnd_Err_inv : forall (i:bnd) (t:expr) (e:expr -> expr),
  ~(ordinary e) -> (lbnd_aux i e t) -> t=(BND 0).
Proof.
intros i t e H; destruct 1; auto; elim H; unfold ordinary.
left; exists a; apply ext_eq_refl.
right; left; apply ext_eq_refl.
right; right; left; exists n; apply ext_eq_refl.
right; right; right; left; exists j; apply ext_eq_refl.
right; right; right; right; left; exists f; exists g; apply ext_eq_refl.
right; right; right; right; right; exists f; apply ext_eq_refl.
Qed.

(********************************************************************
  extensional equality and morphisms
 ********************************************************************)

Lemma abst_compat : forall (i:bnd) (e e':expr -> expr),
  (ext_eq e e') -> (abst i e) <-> (abst i e').
Proof.
  unfold abst. intros i e e' H. split.
  - intros [e'' [H0 H1]].
    exists e''; split; auto.
    rewrite -> H0; auto with Ext_Eq.
  - intros [e'' [H0 H1]].
    exists e''; split; auto.
    rewrite -> H; auto with Ext_Eq.
Qed.

Lemma abst_ext_eq : forall (i:bnd) (e e':expr -> expr),
  (ext_eq e e') -> (abst i e) -> (abst i e').
Proof.
  apply abst_compat; auto.
Qed.

Add Parametric Morphism : abst with
      signature eq ==> ext_eq ==> iff as abst_ext_eq'.
Proof.
  apply abst_compat; auto.
Qed.

Lemma abstr_compat : forall (e e':expr -> expr),
  (ext_eq e e') -> (abstr e) <-> (abstr e').
Proof.
  unfold abstr.
  intros e e' H; split; intro H0.
  - apply abst_ext_eq with e; auto.
  - apply abst_ext_eq with e'; auto.
    rewrite -> H; auto with Ext_Eq.
Qed.

Lemma abstr_ext_eq : forall (e e':expr -> expr),
  (ext_eq e e') -> (abstr e) -> (abstr e').
Proof.
  apply abstr_compat; auto.
Qed.

Add Parametric Morphism : abstr with
      signature ext_eq ==> iff as abstr_ext_eq'.
Proof.
  apply abstr_compat; auto.
Qed.

Lemma ordinary_compat : forall (e e' : expr -> expr),
  (ext_eq e e') -> (ordinary e) <-> (ordinary e').
Proof.
  unfold ordinary.
  intros e e' H; split;
    intros [[a H0] | [H0 | [[n H0] | [[j H0] | [[f [g H0]] | [f H0]]]]]].
  - left.
    exists a; rewrite <- H; auto.
  - right; left.
    rewrite <- H; auto.
  - right; right; left.
    exists n; rewrite <- H; auto.
  - right; right; right; left.
    exists j; rewrite <- H; auto.
  - right; right; right; right; left.
    exists f; exists g; rewrite <- H; auto.
  - right; right; right; right; right.
    exists f; rewrite <- H; auto.
  - left.
    exists a; rewrite -> H; auto.
  - right; left.
    rewrite -> H; auto.
  - right; right; left.
    exists n; rewrite -> H; auto.
  - right; right; right; left.
    exists j; rewrite -> H; auto.
  - right; right; right; right; left.
    exists f; exists g; rewrite -> H; auto.
  - right; right; right; right; right.
    exists f; rewrite -> H; auto.
Qed.

Lemma ordinary_ext_eq : forall (e e' : expr -> expr),
  (ext_eq e e') -> (ordinary e) -> (ordinary e').
Proof.
  apply ordinary_compat; auto.
Qed.

Add Parametric Morphism : ordinary with
      signature ext_eq ==> iff as ordinary_ext_eq'.
Proof.
  apply ordinary_compat; auto.
Qed.

Lemma lbnd_compat : forall (i:bnd) (e e' : expr -> expr) (t:expr),
  (ext_eq e e') -> (lbnd i e t) <-> (lbnd i e' t).
Proof.
  unfold lbnd.
  intros i e e' t H; split; intros [e'' [H0 H1]].
  - exists e''; split; auto with Ext_Eq.
    rewrite -> H0; auto.
  - exists e''; split; auto with Ext_Eq.
    rewrite -> H; auto with Ext_Eq.
Qed.

Lemma lbnd_ext_eq : forall (i:bnd) (e e' : expr -> expr) (t:expr),
  (ext_eq e e') -> (lbnd i e t) -> (lbnd i e' t).
Proof.
  apply lbnd_compat.
Qed.

Add Parametric Morphism : lbnd with
    signature eq ==> ext_eq ==> eq ==> iff as lbnd_ext_eq'.
Proof.
  intros; apply lbnd_compat; auto.
Qed.

(********************************************************************
  properties of ordinary, abst, and lbnd
 ********************************************************************)

Theorem abstraction_induct :
  forall (P:(expr -> expr) -> Prop) (e:expr -> expr),
  (forall (a:con) (e':expr -> expr),
     ext_eq e' (fun x:expr => CON a) -> P e') ->
  (forall (n:var) (e':expr -> expr),
     ext_eq e' (fun x:expr => VAR n) -> P e') ->
  (forall (e':expr -> expr),
     ext_eq e' (fun x:expr => x) -> P e') ->
  (forall (j:bnd) (e':expr -> expr),
     ext_eq e' (fun x:expr => BND j) -> P e') ->
  (forall e' f g:expr -> expr,
     ext_eq e' (fun x:expr => (APP (f x) (g x))) ->
     P f -> P g -> P e') ->
  (forall e' f:expr -> expr,
     ext_eq e' (fun x:expr => (ABS (f x))) -> P f -> P e') ->
  (forall e':expr -> expr, ~(ordinary e') -> P e') ->
  P e.
Proof.
intros P e h1 h2 h3 h4 h5 h6 ho.
assert (ha1 : (exists i:nat, i=(rank e))).
exists (rank e); auto.
elim ha1; clear ha1; intros i h7.
generalize
 (lt_wf_ind i
   (fun j:nat =>
     (forall e: expr -> expr, j = rank e -> P e))).
intro h8; apply h8; clear h8; auto.
clear h7 i e.
intros n hInd e h7.
generalize (classic (ordinary e)).
intros [h8 | h8].
generalize h8; clear h8.
unfold ordinary.
intros [[a h8] | [h8 | [[n' h8] | [[j h8] | [[f [g h8]] | [f h8]]]]]].
apply h1 with a; auto.
apply h3; auto.
apply h2 with n'; auto.
apply h4 with j; auto.
generalize (rank_APP1 f g h8); generalize (rank_APP2 f g h8); intros h9 h10.
assert (ha1 : (rank f = rank f)); assert (ha2 : (rank g = rank g)); auto.
subst.
generalize (hInd (rank f) h10 f ha1); intro h11.
generalize (hInd (rank g) h9 g ha2); intro h12.
apply h5 with f g; auto.
subst.
generalize (rank_ABS f h8); intro h9.
assert (ha1 : (rank f = rank f)); auto.
generalize (hInd (rank f) h9 f ha1); intro h10.
apply h6 with f; auto.
apply ho; auto.
Qed.

Lemma level_abst_aux : forall (i:bnd) (e:expr),
  level i e -> abst_aux i (fun x => e).
intros i e; induction 1.
apply abst_CON; auto.
apply abst_VAR; auto.
apply abst_BND; auto.
generalize (abst_APP IHlevel1 IHlevel2); auto.
generalize (abst_ABS i IHlevel); auto.
Qed.

Lemma proper_abstr : forall e:expr,
  proper e -> abstr (fun x => e).
unfold proper,abstr,abst; intros e H.
exists (fun x:expr => e); split; auto with Ext_Eq.
apply level_abst_aux; auto.
Qed.

Lemma proper_abst_aux : forall e:expr,
  proper e -> abst_aux 0 (fun x => e).
Proof.
unfold proper; intros e H.
apply level_abst_aux; auto.
Qed.

Lemma level_lbnd_aux : forall (i:bnd) (E1:expr),
  level (i+1) E1 -> exists E2:expr->expr, (lbnd_aux i E2 E1).
Proof.
intros i E1 H.
assert (exists j:bnd, j=i+1).
exists (i+1); auto.
elim H0; clear H0; intros j H0.
rewrite <- H0 in H.
generalize H i H0; clear H i H0.
induction 1.
intros; exists (fun x:expr => (CON a)); apply lbnd_CON.
intros; exists (fun x:expr => (VAR n)); apply lbnd_VAR.
intros; exists (fun x:expr => (BND j)); apply lbnd_BND.
intros i0 H1.
elim (IHlevel1 i0 H1); intros E2 H1'.
elim (IHlevel2 i0 H1); intros E2' H2.
exists (fun x:expr => (APP (E2 x) (E2' x))). 
apply lbnd_APP; auto.
intros i0 H0.
assert (i+1=i+1).
auto.
elim (IHlevel i H1); intros E2 H2.
subst.
exists (fun x : expr => ABS (E2 x)).
apply lbnd_ABS; auto.
Qed.

Lemma same_level_lbnd_aux : forall (i:bnd) (E1:expr),
  level i E1 -> exists E2:expr->expr, (lbnd_aux i E2 E1).
Proof.
intros i E1; induction 1.
exists (fun x:expr => (CON a)).
apply lbnd_CON.
exists (fun x:expr => (VAR n)).
apply lbnd_VAR.
exists (fun x:expr => (BND j)).
apply lbnd_BND.
elim IHlevel1; intros E2 H1.
elim IHlevel2; intros E2' H2.
exists (fun x:expr => (APP (E2 x) (E2' x))). 
apply lbnd_APP; auto.
elim IHlevel; intros E2 H0.
exists (fun x : expr => ABS (E2 x)).
apply lbnd_ABS; auto.
Qed.

Lemma abst_aux_ordinary : forall (i:bnd) (e e':expr -> expr),
  abst_aux i e -> ext_eq e' e -> ordinary e'.
Proof.
intros i e e'; induction 1.
intro H; unfold ordinary; left.
exists a; auto.
intro H; unfold ordinary; right; left; auto.
intro H; unfold ordinary; right; right; left.
exists n; auto.
intro H0; unfold ordinary; right; right; right; left.
exists j; auto.
intro H1; unfold ordinary; right; right; right; right; left.
exists f; exists g; auto.
intro H0; unfold ordinary; right; right; right; right; right.
exists f; auto.
Qed.

Lemma abst_ordinary : forall (i:bnd) (e e':expr -> expr),
  abst i e -> ext_eq e' e -> ordinary e'.
Proof.
unfold abst; intros i e e' [e'' [H H0]] H1.
apply abst_aux_ordinary with i e''; auto.
setoid_rewrite H; auto with Ext_Eq.
Qed.

Lemma abst_aux_lbnd_one_to_one :
  forall (i:bnd) (e: expr -> expr), abst_aux i e ->
  forall (f:expr -> expr), abst_aux i f ->
  forall (t:expr), lbnd i e t -> lbnd i f t -> ext_eq e f.
Proof.
intros i e; induction 1.
(* CON case *)
intros f H t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_CON_inv H1 H2); intro H5; subst.
inversion H4; subst; auto.
(* id case *)
intro f; induction 1; auto with Ext_Eq.
intros t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_id_inv H1 H2); intro H5; subst.
generalize (lbnd_CON_inv H3 H4); intro H5; subst.
discriminate H5.
intros t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_id_inv H1 H2); intro H5; subst.
generalize (lbnd_VAR_inv H3 H4); intro H5; subst.
discriminate H5.
intros t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_id_inv H1 H2); intro H5; subst.
generalize (lbnd_BND_inv H3 H4); intro H5; subst.
inversion H5; subst.
absurd (j<j); auto with arith.
intros t [e' [H1 H2]] [f' [H3 H4]].
cut (lbnd i f' t).
intro H5.
generalize (lbnd_id_inv H1 H2); intro H6; subst.
generalize (lbnd_APP_inv f g H3 H5).
intros [s' [t' [H6 [H7 H8]]]].
discriminate H8.
unfold lbnd; exists f'; auto with Ext_Eq.
intros t [e' [H1 H2]] [f' [H3 H4]].
cut (lbnd i f' t).
intro H5.
generalize (lbnd_id_inv H1 H2); intro H6; subst.
generalize (lbnd_ABS_inv f H3 H5).
intros [s' [H6 H7]].
discriminate H7.
unfold lbnd; exists f'; auto with Ext_Eq.
(* VAR case *)
intros f H t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_VAR_inv H1 H2); intro H5; subst.
inversion H4; subst; auto.
(* BND case *)
intros f H' t [e' [H1 H2]] [f' [H3 H4]].
generalize (lbnd_BND_inv H1 H2); intro H5; subst.
inversion H4; subst; auto.
absurd (j<j); auto with arith.
elim H7; apply abst_aux_ordinary with i f; auto.
(* APP case *)
intro f0; induction 1; auto with Ext_Eq.
intros t H1 [e' [H2 H3]].
generalize (lbnd_CON_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H5.
generalize (lbnd_APP_inv f g H5 H1).
intros [s' [t' [H6 [H7 H8]]]].
subst.
discriminate H8.
intros t H1 [e' [H2 H3]].
generalize (lbnd_id_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H5.
generalize (lbnd_APP_inv f g H5 H1).
intros [s' [t' [H6 [H7 H8]]]].
subst.
discriminate H8.
intros t H1 [e' [H2 H3]].
generalize (lbnd_VAR_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H5.
generalize (lbnd_APP_inv f g H5 H1).
intros [s' [t' [H6 [H7 H8]]]].
subst.
discriminate H8.
intros t H1' [e' [H2 H3]].
generalize (lbnd_BND_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H5.
generalize (lbnd_APP_inv f g H5 H1').
intros [s' [t' [H6 [H7 H8]]]].
subst.
discriminate H8.
clear IHabst_aux3 IHabst_aux4.
intros t H1 H2.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H3.
generalize (ext_eq_refl (fun x : expr => APP (f0 x) (g0 x))); intro H4.
generalize (lbnd_APP_inv f g H3 H1).
generalize (lbnd_APP_inv f0 g0 H4 H2).
intros [s' [t' [H5 [H6 H7]]]] [s'' [t'' [H8 [H9 H10]]]].
subst.
inversion H10; subst.
specialize IHabst_aux1 with (1:=H1_) (2:=H8) (3:=H5).
specialize IHabst_aux2 with (1:=H1_0) (2:=H9) (3:=H6).
unfold ext_eq in IHabst_aux1; unfold ext_eq in IHabst_aux2; unfold ext_eq.
intros x h1.
rewrite -> (IHabst_aux1 x h1); rewrite -> (IHabst_aux2 x h1); auto.
intros t H2 H3.
generalize (ext_eq_refl (fun x : expr => APP (f x) (g x))); intro H4.
generalize (ext_eq_refl (fun x : expr => ABS (f0 x))); intro H5.
generalize (lbnd_APP_inv f g H4 H2).
generalize (lbnd_ABS_inv f0 H5 H3).
intros [s [H6 H7]] [s' [t' [H8 [H9 H10]]]].
subst.
discriminate H10.
(* ABS case *)
intro f0; induction 1; auto with Ext_Eq.
intros t H1 [e' [H2 H3]].
generalize (lbnd_CON_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H5.
generalize (lbnd_ABS_inv f H5 H1).
intros [s [H6 H7]].
subst.
discriminate H7.
intros t H1 [e' [H2 H3]].
generalize (lbnd_id_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H5.
generalize (lbnd_ABS_inv f H5 H1).
intros [s [H6 H7]].
subst.
discriminate H7.
intros t H1 [e' [H2 H3]].
generalize (lbnd_VAR_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H5.
generalize (lbnd_ABS_inv f H5 H1).
intros [s [H6 H7]].
subst.
discriminate H7.
intros t H1 [e' [H2 H3]].
generalize (lbnd_BND_inv H2 H3); intro H4.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H5.
generalize (lbnd_ABS_inv f H5 H1).
intros [s [H6 H7]].
subst.
discriminate H7.
intros t H2 H3.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H4.
generalize (ext_eq_refl (fun x : expr => APP (f0 x) (g x))); intro H5.
generalize (lbnd_ABS_inv f H4 H2).
generalize (lbnd_APP_inv f0 g H5 H3).
intros [s' [t' [H8 [H9 H10]]]] [s [H6 H7]].
subst.
discriminate H7.
clear IHabst_aux0.
intros t H1 H2.
generalize (ext_eq_refl (fun x : expr => ABS (f x))); intro H3.
generalize (ext_eq_refl (fun x : expr => ABS (f0 x))); intro H4.
generalize (lbnd_ABS_inv f H3 H1).
generalize (lbnd_ABS_inv f0 H4 H2).
intros [s' [H5 H6]] [s''[H7 H8]].
subst.
inversion H8; subst.
specialize IHabst_aux with (1:=H0) (2:=H7) (3:=H5).
(* use lemmas here *)
unfold ext_eq.
intros x h1.
rewrite -> (IHabst_aux x h1); auto.
Qed.

Lemma abst_lbnd_one_to_one :
  forall (i:bnd) (e: expr -> expr), abst i e ->
  forall (f:expr -> expr), abst i f ->
  forall (t:expr), lbnd i e t -> lbnd i f t -> ext_eq e f.
Proof.
unfold abst; intros i e [e' [H H0]] f [f' [H1 H2]] t H3 H4.
generalize (abst_aux_lbnd_one_to_one H0 H2); intro H5.
setoid_rewrite <- H; setoid_rewrite <- H1.
apply H5 with t; auto.
setoid_rewrite -> H; auto with Ext_Eq.
setoid_rewrite -> H1; auto with Ext_Eq.
Qed.

Lemma abst_eta : forall (i:bnd) (e:expr -> expr),
  (abst i e) -> (abst i (fun x:expr => e x)).
Proof.
unfold abst.
intros i e [e' [H H0]].
exists e'; split; auto.
Qed.

Lemma abstr_eta : forall (e:expr -> expr),
  (abstr e) -> (abstr (fun x:expr => e x)).
Proof.
unfold abstr; apply abst_eta.
Qed.

(********************************************************************
  lbnd is a functional relation
 ********************************************************************)

Lemma lbnd_unique :
  forall (i:bnd) (e:expr -> expr) (s:expr),
  lbnd i e s -> forall (t:expr), lbnd i e t -> s = t.
Proof.
unfold lbnd.
intros i e s [e1 [H H1]] t [e2 [H2 H3]].
generalize H2; clear H2.
generalize H3; clear H3.
generalize t e2; clear t e2.
generalize H; clear H.
generalize e; clear e.
generalize H1; clear H1.
generalize i s e1; clear i s e1.
intros i s e1; induction 1.
intros e H t e2 H3 H2.
assert (ext_eq e2 (fun x:expr => CON a)).
setoid_rewrite -> H2; setoid_rewrite <- H; auto with Ext_Eq.
generalize (lbnd_CON_inv H0 H3); auto.
intros e H t e2 H3 H2.
assert (ext_eq e2 (fun x:expr => x)).
setoid_rewrite -> H2; setoid_rewrite <- H; auto with Ext_Eq.
generalize (lbnd_id_inv H0 H3); auto.
intros e H t e2 H3 H2.
assert (ext_eq e2 (fun x:expr => VAR n)).
setoid_rewrite -> H2; setoid_rewrite <- H; auto with Ext_Eq.
generalize (lbnd_VAR_inv H0 H3); auto.
intros e H t e2 H3 H2.
assert (ext_eq e2 (fun x:expr => BND j)).
setoid_rewrite -> H2; setoid_rewrite <- H; auto with Ext_Eq.
generalize (lbnd_BND_inv H0 H3); auto.
intros e H t0 e2 H3 H2.
assert (ext_eq e (fun x : expr => APP (f x) (g x))).
setoid_rewrite <- H; auto with Ext_Eq.
assert (lbnd i e t0).
unfold lbnd; exists e2; auto.
generalize (lbnd_APP_inv f g H0 H1); auto.
unfold lbnd; intros [s' [t' [[ef [H4 H5]] [[eg [H6 H7]] H8]]]].
generalize (IHlbnd_aux1 ef (ext_eq_symm H4) s' ef H5 (ext_eq_refl ef));
  intro H9.
generalize (IHlbnd_aux2 eg (ext_eq_symm H6) t' eg H7 (ext_eq_refl eg));
  intro H10.
subst; auto.
intros e H t e2 H3 H2.
assert (ext_eq e (fun x : expr => ABS (f x))).
setoid_rewrite <- H; auto with Ext_Eq.
assert (lbnd i e t).
unfold lbnd; exists e2; auto.
generalize (lbnd_ABS_inv f H0 H4); auto.
unfold lbnd; intros [s' [[e' [H5 H6]] H7]].
generalize (IHlbnd_aux e' (ext_eq_symm H5) s' e' H6 (ext_eq_refl e'));
  intro.
subst; auto.
intros e0 H0 t e2 H3 H2.
generalize H; clear H; setoid_rewrite -> H0; setoid_rewrite <- H2; intro H.
generalize (lbnd_Err_inv H H3); auto.
Qed.

(********************************************************************
  applying the description theorem to get lbind, a functional
  version of the lbnd relation
 ********************************************************************)

Definition lbnd_curry : (prodT bnd (expr->expr))->expr->Prop
 := (prodT_curry lbnd).

Lemma lbnd_curry_eq : forall (i:bnd) (e:expr->expr) (s:expr),
  (lbnd i e s)=(lbnd_curry (pairT i e) s).
Proof.
unfold lbnd_curry, prodT_curry; auto.
Qed.

Lemma lbnd_curry_total:
  forall (p:prodT bnd (expr -> expr)), exists s : expr, lbnd_curry p s.
Proof.
intro p.
elim p.
unfold lbnd_curry, prodT_curry.
exact lbnd_total.
Qed.

Lemma lbnd_curry_total_unique :
  forall (p:prodT bnd (expr -> expr)), exists s : expr,
    lbnd_curry p s /\ (forall s':expr, lbnd_curry p s' -> s = s').
Proof.
intro p.
elim p.
unfold lbnd_curry, prodT_curry.
intros a b.
generalize (lbnd_total a b); intro H.
elim H; clear H; intros x H.
exists x; split; auto.
intros s' H0.
generalize (lbnd_unique H H0); auto.
Qed.

Theorem lbind_exists :
  exists lbind_curry : (prodT bnd (expr->expr)) -> expr,
    (forall p:(prodT bnd (expr->expr)), lbnd_curry p (lbind_curry p)).
Proof.
apply unique_choice.
unfold unique; apply lbnd_curry_total_unique.
Qed.

Unset Implicit Arguments.

End hybrid.

(********************************************************************
  Section lbind
 ********************************************************************)

Hint Resolve ext_eq_refl : Ext_Eq.

Section lbind.

Set Implicit Arguments.

Variable con: Set.

Parameter lbind_curry : (prodT bnd (expr con -> expr con)) -> expr con.
Axiom lbind_curry_lbnd_curry : 
  forall p:(prodT bnd (expr con->expr con)), lbnd_curry p (lbind_curry p).

Definition lbind : bnd -> (expr con -> expr con) -> expr con :=
  prodT_uncurry lbind_curry.
Lemma lbind_lbnd :
  forall i:bnd, forall e:expr con->expr con, lbnd i e (lbind i e).
Proof.
intros i e.
unfold lbind, prodT_uncurry.
rewrite -> lbnd_curry_eq.
apply lbind_curry_lbnd_curry.
Qed.

Lemma lbind_value : forall i:bnd, forall e:expr con->expr con,
   forall s:expr con, lbnd i e s -> s = (lbind i e).
Proof.
intros i e s H.
generalize (lbind_curry_lbnd_curry (pairT i e)); intro H0.
unfold lbnd_curry, prodT_curry in H0.
apply lbnd_unique with i e; auto.
Qed.

Lemma abst_lbind_one_to_one :
  forall (i:bnd) (e: expr con -> expr con), abst i e ->
  forall (f:expr con -> expr con), abst i f ->
  lbind i e = lbind i f -> ext_eq e f.
Proof.
intros i e H f H0 H1.
generalize (lbind_lbnd i e); rewrite H1; intro H2.
generalize (lbind_lbnd i f); intro H3.
apply abst_lbnd_one_to_one with i (lbind i f); auto.
Qed.

Lemma lbind_ext_eq : forall (i:bnd) (e e' : expr con -> expr con),
  (ext_eq e e') -> (lbind i e)=(lbind i e').
Proof.
intros i e e' h1.
generalize (lbind_lbnd i e); generalize (lbind_lbnd i e'); intros h2 h3.
specialize lbnd_ext_eq with (1:=h1) (2:=h3); intro h4.
apply lbnd_unique with i e'; auto.
Qed.

(********************************************************************
  rewrite rules for lbind
 ********************************************************************)

Lemma lbind_CON : forall (i:bnd) (a:con),
  (lbind i (fun x => CON a))=(CON a).
Proof.
intros i a; symmetry; apply lbind_value.
unfold lbnd.
exists (fun x:expr con => CON a); split; auto with Ext_Eq.
apply lbnd_CON; auto.
Qed.

Lemma lbind_id : forall (i:bnd), (lbind i (fun x => x))=(BND con i).
Proof.
intro i; symmetry; apply lbind_value.
unfold lbnd.
exists (fun x:expr con => x); split; auto with Ext_Eq.
apply lbnd_id; auto.
Qed.

Lemma lbind_VAR : forall (i:bnd) (n:var),
  (lbind i (fun x => VAR con n))=(VAR con n).
Proof.
intros i n; symmetry; apply lbind_value.
unfold lbnd.
exists (fun x:expr con => VAR con n); split; auto with Ext_Eq.
apply lbnd_VAR; auto.
Qed.

Lemma lbind_BND : forall (i j:bnd),
  (lbind i (fun x => BND con j))=(BND con j).
Proof.
intros i j; symmetry; apply lbind_value.
unfold lbnd.
exists (fun x:expr con => BND con j); split; auto with Ext_Eq.
apply lbnd_BND; auto.
Qed.

Lemma lbind_APP : forall (i:bnd) (f g: expr con -> expr con),
  (lbind i (fun x => APP (f x) (g x)))=(APP (lbind i f) (lbind i g)).
Proof.
intros i f g.
generalize (lbind_lbnd i f); generalize (lbind_lbnd i g); unfold lbnd.
intros [eg [H H0]] [ef [H1 H2]].
symmetry; apply lbind_value.
unfold lbnd.
exists (fun x: expr con => APP (ef x) (eg x)); split.
unfold ext_eq in H; unfold ext_eq in H1; unfold ext_eq; intros x h1.
rewrite (H x h1); rewrite (H1 x h1); auto.
apply lbnd_APP; auto.
Qed.

Lemma lbind_ABS : forall (i:bnd) (f: expr con -> expr con),
  (lbind i (fun x => ABS (f x)))=(ABS (lbind (i+1) f)).
Proof.
intros i f.
generalize (lbind_lbnd (i+1) f); unfold lbnd.
intros [ef [H H0]].
symmetry; apply lbind_value.
unfold lbnd.
exists (fun x: expr con => ABS (ef x)); split.
unfold ext_eq in H; unfold ext_eq; intros x h1.
rewrite (H x h1); auto.
apply lbnd_ABS; auto.
Qed.

Hint Rewrite lbind_CON lbind_id lbind_VAR lbind_BND
             lbind_APP lbind_ABS : lbind_rw.

(********************************************************************
  lambda and injectivity
 ********************************************************************)

Definition lambda : (expr con -> expr con) -> expr con :=
  fun e:expr con -> expr con => (ABS (lbind 0 e)).

Lemma abstr_lbind_simp_aux :
  forall (i:bnd)(e:expr con->expr con), (abst_aux i e) ->
  forall (f:expr con->expr con), (abst_aux i f) ->
  (lbind i e)=(lbind i f) -> e=f.
Proof.
intros i e; induction 1.
intro f; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
autorewrite with lbind_rw; intro H; rewrite H; auto.
intro f; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
auto.
rewrite lbind_id; rewrite lbind_BND; inversion 1.
subst.
generalize (lt_irrefl j); intro H1; elim H1; auto.
intro f; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
autorewrite with lbind_rw; intro H; rewrite H; auto.
intro f; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
rewrite lbind_id; rewrite lbind_BND; inversion 1.
subst.
generalize (lt_irrefl i); intro H1; elim H1; auto.
rewrite lbind_BND; rewrite lbind_BND; inversion 1; auto.
intro f0; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
autorewrite with lbind_rw; inversion 1.
generalize (IHabst_aux1 f0 H1_ H3); generalize (IHabst_aux2 g0 H1_0 H4);
  intros; subst; auto.
intro f0; destruct 1; try (autorewrite with lbind_rw; discriminate 1).
autorewrite with lbind_rw; inversion 1.
generalize (IHabst_aux f0 H0 H3); intro; subst; auto.
Qed.

Lemma abstr_lbind_simp :
  forall (i:bnd)(e:expr con->expr con), (abst i e) ->
  forall (f:expr con->expr con), (abst i f) ->
  (lbind i e)=(lbind i f) -> (ext_eq e f).
Proof.
intros i e [e' [H H0]] f [f' [H1 H2]] H3.
apply abst_lbind_one_to_one with i; auto.
unfold abst; exists e'; split; auto with Ext_Eq.
unfold abst; exists f'; split; auto with Ext_Eq.
Qed.

Lemma abstr_lam_simp : forall e f:expr con->expr con,
  (abstr e) -> (abstr f) -> (lambda e)=(lambda f) -> (ext_eq e f).
Proof.
unfold lambda; intros e f H H0 H1.
inversion H1.
apply abstr_lbind_simp with 0; auto.
Qed.

Lemma abstr_lam_simp_eta : forall e f:expr con->expr con,
  (abstr e) -> (abstr f) ->
  (lbind 0 (fun x => e x))=(lbind 0 (fun x => f x)) -> (ext_eq e f).
Proof.
intros e f h1 h2 h3.
generalize (ext_eq_eta e); generalize (ext_eq_eta f); intros h4 h5.
generalize (lbind_ext_eq 0 h4); intro h6.
generalize (lbind_ext_eq 0 h5); intro h7.
apply abstr_lam_simp; auto.
unfold lambda; auto.
rewrite -> h7; rewrite -> h3; rewrite h6; auto.
Qed.

(********************************************************************
  Other properties
 ********************************************************************)

Lemma lbind_does_not_occur : forall (y:expr con) (i:bnd),
  (lbind i (fun x => y))=y.
Proof.
induction y; intro i; autorewrite with lbind_rw; auto.
rewrite IHy1; rewrite IHy2; auto.
generalize (lbind_ABS i (fun x => y)); intro H.
rewrite IHy; auto.
Qed.

Lemma level_lbnd_abst : forall (i:bnd) (E1:expr con),
  (level i E1) -> forall (j:bnd), j+1=i ->
  exists E2:expr con->expr con, (lbnd_aux j E2 E1 /\ abst_aux j E2).
Proof.
intros i E1; induction 1.
intros j h; exists (fun x:expr con => (CON a)); split.
apply lbnd_CON.
apply abst_CON.
intros j h; exists (fun x:expr con => (VAR con n)); split.
apply lbnd_VAR.
apply abst_VAR.
intros k h.
subst.
assert (S k > j); try omega.
generalize (gt_S k j H0); intros [h | h].
exists (fun x:expr con => (BND con j)); split.
apply lbnd_BND; auto.
apply abst_BND; auto.
subst.
exists (fun x:expr con => x); split.
apply lbnd_id.
apply abst_id.
intros j h.
elim (IHlevel1 j h); elim (IHlevel2 j h).
intros E2 [h1 h2] E3 [h3 h4].
exists (fun x => (APP (E3 x) (E2 x))); split.
apply lbnd_APP; auto.
apply abst_APP; auto.
intros j h.
assert (j+1+1=i+1); try omega.
elim (IHlevel (j+1) H0); intros E2 [h1 h2].
exists (fun x => (ABS (E2 x))); split.
apply lbnd_ABS; auto.
apply abst_ABS; auto.
Qed.

Lemma level_lbind_abst :
  forall (i:bnd) (E1:expr con),
  (level i E1) -> forall (j:bnd), j+1=i->
  exists E2:expr con->expr con, (lbind j E2=E1 /\ abst j E2).
Proof.
intros i E1 h1 j h2.
generalize (level_lbnd_abst h1 j h2); intros [E2 [h3 h4]].
assert (lbnd j E2 E1).
unfold lbnd; exists E2.
split; auto with Ext_Eq.
generalize (lbind_value H); intro; subst.
exists E2; split; auto.
unfold abst; exists E2; auto with Ext_Eq.
Qed.

Lemma level_lbnd_abst_j :
  forall (j:bnd) (E1:expr con),
  (level j E1) ->
  exists E2:expr con->expr con, (lbnd_aux j E2 E1 /\ abst_aux j E2).
Proof.
intros j E1; induction 1.
exists (fun x:expr con => (CON a)); split; [apply lbnd_CON | apply abst_CON].
exists (fun x:expr con => (VAR con n));
  split; [apply lbnd_VAR | apply abst_VAR].
exists (fun x:expr con => (BND con j));
  split; [apply lbnd_BND | apply abst_BND]; auto.
elim IHlevel1; elim IHlevel2.
intros E2 [h1 h2] E3 [h3 h4].
exists (fun x => (APP (E3 x) (E2 x))); split.
apply lbnd_APP; auto.
apply abst_APP; auto.
elim IHlevel; intros E2 [h1 h2].
exists (fun x => (ABS (E2 x))); split.
apply lbnd_ABS; auto.
apply abst_ABS; auto.
Qed.

Lemma level_lbind_abst_j :
  forall (j:bnd) (E1:expr con),
  (level j E1) ->
  exists E2:expr con->expr con, (lbind j E2=E1 /\ abst j E2).
Proof.
intros j E1 h1.
generalize (level_lbnd_abst_j h1); intros [E2 [h3 h4]].
assert (lbnd j E2 E1).
unfold lbnd; exists E2.
split; auto with Ext_Eq.
generalize (lbind_value H); intro; subst.
exists E2; split; auto.
unfold abst; exists E2; auto with Ext_Eq.
Qed.

Lemma proper_lambda_abstr : forall E1:expr con,
  proper (ABS E1) -> exists E2:expr con->expr con,
  ((ABS E1)=(lambda E2) /\ (abstr E2)).
Proof.
unfold lambda, proper, abstr.
intros E1 h.
inversion h; subst.
assert (0+1=0+1); try omega.
generalize (level_lbind_abst H1 0 H); intros [E2 [h1 h2]].
exists E2; split; auto.
rewrite <- h1; auto.
Qed.

Lemma proper_lambda : forall E1:expr con,
  proper (ABS E1) ->
  exists E2:expr con->expr con, (ABS E1)=(lambda (fun x => E2 x)).
Proof.
unfold lambda, proper.
intros E1 H.
inversion H; subst.
generalize level_lbnd_aux; intro H0.
generalize (H0 con 0 E1 H2); clear H0; intro H0.
elim H0; clear H0; intros E2 H0.
exists E2.
assert (lbnd 0 E2 E1).
unfold lbnd.
exists E2; split; auto with Ext_Eq.
assert (lbnd 0 (fun x => E2 x) E1).
apply lbnd_ext_eq with E2.
apply ext_eq_eta.
unfold lbnd.
exists E2; split; auto with Ext_Eq.
generalize (lbind_value H3); intro H4.
subst; auto.
Qed.

Lemma level_lbind_eta_e : forall (i:bnd) (E:expr con->expr con),
  abst i E ->
  level (i+1) (lbind i (fun x => E x)) ->
  forall (x:expr con), proper x -> level i x -> (level i (E x)).
Proof.
intros i E [e' [H H0]].
generalize E H; clear E H.
induction H0.
(* CON case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
apply level_CON; auto.
(* id case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
(* VAR case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
apply level_VAR; auto.
(* BND case *)
intros E H' H1 x h1 H2.
rewrite <- H'; auto.
apply level_BND; auto.
(* APP case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
generalize (lbind_lbnd i (fun x => E x)); intro H2.
assert (ext_eq (fun x => E x) (fun x => APP (f x) (g x))).
apply ext_eq_trans with E; auto with Ext_Eq.
apply ext_eq_symm; auto.
generalize (lbnd_APP_inv (fun x => f x) (fun x => g x) H3 H2).
intros [s [t [H4 [H5 H6]]]].
rewrite H6 in H0.
inversion H0; subst.
apply level_APP; auto.
apply IHabst_aux1; auto with Ext_Eq.
generalize (lbind_value H4); intro; subst; auto.
apply IHabst_aux2; auto with Ext_Eq.
generalize (lbind_value H5); intro; subst; auto.
(* ABS case *)
intros E H H0' x h1 H1.
rewrite <- H; auto.
generalize (lbind_lbnd i (fun x => E x)); intro H2.
assert (ext_eq (fun x => E x) (fun x => ABS (f x))).
apply ext_eq_trans with E; auto with Ext_Eq.
apply ext_eq_symm; auto.
generalize (lbnd_ABS_inv (fun x => f x) H3 H2).
intros [s [H4 H5]].
rewrite H5 in H0'.
inversion H0'; subst.
apply level_ABS; auto.
apply IHabst_aux; auto with Ext_Eq.
generalize (lbind_value H4); intro; subst; auto.
apply level_succ; auto.
Qed.

Lemma level_lbind_e : forall (i:bnd) (E:expr con->expr con),
  abst i E ->
  level (i+1) (lbind i E) ->
  forall (x:expr con), proper x -> level i x -> (level i (E x)).
Proof.
intros i E [e' [H H0]].
generalize E H; clear E H.
induction H0.
(* CON case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
apply level_CON; auto.
(* id case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
(* VAR case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
apply level_VAR; auto.
(* BND case *)
intros E H' H1 x h1 H2.
rewrite <- H'; auto.
apply level_BND; auto.
(* APP case *)
intros E H H0 x h1 H1.
rewrite <- H; auto.
generalize (lbind_lbnd i E); intro H2.
assert (ext_eq E (fun x => APP (f x) (g x))).
apply ext_eq_symm; auto.
generalize (lbnd_APP_inv f g H3 H2).
intros [s [t [H4 [H5 H6]]]].
rewrite H6 in H0.
inversion H0; subst.
apply level_APP; auto.
apply IHabst_aux1; auto with Ext_Eq.
generalize (lbind_value H4); intro; subst; auto.
apply IHabst_aux2; auto with Ext_Eq.
generalize (lbind_value H5); intro; subst; auto.
(* ABS case *)
intros E H H0' x h1 H1.
rewrite <- H; auto.
generalize (lbind_lbnd i E); intro H2.
assert (ext_eq E (fun x => ABS (f x))).
apply ext_eq_symm; auto.
generalize (lbnd_ABS_inv f H3 H2).
intros [s [H4 H5]].
rewrite H5 in H0'.
inversion H0'; subst.
apply level_ABS; auto.
apply IHabst_aux; auto with Ext_Eq.
generalize (lbind_value H4); intro; subst; auto.
apply level_succ; auto.
Qed.

Lemma abstr_proper: forall E:expr con -> expr con,
  (abstr E) -> (proper (lambda E)).
Proof.
unfold abstr,proper,lambda.
intros E [E' [h1 h2]].
apply level_ABS.
change (level 1 (lbind 0 E)).
generalize (lbind_ext_eq 0 h1); intro h3.
rewrite <- h3.
clear h1 h3.
generalize h2; clear h2; induction 1.
rewrite lbind_CON; apply level_CON.
rewrite lbind_id; apply level_BND; auto with arith.
rewrite lbind_VAR; apply level_VAR.
rewrite lbind_BND; apply level_BND; auto with arith.
rewrite lbind_APP; apply level_APP; auto.
rewrite lbind_ABS; apply level_ABS; auto.
Qed.

Lemma abstr_proper_e : forall (E:expr con -> expr con) (e':expr con),
  abstr E -> proper e' -> (proper (E e')).
Proof.
intros E e' h1 h2.
generalize (abstr_proper h1); intro h3.
unfold proper,lambda in h3.
inversion h3; subst; clear h3.
unfold proper.
apply level_lbind_e; auto.
Qed.

Lemma abstr_size_lbind : forall E:expr con -> expr con,
  abstr E -> forall (i:bnd) (j:var),
  (size (lbind i E))=(size (E (VAR con j))).
Proof.
intros E [E' [h1 h2]].
generalize h2 E h1; clear h1 h2 E.
induction 1.
intros E h1 j n.
generalize (lbind_ext_eq j h1); intro h2.
rewrite <- h2.
rewrite <- h1; auto.
autorewrite with lbind_rw; auto.
apply proper_VAR; auto.
intros E h1 j n.
generalize (lbind_ext_eq j h1); intro h2.
rewrite <- h2.
rewrite <- h1.
autorewrite with lbind_rw; auto.
apply proper_VAR; auto.
intros E h1 j n'.
generalize (lbind_ext_eq j h1); intro h2.
rewrite <- h2.
rewrite <- h1.
autorewrite with lbind_rw; auto.
apply proper_VAR; auto.
intros E h1 k n.
generalize (lbind_ext_eq k h1); intro h2.
rewrite <- h2.
rewrite <- h1.
autorewrite with lbind_rw; auto.
apply proper_VAR; auto.
intros E h1 j n.
generalize (lbind_ext_eq j h1); intro h2.
rewrite <- h2.
rewrite <- h1.
autorewrite with lbind_rw.
simpl.
assert (h3: (size (lbind j f) = size (f (VAR con n)))).
apply IHh2_1; auto with Ext_Eq.
assert (h4: (size (lbind j g) = size (g (VAR con n)))).
apply IHh2_2; auto with Ext_Eq.
rewrite h3; rewrite h4; auto.
apply proper_VAR; auto.
intros E h1 j n.
generalize (lbind_ext_eq j h1); intro h3.
rewrite <- h3.
rewrite <- h1.
autorewrite with lbind_rw.
simpl.
assert (h4: (size (lbind (j+1) f) = size (f (VAR con n)))).
apply IHh2; auto with Ext_Eq.
rewrite h4; auto.
apply proper_VAR; auto.
Qed.

Theorem eq_ext_double:
  forall (f g: expr con -> expr con -> expr con),
    (forall x, proper x ->  abstr (f x)) -> 
    (forall x, proper x ->  abstr (g x)) -> 
    abstr (fun x => lambda (f x)) -> 
    abstr (fun x => lambda (g x)) -> 
    lbind 0 (fun x  => lambda (f x)) =
    lbind 0 (fun x => lambda (g x)) ->
    forall x1, proper x1  -> ext_eq (f x1)  (g x1).
Proof.
  intros f g H H0 H1 H2 H3 x1 H4.
  apply abst_lbind_one_to_one with 0; unfold abstr in H,H0; auto.
  apply abstr_lbind_simp in H3; unfold abstr in H,H0; auto.
  unfold ext_eq in H3.
  apply H3 in H4. unfold lambda in H4. inversion H4.
  auto.
Qed.

(********************************************************************
  proper_VAR_induct
 ********************************************************************)

Theorem proper_VAR_induct : forall (P:expr con -> Prop) (e:expr con),
  proper e ->
  (forall a:con, P (CON a)) ->
  (forall n:var, P (VAR con n)) ->
  (forall E1 E2:expr con, proper E1 -> proper E2 ->
    P E1 -> P E2 -> P (APP E1 E2)) ->
  (forall E:expr con -> expr con,
    abstr E -> forall n:var, P (E (VAR con n)) -> P (lambda E)) ->
  P e.
Proof.
intros P e H H0 H1 H2 H3.
assert (exists i:nat, i=(size e)).
exists (size e); auto.
elim H4; clear H4; intros i H4.
generalize
 (lt_wf_ind i
   (fun j:nat =>
     (forall e: expr con, (j=(size e) -> (proper e) -> P e)))).
intro H5; apply H5; clear H5; auto.
clear H4 i H e.
intros n H e H4 H5.
induction e.
apply H0.
apply H1.
absurd (proper (BND con b)); auto.
apply bnd_not_proper; auto.
generalize (proper_APP1 H5); generalize (proper_APP2 H5); intros h1 h2.
assert ((size e1) < n).
generalize (size_APP1 e1 e2); intro; omega.
assert ((size e2) < n).
generalize (size_APP2 e1 e2); intro; omega.
assert (size e1=size e1); auto.
assert (size e2=size e2); auto.
generalize (H (size e1) H6 e1 H8 h2); intro h3.
generalize (H (size e2) H7 e2 H9 h1); intro h4.
apply H2; auto.
generalize (proper_lambda_abstr H5); intros [E2 [h1 h2]].
rewrite h1; rewrite h1 in H5; rewrite h1 in H4.
apply H3 with 0; auto.
apply H with (n-1); try omega; auto.
generalize (size_positive (lambda E2)); subst; omega.
simpl in H4.
rewrite <- (abstr_size_lbind h2 0 0).
omega.
apply abstr_proper_e; auto.
apply proper_VAR.
Qed.

End lbind.
