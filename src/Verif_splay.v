Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VSTProgs.splay.

Set Implicit Arguments.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_node := Tstruct _node noattr.

Definition key := Z.

Inductive node (V : Type) :=
| E : node V
| T : key -> V -> node V -> node V -> node V.

Arguments E {V}.
Arguments T {V}.

(* bottom-up path *)
Fixpoint path_splay V (path : list (key * V * bool * node V)) l r :=
  match path with
  | nil => (l, r)
  | (k, v, true, s) :: nil => (l, T k v r s)
  | (k, v, false, s) :: nil => (T k v s l, r)
  | (k0, v0, true, s0) :: (k1, v1, true, s1) :: path' =>
    path_splay path' l (T k0 v0 r (T k1 v1 s0 s1))
  | (k0, v0, true, s0) :: (k1, v1, false, s1) :: path' =>
    path_splay path' (T k1 v1 s1 l) (T k0 v0 r s0)
  | (k0, v0, false, s0) :: (k1, v1, true, s1) :: path' =>
    path_splay path' (T k0 v0 s0 l) (T k1 v1 r s1)
  | (k0, v0, false, s0) :: (k1, v1, false, s1) :: path' =>
    path_splay path' (T k0 v0 (T k1 v1 s1 s0) l) r
  end.

(* top-down path*)
Definition splay V path k (v : V) l r :=
  let (l', r') := path_splay (rev path) l r in
  T k v l' r'.

Fixpoint path_app V (path : list (key * V * bool * node V)) n :=
  match path with
  | nil => n
  | (k, v, true, s) :: path' => T k v (path_app path' n) s
  | (k, v, false, s) :: path' => T k v s (path_app path' n)
  end.

Lemma list_ind2 : forall A (P : list A -> Prop), P [] -> (forall (a : A), P [a]) -> (forall a b l, P l -> P (a :: b :: l)) -> forall (l : list A), P l.
Proof.
  intros ?????.
  refine (fix F (l : list A) :=
            match l with
            | nil => H
            | [a] => H0 a
            | a :: b :: l => H1 a b l (F l)
            end).
Qed.

Lemma Zlength_even_cons_cons : forall A a b (l : list A),
    Zeven (Zlength l) <-> Zeven (Zlength (a::b::l)).
Proof.
  intros.
  rewrite ?Zeven_ex_iff.
  split; intros [? ?].
  - exists (x + 1).
    rewrite ?Zlength_cons; lia.
  - exists (x - 1).
    rewrite ?Zlength_cons in H; lia.
Qed.

Lemma path_splay_snoc_true : forall V path k v s (l r : node V), Zeven (Zlength path) ->
  path_splay (path ++ [(k, v, true, s)]) l r =
  let (l', r') := path_splay path l r in (l', T k v r' s).
Proof.
  induction path using list_ind2; intros.
  - reflexivity.
  - contradiction.
  - destruct a, p, p, b, p, p.
    cbn[app path_splay].
    rewrite <-Zlength_even_cons_cons in H.
    destruct b0, b; rewrite IHpath by auto; reflexivity.
Qed.

Lemma path_splay_snoc_false : forall V path k v s (l r : node V), Zeven (Zlength path) ->
  path_splay (path ++ [(k, v, false, s)]) l r =
  let (l', r') := path_splay path l r in (T k v s l', r').
Proof.
  induction path using list_ind2; intros.
  - reflexivity.
  - contradiction.
  - destruct a, p, p, b, p, p.
    cbn[app path_splay].
    rewrite <-Zlength_even_cons_cons in H.
    destruct b0, b; rewrite IHpath by auto; reflexivity.
Qed. 

Lemma path_splay_split_even : forall V path1 path2 (l r l1 r1 : node V),
    Zeven (Zlength path1) -> Zeven (Zlength path2) ->
    path_splay path1 l r = (l1, r1) ->
    path_splay (path1 ++ path2) l r = path_splay path2 l1 r1.
Proof.
  induction path1 using list_ind2; intros.
  - inv H1.
    reflexivity.
  - contradiction.
  - rewrite <-Zlength_even_cons_cons in H.
    destruct a, p, p, b, p, p.
    cbn[app path_splay].
    destruct b, b0; eapply IHpath1; eauto; reflexivity.
Qed.

Notation bst_at sh k vp lp rp p x :=
  (data_at sh t_node (Vlong (Int64.repr k), (vp, (lp, (rp, p)))) x).

Fixpoint noderep V (A : node V) x p :=
  match A with
  | E => !! (x = nullval) && emp
  | T k v l r => EX vp lp rp : val,
    bst_at Ews k vp lp rp p x * noderep l lp x * noderep r rp x
  end.

Lemma noderep_local_facts:
  forall V (A : node V) x p,
    noderep A x p |--
   !! (is_pointer_or_null x /\ (x=nullval <-> A=E)).
Proof.
  intros.
  destruct A; cbn[noderep].
  - entailer!.
    split; auto.
  - Intros vp lp rp.
    entailer!.
    split; intro.
    * subst x.
      eapply field_compatible_nullval; eauto.
    * inv H1.
Qed.

#[export] Hint Resolve noderep_local_facts : saturate_local.

Lemma noderep_valid_pointer:
  forall V (A : node V) x p,
   noderep A x p |-- valid_pointer x.
Proof.
  intros.
  destruct A; cbn[noderep].
  + entailer!.
  + Intros vp lp rp.
    entailer!.
Qed.

#[export] Hint Resolve noderep_valid_pointer : valid_pointer.

Fixpoint nodepath V (path : list (key * V * bool * node V)) x xp y yp :=
  match path with
  | nil => !! (x = y /\ xp = yp) && emp
  | (k, v, dir, s) :: path' => EX vp lp rp : val,
    bst_at Ews k vp lp rp xp x *
    nodepath path' (if dir then lp else rp) x y yp *
    noderep s (if dir then rp else lp) x
  end.

Fixpoint nodepath' V (path : list (key * V * bool * node V)) (x xp y yp : val) :=
  match path with
  | nil => !! (x = y /\ xp = yp) && emp
  | (ypk, ypv, dir, s) :: path' => EX (ypvp sp yg : val),
    bst_at Ews ypk ypvp (if dir then y else sp) (if dir then sp else y) yg yp *
    nodepath' path' x xp yp yg *
    noderep s sp yp
  end.

Lemma nodepath_cons_parent : forall V ypk (ypv : V) dir s path x xp y yp,
  nodepath (path ++ [(ypk, ypv, dir, s)]) x xp y yp =
  EX (ypvp sp yg : val),
  bst_at Ews ypk ypvp (if dir then y else sp) (if dir then sp else y) yg yp *
  nodepath path x xp yp yg *
  noderep s sp yp.
Proof.
  induction path as [|[[[k v] dir0] s0]]; intros; cbn[app nodepath].
  - apply pred_ext.
    + Intros vp lp rp.
      subst.
      Exists vp (if dir then rp else lp) xp.
      destruct dir; entailer!.
    + Intros ypvp sp yg.
      subst.
      Exists ypvp (if dir then y else sp) (if dir then sp else y).
      unfold bst_at; destruct dir; entailer!.
  - apply pred_ext.
    + Intros vp lp rp.
      rewrite IHpath.
      Intros ypvp sp yg.
      Exists ypvp sp yg vp lp rp.
      entailer!.
    + Intros ypvp sp yg vp lp rp.
      Exists vp lp rp.
      rewrite IHpath.
      Exists ypvp sp yg.
      entailer!.
Qed.

Lemma nodepath'_nodepath : forall V path x xp y yp,
    @nodepath' V path x xp y yp = nodepath (rev path) x xp y yp.
Proof.
  induction path; intros; cbn[rev nodepath'].
  - reflexivity.
  - destruct a, p, p.
    rewrite nodepath_cons_parent.
    repeat (apply exp_congr; intro).
    rewrite IHpath.
    reflexivity.
Qed.

Lemma nodepath_nodepath' : forall V path x xp y yp,
    @nodepath V path x xp y yp = nodepath' (rev path) x xp y yp.
Proof.
  intros.
  rewrite nodepath'_nodepath, rev_involutive.
  reflexivity.
Qed.

Lemma nodepath_local_facts : forall V path root x p,
    @nodepath V path root nullval x p |--
    !! (is_pointer_or_null p).
Proof.
  intros.
  rewrite nodepath_nodepath'.
  remember (rev path) as path'.
  clear Heqpath' path.
  rename path' into path.
  destruct path; intros; cbn[nodepath'].
  - entailer!.
  - destruct p0, p0, p0.
    Intros xpvp sp xg.
    entailer!.
Qed.

#[export] Hint Resolve nodepath_local_facts : saturate_local.

Lemma nodepath_valid_pointer : forall V path root x p,
    @nodepath V path root nullval x p |--
    valid_pointer p.
Proof.
  intros.
  rewrite nodepath_nodepath'.
  remember (rev path) as path'.
  clear Heqpath' path.
  rename path' into path.
  destruct path; intros; cbn[nodepath'].
  - entailer!.
  - destruct p0, p0, p0.
    Intros xpvp sp xg.
    entailer!.
Qed.

#[export] Hint Resolve nodepath_valid_pointer : valid_pointer.

Lemma force_val_false : forall x y, isptr x -> isptr y ->
                   x <> y -> force_val (sem_cmp_pp Ceq x y) = Val.of_bool false.
Proof.
  intros.
  destruct x, y; try contradiction.
  unfold sem_cmp_pp.
  simpl.
  if_tac; simpl; auto.
  subst b0.
  assert (i <> i0) by (intro; subst; contradiction).
  rewrite Ptrofs.eq_false; auto.
Qed.

Lemma force_val_true : forall x, isptr x ->
                            force_val (sem_cmp_pp Ceq x x) = Val.of_bool true.
Proof.
  intros.
  destruct x; try contradiction.
  unfold sem_cmp_pp.
  simpl.
  rewrite eq_block_lem, Ptrofs.eq_true.
  reflexivity.
Qed.

Definition rootboxpath V path rootptr x p :=
  EX (root : val), data_at Ews (tptr t_node) root rootptr *  
  @nodepath V path root nullval x p.

Definition rotate_spec V : ident * funspec :=
 DECLARE _rotate
  WITH dir : bool, path : _, rootptr : val, pk : key, xk : key, A : node V, xx : val, B : node V, xs : val, xvp : val, x : val, C : node V, s : val, pvp : val, p : val, g : val
  PRE  [ tptr (tptr t_node), tptr t_node ]
    PROP ()
    PARAMS (rootptr; x)
    SEP (bst_at Ews pk pvp (if dir then x else s) (if dir then s else x) g p;
        bst_at Ews xk xvp (if dir then xx else xs) (if dir then xs else xx) p x;
         noderep A xx x; noderep B xs x; noderep C s p;
         @rootboxpath V path rootptr p g)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (bst_at Ews pk pvp (if dir then xs else s) (if dir then s else xs) x p;
        bst_at Ews xk xvp (if dir then xx else p) (if dir then p else xx) g x;
         noderep A xx x; noderep B xs p; noderep C s p;
         rootboxpath path rootptr x g).

Definition splay_spec V : ident * funspec :=
  DECLARE _splay
  WITH path : _, U : node V, rootptr : val, k : Z, v : V, l : node V, r : node V, x : val, p : val
  PRE  [ tptr (tptr t_node), tptr t_node ]
    PROP ()
    PARAMS (rootptr; x)
    SEP (noderep (T k v l r) x p; rootboxpath path rootptr x p)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at Ews (tptr t_node) x rootptr;
        noderep (splay path k v l r) x nullval).

Definition Gprog V : funspecs := Eval cbn in [rotate_spec V; splay_spec V].

Lemma body_splay_spec V :
  semax_body Vprog (Gprog V) f_splay (splay_spec V).
Proof.
  Set Ltac Profiling.
  start_function.
  forward_loop 
    (EX p' (path1 path2 : list _),
     PROP (path = path1 ++ path2 /\ (path1 = [] \/ Zeven (Zlength path2)))
     LOCAL (temp _root rootptr; temp _x x)
     SEP (rootboxpath path1 rootptr x p';
          noderep (splay path2 k v l r) x p')).
  { Exists p path (@nil (key * V * bool * node V)).
    rewrite app_nil_r.
    cbn[splay rev path_splay].
    entailer!. }
  unfold rootboxpath.
  clear p.
  Intros p path1 path2 root.
  unfold splay.
  destruct (path_splay (rev path2) l r) eqn:?.
  cbn[noderep].
  Intros vp lp rp.
  forward.
  rewrite nodepath_nodepath'.
  destruct (rev path1) eqn:?; cbn[nodepath'].
  { Intros.
    apply rev_nil_elim in Heql0.
    subst.
    forward_if.
    2: contradiction.
    forward.
    unfold splay.
    cbn[app].
    rewrite Heqp0.
    cbn[noderep].
    Exists vp lp rp.
    entailer!. }
  destruct p0, p0, p0.
  Intros pvp sp g.
  forward_if.
  1: subst; assert_PROP (False) by entailer!; contradiction.
  (* add nodepath' is_null_or_pointer and valid_pointer *)
  rewrite nodepath'_nodepath.
  forward.
  rewrite nodepath_nodepath', rev_involutive.
  destruct l0; cbn[nodepath'].
  { Intros.
    apply (f_equal (@rev _)) in Heql0.
    rewrite rev_involutive in Heql0.
    subst.
    forward_if.
    2: contradiction.
    forward_call (b, @nil (key * V * bool * node V), rootptr, k0, k, if b then n else n0, if b then lp else rp, if b then n0 else n, if b then rp else lp, vp, x, n1, sp, pvp, p, nullval).
    { unfold rootboxpath.
      cbn[nodepath].
      Exists p.
      destruct b; entailer!. }
    forward.
    unfold splay.
    destruct H0; [discriminate|].
    unfold rootboxpath.
    cbn[rev app nodepath noderep].
    Intros root.
    subst.
    destruct b.
    - rewrite path_splay_snoc_true, Heqp0 by (rewrite Zlength_rev; auto).
      cbn[noderep].
      Exists vp lp p pvp rp sp.
      entailer!.
    - rewrite path_splay_snoc_false, Heqp0 by (rewrite Zlength_rev; auto).
      cbn[noderep].
      Exists vp p rp pvp sp lp.
      entailer!. }
  destruct p0, p0, p0.
  Intros gvp up gg.
  forward_if.
  1: subst; assert_PROP (False) by entailer!; contradiction.
  assert_PROP (isptr x) by entailer!.
  assert_PROP (isptr p) by entailer!.
  assert_PROP (is_pointer_or_null sp) by entailer!.
  assert_PROP (is_pointer_or_null up) by entailer!.
  forward.
  { destruct b; entailer!. }
  forward.
  { destruct b0; entailer!. }
  assert_PROP (up <> p).
  { apply not_prop_right.
    intro; subst.
    destruct n2; cbn[noderep].
    1: Intros; entailer!.
    Intros vp0 lp0 rp0.
    entailer!.
    data_at_conflict p. }
  assert_PROP (sp <> x).
  { apply not_prop_right.
    intro; subst.
    destruct n1; cbn[noderep].
    1: Intros; entailer!.
    Intros vp0 lp0 rp0.
    entailer!.
    data_at_conflict x. }
  destruct b, b0.
  - forward_if.
    2:{ rewrite ?force_val_true in H9 by assumption.
        simpl in H9.
        discriminate. }
    forward_call (true, rev l0, rootptr, k1, k0, T k v n n0, x, n1, sp, pvp, p, n2, up, gvp, g, gg).
    { unfold rootboxpath.
      cbn[noderep].
      Exists vp lp rp root.
      rewrite nodepath'_nodepath.
      entailer!. }
    cbn[noderep].
    clear vp lp rp.
    Intros vp lp rp.
    forward_call (true, rev l0, rootptr, k0, k, n, lp, n0, rp, vp, x, (T k1 v1 n1 n2), g, pvp, p, gg).
    { cbn[noderep].
      Exists gvp sp up.
      entailer!. }
    Exists gg (rev l0) ( (k1, v1, true, n2) :: (k0, v0, true, n1) :: path2).
    destruct H0; [subst; discriminate|].
    unfold splay.
    cbn[rev].
    rewrite <-app_assoc.
    erewrite path_splay_split_even.
    2: (rewrite Zlength_rev; assumption).
    2: constructor.
    2: cbn[rev path_splay app]; eauto.
    cbn[app path_splay].
    entailer!.
    + split.
      * apply (f_equal (@rev _)) in Heql0.
        rewrite rev_involutive in Heql0.
        rewrite Heql0.
        cbn[rev app].
        rewrite <-?app_assoc.
        reflexivity.
      * right.
        apply Zlength_even_cons_cons.
        assumption.
    + remember (T k1 v1 n1 n2).
      cbn[noderep].
      Exists vp lp p pvp rp g.
      entailer!.
  - forward_if.
    1:{ rewrite force_val_true in H9 by auto.
        simpl in H9.
        destruct p; try contradiction.
        destruct up; try contradiction.
        - unfold sem_cmp_pp in H9.
          simpl in H9.
          inv H6.
          rewrite Int64.eq_true in H9.
          simpl in H9.
          discriminate.
        - rewrite force_val_false in H9 by eauto.
          simpl in H9.
          discriminate. }
    forward_call (true, rev l0 ++ [(k1, v1, false, n2)], rootptr, k0, k, n, lp, n0, rp, vp, x, n1, sp, pvp, p, g).
    { unfold rootboxpath.
      Exists root.
      rewrite nodepath_nodepath', rev_app_distr.
      cbn[app rev nodepath'].
      rewrite rev_involutive.
      Exists gvp up gg.
      entailer!. }
    unfold rootboxpath.
    clear root.
    Intros root.
    rewrite nodepath_nodepath', rev_app_distr, rev_involutive.
    cbn[rev app nodepath'].
    clear gvp gg.
    Intros gvp up0 gg.
    forward_call (false, rev l0, rootptr, k1, k, (T k0 v0 n0 n1), p, n, lp, vp, x, n2, up0, gvp, g, gg).
    { unfold rootboxpath.
      Exists root.
      rewrite nodepath'_nodepath.
      cbn[noderep].
      Exists pvp rp sp.
      entailer!. }
    Exists gg (rev l0) ((k1, v1, false, n2) :: (k0, v0, true, n1) :: path2).
    destruct H0; [subst; discriminate|].
    unfold splay.
    cbn[rev].
    rewrite <-app_assoc.
    erewrite path_splay_split_even.
    2: (rewrite Zlength_rev; assumption).
    2: constructor.
    2: cbn[rev path_splay app]; eauto.
    cbn[app path_splay].
    entailer!.
    + split.
      * apply (f_equal (@rev _)) in Heql0.
        rewrite rev_involutive in Heql0.
        rewrite Heql0.
        cbn[rev app].
        rewrite <-?app_assoc.
        reflexivity.
      * right.
        apply Zlength_even_cons_cons.
        assumption.
    + remember (T k0 v0 n0 n1).
      cbn[noderep].
      Exists vp g p gvp up0 lp.
      entailer!.
  - forward_if.
    1:{ rewrite force_val_true in H9 by auto.
        simpl in H9.
        destruct x; try contradiction.
        destruct sp; try contradiction.
        - unfold sem_cmp_pp in H9.
          simpl in H9.
          inv H5.
          rewrite Int64.eq_true in H9.
          simpl in H9.
          discriminate.
        - rewrite force_val_false in H9 by eauto.
          simpl in H9.
          discriminate. }
    forward_call (false, rev l0 ++ [(k1, v1, true, n2)], rootptr, k0, k, n0, rp, n, lp, vp, x, n1, sp, pvp, p, g).
    { unfold rootboxpath.
      Exists root.
      rewrite nodepath_nodepath', rev_app_distr, rev_involutive.
      cbn[rev app nodepath'].
      Exists gvp up gg.
      entailer!. }
    unfold rootboxpath.
    clear root.
    Intros root.
    rewrite nodepath_nodepath', rev_app_distr, rev_involutive.
    cbn[rev app nodepath'].
    clear gvp gg.
    Intros gvp sp0 gg.
    forward_call (true, rev l0, rootptr, k1, k, (T k0 v0 n1 n), p, n0, rp, vp, x, n2, sp0, gvp, g, gg).
    { cbn[noderep].
      Exists pvp sp lp.
      unfold rootboxpath.
      Exists root.
      rewrite nodepath'_nodepath.
      entailer!. }
    Exists gg (rev l0) ((k1, v1, true, n2) :: (k0, v0, false, n1) :: path2).
    destruct H0; [subst; discriminate|].
    unfold splay.
    cbn[rev].
    rewrite <-app_assoc.
    erewrite path_splay_split_even.
    2: (rewrite Zlength_rev; assumption).
    2: constructor.
    2: cbn[rev path_splay app]; eauto.
    cbn[app path_splay].
    entailer!.
    + split.
      * apply (f_equal (@rev _)) in Heql0.
        rewrite rev_involutive in Heql0.
        rewrite Heql0.
        cbn[rev app].
        rewrite <-?app_assoc.
        reflexivity.
      * right.
        apply Zlength_even_cons_cons.
        assumption.
    + remember (T k0 v0 n1 n).
      cbn[noderep].
      Exists vp p g gvp rp sp0.
      entailer!.
  - forward_if.
    2:{
      destruct p; try contradiction. 
      destruct x; try contradiction.
      destruct up; try contradiction; inv H6;
        destruct sp; try contradiction; inv H5.
      all: unfold sem_cmp_pp in H9; simpl in H9; rewrite ?Int64.eq_true in H9.
      1: inversion H9.
      1, 2: simpl in H9;
        if_tac in H9; simpl in H9; subst;
          rewrite ?Ptrofs.eq_false in H9 by (intro; subst; contradiction);
          inversion H9.
      if_tac in H9; if_tac in H9; subst;
        rewrite ?Ptrofs.eq_false in H9 by (intro; subst; contradiction); inversion H9.
    }
    forward_call (false, rev l0, rootptr, k1, k0, T k v n n0, x, n1, sp, pvp, p, n2, up, gvp, g, gg).
    { unfold rootboxpath.
      cbn[noderep].
      Exists vp lp rp root.
      rewrite nodepath'_nodepath.
      entailer!. }
    cbn[noderep].
    clear vp lp rp.
    Intros vp lp rp.
    forward_call (false, rev l0, rootptr, k0, k, n0, rp, n, lp, vp, x, (T k1 v1 n2 n1), g, pvp, p, gg).
    { cbn[noderep].
      Exists gvp up sp.
      entailer!. }
    Exists gg (rev l0) ((k1, v1, false, n2) :: (k0, v0, false, n1) :: path2).
    destruct H0; [subst; discriminate|].
    unfold splay.
    cbn[rev].
    rewrite <-app_assoc.
    erewrite path_splay_split_even.
    2: (rewrite Zlength_rev; assumption).
    2: constructor.
    2: cbn[rev path_splay app]; eauto.
    cbn[app path_splay].
    entailer!.
    + split.
      * apply (f_equal (@rev _)) in Heql0.
        rewrite rev_involutive in Heql0.
        rewrite Heql0.
        cbn[rev app].
        rewrite <-?app_assoc.
        reflexivity.
      * right.
        apply Zlength_even_cons_cons.
        assumption.
    + remember (T k1 v1 n2 n1).
      cbn[noderep].
      Exists vp p rp pvp g lp.
      entailer!. 
Time Qed.
