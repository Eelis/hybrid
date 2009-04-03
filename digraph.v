Require Import List.
Require Import util.
Require Import list_util.
Require reachability.
Require Import Program.

Set Implicit Arguments.

Record DiGraph: Type := Build
  { Vertex: Set
  ; Vertex_eq_dec: forall (v v': Vertex), decision (v = v')
  ; vertices: list Vertex
  ; vertices_exhaustive: forall v, In v vertices
  ; edges: Vertex -> list Vertex
  ; edges_NoDup: forall v, NoDup (edges v)
  }.

Hint Resolve edges_NoDup.
Hint Immediate edges_NoDup.
Hint Immediate vertices_exhaustive.

Implicit Arguments edges [d].

Definition flat_edge_list (g: DiGraph): list (Vertex g * Vertex g) :=
  flat_map (fun v => map (pair v) (edges v)) (vertices g).

Section reachability.

  Variable g: DiGraph.

  Let tr (v w: Vertex g): Prop := In w (edges v).
  Let ved := Vertex_eq_dec g.

  Definition Edge: Set := (Vertex g * Vertex g)%type.
  Definition Edge_eq_dec: forall (e e': Edge), decision (e=e')
    := pair_eq_dec ved ved.

  Definition reachable := reachability.reachable tr.

  Variable start: list (Vertex g).
  Hypothesis NoDup_start: NoDup start.

  Let reachable v: Prop := exists s, In s start /\ reachable s v.

  Program Fixpoint unreachables_worker (unvisited: list (Vertex g))
    (tovisit: { l | NoDup l /\ incl l unvisited 
      /\ (forall v, ~ In v unvisited -> forall w, In w unvisited -> tr v w -> In w l)
      /\ (forall v, ~ In v unvisited -> reachable v)
      /\ (forall v, In v l -> reachable v)}) {measure length unvisited}:
    { l | incl l (subtr ved unvisited tovisit)
      /\ (forall v, ~ In v l -> forall w, tr v w -> ~ In w l)
      /\ (forall v, ~ In v l -> reachable v) } :=
    match tovisit with
    | nil => unvisited
    | h :: t => unreachables_worker (remove ved h unvisited)
      (t ++ intersection ved unvisited (subtr ved (edges h) (h :: t)))
    end.

  Next Obligation. Proof with auto.
    (* the result in the nil case meets the result spec *)
    split. apply incl_refl.
    destruct H. destruct H0. destruct H1. destruct H2.
    split...
    repeat intro.
    destruct (H1 _ H4 _ H6 H5).
  Qed.

  Next Obligation. Proof with simpl; auto.
    (* the length decreases in the recursive call *)
    apply remove_length_lt. destruct H. destruct H0.
    apply H0...
  Qed.

  Next Obligation. Proof with simpl; auto.
    (* the invariant is maintained in the recursive call *)
    clear unreachables_worker.
    destruct H. destruct H0. destruct H1. destruct H2.
    inversion_clear H.
    repeat split; intros.
            (* we don't introduce duplicates *)
            apply NoDup_app...
            repeat intro.
            destruct (intersection_In ved x _ _ H6).
            destruct (snd (In_remove ved (subtr ved (edges h) t) x h) H8).
            destruct (In_subtr _ _ _ _ H9)...
          (* the new tovisit is still included in the new unvisited *)
          apply incl_app.
            repeat intro.
            apply (fst (In_remove ved unvisited a h)).
            split... intro. subst...
          repeat intro.
          destruct (intersection_In ved a _ _ H).
          apply (fst (In_remove ved unvisited a h)).
          split...
          destruct (In_remove ved (subtr ved (edges h) t) a h).
          firstorder.
        (* the new tovisit is still the border between visiteds and unvisiteds *)
        destruct (snd (In_remove ved _ _ _) H6).
        rewrite remove_eq_filter in H.
        destruct (not_In_filter' ved _ _ unvisited H).
          destruct (H1 _ H10 _ H8 H7)...
          firstorder.
        destruct (ved h v); [idtac | discriminate].
        clear H10. subst v.
        destruct (In_dec ved w t)...
        apply in_or_app...
      (* things not in the new unvisited are still reachable *)
      rewrite remove_eq_filter in H.
      destruct (not_In_filter' ved v _ unvisited H)...
      destruct (ved h v); [idtac | discriminate].
      firstorder.
    (* things in the new tovisit are still reachable *)
    destruct (in_app_or _ _ _ H). apply H3...
    destruct (intersection_In _ _ _ _ H6). clear H H6.
    destruct (snd (In_remove ved (subtr ved (edges h) t) v h) H8).
    destruct (H3 h (in_eq _ _)). destruct H9.
    exists x. split...
    apply reachability.reachable_next with h...
    unfold tr.
    destruct (In_subtr _ _ _ _ H)...
  Qed.

  Next Obligation. Proof with auto.
    (* the result in the recursive case meets the result spec *)
    set (exist (fun unvisited' : list (Vertex g) => length unvisited' < length unvisited)
      (remove ved h unvisited) (unreachables_worker_obligation_2
      unreachables_worker (exist _ tovisit H) Heq_tovisit)).
    set (exist (fun l =>
      NoDup l /\ incl l (remove ved h unvisited) /\
      (forall v0, ~ In v0 (remove ved h unvisited) -> forall w, In w (remove ved h unvisited) -> tr v0 w -> In w l) /\
      (forall v0, ~ In v0 (remove ved h unvisited) -> reachable v0) /\ (forall v0, In v0 l -> reachable v0))
       (t ++ intersection ved unvisited (remove ved h (subtr ved (edges h) t)))
       (unreachables_worker_obligation_3 unreachables_worker (exist _ tovisit H) Heq_tovisit)).
          (* todo: the above is _awful_ *)
    destruct (unreachables_worker s s0).
    simpl proj1_sig in *.
    clear s s0 unreachables_worker.
    destruct a. destruct H1.
    split...
    subst tovisit.
    simpl.
    repeat intro.
    destruct (In_subtr _ _ _ _ (H0 a H3)). clear H0.
    destruct (snd (In_remove ved unvisited a h) H4). clear H4. 
    apply (In_remove ved (subtr ved unvisited t) a h)...
    split... apply subtr_In...
  Qed.

  Program Definition unreachables:
    { l: list (Vertex g) | forall w, ~ In w l <-> reachable w }
     := @unreachables_worker (vertices g) start.

  Next Obligation. Proof with auto.
    (* the invariant holds at the start *)
    split...
    split. repeat intro...
    split. intros. elimtype False...
    split. intros. elimtype False...
    intros. exists v. split...
    apply reachability.reachable_refl.
  Qed.

  Obligation Tactic := idtac.

  Next Obligation. Proof with auto.
    (* worker's result implies our desired result *)
    destruct (unreachables_worker (exist (fun l => NoDup l /\ incl l (vertices g) /\
       (forall v, ~ In v (vertices g) -> forall w0, In w0 (vertices g) -> tr v w0 -> In w0 l) /\
       (forall v, ~ In v (vertices g) -> reachable v) /\
       (forall v, In v l -> reachable v)) start unreachables_obligation_1)).
    simpl in *.
    destruct a. destruct H0.
    intro. split... repeat intro.
    destruct H2. destruct H2.
    destruct (reachability.reachable_flip_inv (fun j => In j x) (fun j => In_dec ved j x) H4)...
      intro.
      apply (snd (In_subtr ved (vertices g) start _ (H _ H5)) H2).
    destruct H5. destruct H5. destruct H6.
    apply (H0 _ H5 _ H7)...
  Qed.

  Obligation Tactic := program_simpl.


  (* let's do it again, this time using James' method *)

  Inductive result_rel:
    forall (unvisited tovisit result: list (Vertex g)), Prop :=
      | result_nil unvisited: result_rel unvisited nil unvisited
      | result_cons unvisited h t r:
         result_rel (remove ved h unvisited)
         (t ++ intersection ved unvisited (subtr ved (edges h) (h :: t))) r ->
         result_rel unvisited (h :: t) r.

  Hint Constructors result_rel.

  Lemma half_correct (unvisited tovisit r: list (Vertex g)):
    result_rel unvisited tovisit r ->
     (forall v, ~ In v unvisited -> reachable v)
     -> (forall v, In v tovisit -> reachable v)
     -> (forall v, ~ In v r -> reachable v).
      (* todo: is this soundness or completeness? i can't tell because
       of this complement stuff.. *)
  Proof with simpl; auto.
    intros unvisited tovisit r P.
    induction P...
    repeat intro.
    apply IHP; intros...
      (* things not in the new unvisited are still reachable *)
      rewrite remove_eq_filter in H2.
      destruct (not_In_filter' ved _ _ unvisited H2)...
      destruct (ved h v0); [idtac | discriminate].
      clear H3. subst...
    (* things in the new tovisit are still reachable *)
    destruct (in_app_or _ _ _ H2). apply H0...
    destruct (intersection_In _ _ _ _ H3). clear H3.
    destruct (snd (In_remove ved (subtr ved (edges h) t) v0 h) H5).
    destruct (H0 h (in_eq _ _)). destruct H7.
    exists x. split...
    apply reachability.reachable_next with h...
    destruct (In_subtr _ _ _ _ H5)...
  Qed.

  Lemma other_half (unvisited tovisit r: list (Vertex g)):
    result_rel unvisited tovisit r ->
    (forall v, ~ In v unvisited -> forall w,
      In w unvisited -> tr v w -> In w tovisit) -> 
      (forall v, ~ In v r -> forall w, tr v w -> ~ In w r)
      /\ incl r (subtr ved unvisited tovisit).
  Proof with simpl; auto.
    intros unvisited tovisit r P.
    induction P; intros.
      split.
        repeat intro.
        destruct (H _ H0 _ H2 H1).
      unfold incl...
    destruct IHP.
      intros.
      (* the new tovisit is still the border between visiteds and unvisiteds *)
      destruct (snd (In_remove ved _ _ _) H1).
      rewrite remove_eq_filter in H0.
      destruct (not_In_filter' ved _ _ unvisited H0).
        destruct (H _ H5 _ H3 H2)...
        firstorder.
      destruct (ved h v); [idtac | discriminate].
      clear H5. subst v.
      destruct (In_dec ved w t)...
      apply in_or_app...
    split...
    repeat intro.
    destruct (In_subtr _ _ _ _ (H1 _ H2)).
    simpl.
    apply (fst (In_remove ved (subtr ved unvisited t) a h)).
    destruct (snd (In_remove ved unvisited a h) H3).
    split...
    apply subtr_In...
  Qed.

  Program Fixpoint result_rel_exists (unvisited: list (Vertex g))
    (tovisit: { l | NoDup l /\ incl l unvisited })
     {measure length unvisited}:
       { r | result_rel unvisited tovisit r } :=
    match tovisit with
    | nil => unvisited
    | h :: t => result_rel_exists (remove ved h unvisited)
      (t ++ intersection ved unvisited (subtr ved (edges h) (h :: t)))
    end.

  Next Obligation. (* length decrease *)
    intros.
    apply remove_length_lt. destruct H.
    apply H0. auto.
  Qed.

  Next Obligation. Proof with auto. (* NoDup/incl for recursive call. *)
    destruct H. inversion_clear H.
    split.
      (* we don't introduce duplicates *)
      apply NoDup_app...
      repeat intro.
      destruct (intersection_In ved x _ _ H3).
      destruct (snd (In_remove ved (subtr ved (edges h) t) x h) H5).
      destruct (In_subtr _ _ _ _ H6)...
    (* the new tovisit is still included in the new unvisited *)
    apply incl_app.
      repeat intro.
      apply (fst (In_remove ved unvisited a h)).
      split... intro. subst...
    repeat intro.
    destruct (intersection_In ved a _ _ H).
    apply (fst (In_remove ved unvisited a h)).
    split...
    destruct (In_remove ved (subtr ved (edges h) t) a h).
    firstorder.
  Qed.

  Next Obligation. Proof with auto. (* recursive result meets the spec *)
    (* ugly trivial thing, really just a silly Program artifact. *)
    destruct (result_rel_exists
       (exist
          (fun unvisited' : list (Vertex g) =>
           length unvisited' < length unvisited) (remove ved h unvisited)
          (result_rel_exists_obligation_2 result_rel_exists
             (exist (fun l : list (Vertex g) => NoDup l /\ incl l unvisited)
                tovisit H) Heq_tovisit))
       (exist
          (fun l : list (Vertex g) =>
           NoDup l /\ incl l (remove ved h unvisited))
          (t ++
           intersection ved unvisited (remove ved h (subtr ved (edges h) t)))
          (result_rel_exists_obligation_3 result_rel_exists
             (exist (fun l : list (Vertex g) => NoDup l /\ incl l unvisited)
                tovisit H) Heq_tovisit))).
     simpl in *. subst...
  Qed.

  Program Definition unreachables':
    { l: list (Vertex g) | forall w, ~ In w l <-> reachable w }
    := @result_rel_exists (vertices g) start.

  Next Obligation. Proof with auto.
    split... repeat intro. apply vertices_exhaustive.
  Qed.

  Next Obligation. Proof with auto.
    destruct (result_rel_exists
       (exist (fun l : list (Vertex g) => NoDup l /\ incl l (vertices g))
          start unreachables'_obligation_1)).
    simpl in *.
    split.
      apply (half_correct r); intros...
        elimtype False...
      exists v. split... apply reachability.reachable_refl.
    destruct (other_half r).
      intros. elimtype False...
    repeat intro.
    destruct H1. destruct H1.
    destruct (reachability.reachable_flip_inv (fun j => In j x) (fun j => In_dec ved j x) H3)...
      intro.
      apply (snd (In_subtr ved (vertices g) start _ (H0 x0 H4)) H1).
    destruct H4. destruct H4. destruct H5.
    apply (H _ H4 _ H6)...
  Qed.

  (* This concludes James' approach. *)


  Program Definition reachables:
    { l: list (Vertex g) | forall w, In w l <-> reachable w }
    := subtr ved (vertices g) unreachables.

  Obligation Tactic := idtac.

  Next Obligation. Proof with auto.
    destruct unreachables.
    intros.
    split; intro.
      destruct (In_subtr _ _ _ _ H).
      simpl in H1.
      apply (i w)...
    apply subtr_In...
    apply (i w)...
  Qed.

  Definition reachable_dec (v: Vertex g): decision (reachable v) :=
    let (x, i) := unreachables in
      match In_dec ved v x with
      | left i0 => right (fun H => snd (i v) H i0)
      | right n => left (fst (i v) n)
      end.

End reachability.

Implicit Arguments reachable [[g]].
